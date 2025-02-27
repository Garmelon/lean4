/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment

import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

import Lean.Util.Paths
import Lean.LoadDynlib

import Lean.Server.Utils
import Lean.Server.Snapshots
import Lean.Server.AsyncList
import Lean.Server.References

import Lean.Server.FileWorker.Utils
import Lean.Server.FileWorker.RequestHandling
import Lean.Server.FileWorker.WidgetRequests

import Lean.Server.Rpc.Basic
import Lean.Widget.InteractiveDiagnostic

/-!
For general server architecture, see `README.md`. For details of IPC communication, see `Watchdog.lean`.
This module implements per-file worker processes.

File processing and requests+notifications against a file should be concurrent for two reasons:
- By the LSP standard, requests should be cancellable.
- Since Lean allows arbitrary user code to be executed during elaboration via the tactic framework,
  elaboration can be extremely slow and even not halt in some cases. Users should be able to
  work with the file while this is happening, e.g. make new changes to the file or send requests.

To achieve these goals, elaboration is executed in a chain of tasks, where each task corresponds to
the elaboration of one command. When the elaboration of one command is done, the next task is spawned.
On didChange notifications, we search for the task in which the change occured. If we stumble across
a task that has not yet finished before finding the task we're looking for, we terminate it
and start the elaboration there, otherwise we start the elaboration at the task where the change occured.

Requests iterate over tasks until they find the command that they need to answer the request.
In order to not block the main thread, this is done in a request task.
If a task that the request task waits for is terminated, a change occured somewhere before the
command that the request is looking for and the request sends a "content changed" error.
-/

namespace Lean.Server.FileWorker

open Lsp
open IO
open Snapshots
open Std (RBMap RBMap.empty)
open JsonRpc

structure WorkerContext where
  hIn           : FS.Stream
  hOut          : FS.Stream
  hLog          : FS.Stream
  srcSearchPath : SearchPath
  initParams    : InitializeParams

/- Asynchronous snapshot elaboration. -/
section Elab
  structure AsyncElabState where
    headerSnap : Snapshot
    snaps : Array Snapshot

  private def AsyncElabState.lastSnap (s : AsyncElabState) : Snapshot :=
    s.snaps.getD (s.snaps.size - 1) s.headerSnap

  abbrev AsyncElabM := StateT AsyncElabState <| EIO ElabTaskError

  -- Placed here instead of Lean.Server.Utils because of an import loop
  private def publishReferences (m : DocumentMeta) (s : AsyncElabState) (hOut : FS.Stream) : IO Unit := do
    let trees := (s.snaps.insertAt 0 s.headerSnap).map fun snap => snap.infoTree
    let references := findModuleRefs m.text trees (localVars := true)
    hOut.writeLspNotification {
      method := "$/lean/ileanInfo"
      param := { version := m.version, references : LeanIleanInfoParams }
    }

  /-- Elaborates the next command after `parentSnap` and emits diagnostics into `hOut`. -/
  private def nextCmdSnap (ctx : WorkerContext) (m : DocumentMeta) (cancelTk : CancelToken)
      : AsyncElabM (Option Snapshot) := do
    cancelTk.check
    let s ← get
    let lastSnap := s.lastSnap
    if lastSnap.isAtEnd then
      publishDiagnostics m lastSnap.diagnostics.toArray ctx.hOut
      publishProgressDone m ctx.hOut
      publishReferences m s ctx.hOut
      return none
    publishProgressAtPos m lastSnap.endPos ctx.hOut
    let snap ← compileNextCmd m.text lastSnap
    set { s with snaps := s.snaps.push snap }
    -- TODO(MH): check for interrupt with increased precision
    cancelTk.check
    /- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
      while prefering newer versions over old ones. The former is necessary because we do
      not explicitly clear older diagnostics, while the latter is necessary because we do
      not guarantee that diagnostics are emitted in order. Specifically, it may happen that
      we interrupted this elaboration task right at this point and a newer elaboration task
      emits diagnostics, after which we emit old diagnostics because we did not yet detect
      the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
      because we cannot guarantee that no further diagnostics are emitted after clearing
      them. -/
    -- NOTE(WN): this is *not* redundent even if there are no new diagnostics in this snapshot
    -- because empty diagnostics clear existing error/information squiggles. Therefore we always
    -- want to publish in case there was previously a message at this position.
    publishDiagnostics m snap.diagnostics.toArray ctx.hOut
    return some snap

  /-- Elaborates all commands after the last snap (using `headerSnap` if `snaps`
  is empty), emitting the diagnostics into `hOut`. -/
  def unfoldCmdSnaps (m : DocumentMeta) (headerSnap : Snapshot) (snaps : Array Snapshot) (cancelTk : CancelToken)
      : ReaderT WorkerContext IO (AsyncList ElabTaskError Snapshot) := do
    if snaps.isEmpty && headerSnap.msgLog.hasErrors then
      -- Treat header processing errors as fatal so users aren't swamped with
      -- followup errors
      let hOut := (←read).hOut
      publishProgressAtPos m headerSnap.beginPos hOut (kind := LeanFileProgressKind.fatalError)
      AsyncList.nil
    else
      let ctx ← read
      AsyncList.unfoldAsync (nextCmdSnap ctx m cancelTk) { headerSnap, snaps }
end Elab

-- Pending requests are tracked so they can be cancelled
abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) compare

structure WorkerState where
  doc             : EditableDocument
  pendingRequests : PendingRequestMap
  /-- A map of RPC session IDs. We allow asynchronous elab tasks and request handlers
  to modify sessions. A single `Ref` ensures atomic transactions. -/
  rpcSessions     : Std.RBMap UInt64 (IO.Ref RpcSession) compare

abbrev WorkerM := ReaderT WorkerContext <| StateRefT WorkerState IO

/- Worker initialization sequence. -/
section Initialization
  /-- Use `lake print-paths` to compile dependencies on the fly and add them to `LEAN_PATH`.
  Compilation progress is reported to `hOut` via LSP notifications. Return the search path for
  source files. -/
  partial def lakeSetupSearchPath (lakePath : System.FilePath) (m : DocumentMeta) (imports : Array Import) (hOut : FS.Stream) : IO SearchPath := do
    let args := #["print-paths"] ++ imports.map (toString ·.module)
    let cmdStr := " ".intercalate (toString lakePath :: args.toList)
    let lakeProc ← Process.spawn {
      stdin  := Process.Stdio.null
      stdout := Process.Stdio.piped
      stderr := Process.Stdio.piped
      cmd    := lakePath.toString
      args
    }
    -- progress notification: report latest stderr line
    let rec processStderr (acc : String) : IO String := do
      let line ← lakeProc.stderr.getLine
      if line == "" then
        return acc
      else
        publishDiagnostics m #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.information, message := line }] hOut
        processStderr (acc ++ line)
    let stderr ← IO.asTask (processStderr "") Task.Priority.dedicated
    let stdout := String.trim (← lakeProc.stdout.readToEnd)
    let stderr ← IO.ofExcept stderr.get
    match (← lakeProc.wait) with
    | 0 =>
      -- ignore any output up to the last line
      -- TODO: leanpkg should instead redirect nested stdout output to stderr
      let stdout := stdout.split (· == '\n') |>.getLast!
      let Except.ok (paths : LeanPaths) ← pure (Json.parse stdout >>= fromJson?)
        | throwServerError s!"invalid output from `{cmdStr}`:\n{stdout}\nstderr:\n{stderr}"
      initSearchPath (← getBuildDir) paths.oleanPath
      paths.loadDynlibPaths.forM loadDynlib
      paths.srcPath.mapM realPathNormalized
    | 2 => pure []  -- no lakefile.lean
    | _ => throwServerError s!"`{cmdStr}` failed:\n{stdout}\nstderr:\n{stderr}"

  def compileHeader (m : DocumentMeta) (hOut : FS.Stream) (opts : Options) : IO (Snapshot × SearchPath) := do
    let inputCtx := Parser.mkInputContext m.text.source "<input>"
    let (headerStx, headerParserState, msgLog) ← Parser.parseHeader inputCtx
    let mut srcSearchPath ← initSrcSearchPath (← getBuildDir)
    let lakePath ← match (← IO.getEnv "LAKE") with
      | some path => System.FilePath.mk path
      | none =>
        let lakePath :=
          -- backward compatibility, kill when `leanpkg` is removed
          if (← System.FilePath.pathExists "leanpkg.toml") && !(← System.FilePath.pathExists "lakefile.lean") then "leanpkg"
          else "lake"
        let lakePath ← match (← IO.getEnv "LEAN_SYSROOT") with
          | some path => pure <| System.FilePath.mk path / "bin" / lakePath
          | _         => pure <| (← appDir) / lakePath
        lakePath.withExtension System.FilePath.exeExtension
    let (headerEnv, msgLog) ← try
      if let some path := m.uri.toPath? then
        -- NOTE: we assume for now that `lakefile.lean` does not have any non-stdlib deps
        -- NOTE: lake does not exist in stage 0 (yet?)
        if path.fileName != "lakefile.lean" && (← System.FilePath.pathExists lakePath) then
          let pkgSearchPath ← lakeSetupSearchPath lakePath m (Lean.Elab.headerToImports headerStx).toArray hOut
          srcSearchPath := pkgSearchPath ++ srcSearchPath
      Elab.processHeader headerStx opts msgLog inputCtx
    catch e =>  -- should be from `lake print-paths`
      let msgs := MessageLog.empty.add { fileName := "<ignored>", pos := ⟨0, 0⟩, data := e.toString }
      pure (← mkEmptyEnvironment, msgs)
    let mut headerEnv := headerEnv
    try
      if let some path := m.uri.toPath? then
        headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
    catch _ => ()
    let cmdState := Elab.Command.mkState headerEnv msgLog opts
    let cmdState := { cmdState with infoState := {
      enabled := true
      trees := #[Elab.InfoTree.context ({
        env := headerEnv
        fileMap := m.text
      }) (Elab.InfoTree.node
          (Elab.Info.ofCommandInfo { elaborator := `header, stx := headerStx })
          (headerStx[1].getArgs.toList.map (fun importStx =>
            Elab.InfoTree.node (Elab.Info.ofCommandInfo {
              elaborator := `import
              stx := importStx
            }) #[].toPersistentArray
          )).toPersistentArray
      )].toPersistentArray
    }}
    let headerSnap := {
      beginPos := 0
      stx := headerStx
      mpState := headerParserState
      cmdState := cmdState
      interactiveDiags := ← cmdState.messages.msgs.mapM (Widget.msgToInteractiveDiagnostic m.text)
    }
    publishDiagnostics m headerSnap.diagnostics.toArray hOut
    return (headerSnap, srcSearchPath)

  def initializeWorker (meta : DocumentMeta) (i o e : FS.Stream) (initParams : InitializeParams) (opts : Options)
      : IO (WorkerContext × WorkerState) := do
    let (headerSnap, srcSearchPath) ← compileHeader meta o opts
    let cancelTk ← CancelToken.new
    let ctx :=
      { hIn                := i
        hOut               := o
        hLog               := e
        srcSearchPath      := srcSearchPath
        initParams         := initParams
      }
    let cmdSnaps ← unfoldCmdSnaps meta headerSnap #[] cancelTk ctx
    let doc : EditableDocument := ⟨meta, headerSnap, cmdSnaps, cancelTk⟩
    return (ctx,
    { doc             := doc
      pendingRequests := RBMap.empty
      rpcSessions     := Std.RBMap.empty
    })
end Initialization

section Updates
  def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : WorkerM Unit := do
    modify fun st => { st with pendingRequests := map st.pendingRequests }

  /-- Given the new document, updates editable doc state. -/
  def updateDocument (newMeta : DocumentMeta) : WorkerM Unit := do
    -- The watchdog only restarts the file worker when the syntax tree of the header changes.
    -- If e.g. a newline is deleted, it will not restart this file worker, but we still
    -- need to reparse the header so that the offsets are correct.
    let ctx ← read
    let oldDoc := (←get).doc
    let newHeaderSnap ← reparseHeader newMeta.text.source oldDoc.headerSnap
    if newHeaderSnap.stx != oldDoc.headerSnap.stx then
      throwServerError "Internal server error: header changed but worker wasn't restarted."
    let ⟨cmdSnaps, e?⟩ ← oldDoc.cmdSnaps.updateFinishedPrefix
    match e? with
    -- This case should not be possible. only the main task aborts tasks and ensures that aborted tasks
    -- do not show up in `snapshots` of an EditableDocument.
    | some ElabTaskError.aborted =>
      throwServerError "Internal server error: elab task was aborted while still in use."
    | some (ElabTaskError.ioError ioError) => throw ioError
    | _ => -- No error or EOF
      oldDoc.cancelTk.set
      let changePos := oldDoc.meta.text.source.firstDiffPos newMeta.text.source
      -- NOTE(WN): we invalidate eagerly as `endPos` consumes input greedily. To re-elaborate only
      -- when really necessary, we could do a whitespace-aware `Syntax` comparison instead.
      let mut validSnaps := cmdSnaps.finishedPrefix.takeWhile (fun s => s.endPos < changePos)
      if validSnaps.length = 0 then
        let cancelTk ← CancelToken.new
        let newCmdSnaps ← unfoldCmdSnaps newMeta newHeaderSnap #[] cancelTk ctx
        modify fun st => { st with doc := ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩ }
      else
        /- When at least one valid non-header snap exists, it may happen that a change does not fall
           within the syntactic range of that last snap but still modifies it by appending tokens.
           We check for this here. We do not currently handle crazy grammars in which an appended
           token can merge two or more previous commands into one. To do so would require reparsing
           the entire file. -/
        let mut lastSnap := validSnaps.getLast!
        let preLastSnap := if validSnaps.length ≥ 2
          then validSnaps.get! (validSnaps.length - 2)
          else newHeaderSnap
        let newLastStx ← parseNextCmd newMeta.text.source preLastSnap
        if newLastStx != lastSnap.stx then
          validSnaps ← validSnaps.dropLast
        let cancelTk ← CancelToken.new
        let newSnaps ← unfoldCmdSnaps newMeta newHeaderSnap validSnaps.toArray cancelTk ctx
        let newCmdSnaps := AsyncList.ofList validSnaps ++ newSnaps
        modify fun st => { st with doc := ⟨newMeta, newHeaderSnap, newCmdSnaps, cancelTk⟩ }
end Updates

/- Notifications are handled in the main thread. They may change global worker state
such as the current file contents. -/
section NotificationHandling
  def handleDidChange (p : DidChangeTextDocumentParams) : WorkerM Unit := do
    let docId := p.textDocument
    let changes := p.contentChanges
    let oldDoc := (←get).doc
    let some newVersion ← pure docId.version?
      | throwServerError "Expected version number"
    if newVersion ≤ oldDoc.meta.version then
      -- TODO(WN): This happens on restart sometimes.
      IO.eprintln s!"Got outdated version number: {newVersion} ≤ {oldDoc.meta.version}"
    else if ¬ changes.isEmpty then
      let newDocText := foldDocumentChanges changes oldDoc.meta.text
      updateDocument ⟨docId.uri, newVersion, newDocText⟩

  def handleCancelRequest (p : CancelParams) : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)

def handleRpcRelease (p : Lsp.RpcReleaseParams) : WorkerM Unit := do
  let st ← get
  -- NOTE(WN): when the worker restarts e.g. due to changed imports, we may receive `rpc/release`
  -- for the previous RPC session. This is fine, just ignore.
  if let some seshRef := st.rpcSessions.find? p.sessionId then
    let monoMsNow ← IO.monoMsNow
    seshRef.modify fun sesh => Id.run do
      let mut sesh := sesh
      for ref in p.refs do
        sesh := sesh.release ref |>.snd
      sesh.keptAlive monoMsNow

def handleRpcKeepAlive (p : Lsp.RpcKeepAliveParams) : WorkerM Unit := do
  let st ← get
  match st.rpcSessions.find? p.sessionId with
  | none => return
  | some seshRef =>
    seshRef.modify (·.keptAlive (← IO.monoMsNow))

end NotificationHandling

/-! Requests here are handled synchronously rather than in the asynchronous `RequestM`. -/
section RequestHandling

def handleRpcConnect (p : RpcConnectParams) : WorkerM RpcConnected := do
  let (newId, newSesh) ← RpcSession.new
  let newSeshRef ← IO.mkRef newSesh
  modify fun st => { st with rpcSessions := st.rpcSessions.insert newId newSeshRef }
  return { sessionId := newId }

end RequestHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : WorkerM paramType :=
    match fromJson? params with
    | Except.ok parsed => pure parsed
    | Except.error inner => throwServerError s!"Got param with wrong structure: {params.compress}\n{inner}"

  def handleNotification (method : String) (params : Json) : WorkerM Unit := do
    let handle := fun paramType [FromJson paramType] (handler : paramType → WorkerM Unit) =>
      parseParams paramType params >>= handler
    match method with
    | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | "$/lean/rpc/release"     => handle RpcReleaseParams handleRpcRelease
    | "$/lean/rpc/keepAlive"   => handle RpcKeepAliveParams handleRpcKeepAlive
    | _                        => throwServerError s!"Got unsupported notification method: {method}"

  def queueRequest (id : RequestID) (requestTask : Task (Except IO.Error Unit))
      : WorkerM Unit := do
    updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

  def handleRequest (id : RequestID) (method : String) (params : Json)
      : WorkerM Unit := do
    let ctx ← read
    let st ← get

    if method == "$/lean/rpc/connect" then
      try
        let ps ← parseParams RpcConnectParams params
        let resp ← handleRpcConnect ps
        ctx.hOut.writeLspResponse ⟨id, resp⟩
      catch e =>
        ctx.hOut.writeLspResponseError
          { id
            code := ErrorCode.internalError
            message := toString e }
      return

    let rc : RequestContext :=
      { rpcSessions := st.rpcSessions
        srcSearchPath := ctx.srcSearchPath
        doc := st.doc
        hLog := ctx.hLog
        initParams := ctx.initParams }
    let t? ← EIO.toIO' <| handleLspRequest method params rc
    let t₁ ← match t? with
      | Except.error e =>
        IO.asTask do
          ctx.hOut.writeLspResponseError <| e.toLspResponseError id
      | Except.ok t => (IO.mapTask · t) fun
        | Except.ok resp =>
          ctx.hOut.writeLspResponse ⟨id, resp⟩
        | Except.error e =>
          ctx.hOut.writeLspResponseError <| e.toLspResponseError id
    queueRequest id t₁
end MessageHandling

section MainLoop
  partial def mainLoop : WorkerM Unit := do
    let ctx ← read
    let mut st ← get
    let msg ← ctx.hIn.readLspMessage
    let filterFinishedTasks (acc : PendingRequestMap) (id : RequestID) (task : Task (Except IO.Error Unit))
        : IO PendingRequestMap := do
      if (←hasFinished task) then
        /- Handler tasks are constructed so that the only possible errors here
        are failures of writing a response into the stream. -/
        if let Except.error e := task.get then
          throwServerError s!"Failed responding to request {id}: {e}"
        acc.erase id
      else acc
    let pendingRequests ← st.pendingRequests.foldM (fun acc id task => filterFinishedTasks acc id task) st.pendingRequests
    st := { st with pendingRequests }

    -- Opportunistically (i.e. when we wake up on messages) check if any RPC session has expired.
    for (id, seshRef) in st.rpcSessions do
      let sesh ← seshRef.get
      if (← sesh.hasExpired) then
        st := { st with rpcSessions := st.rpcSessions.erase id }

    set st
    match msg with
    | Message.request id method (some params) =>
      handleRequest id method (toJson params)
      mainLoop
    | Message.notification "exit" none =>
      let doc ← (←get).doc
      doc.cancelTk.set
      return ()
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      mainLoop
    | _ => throwServerError "Got invalid JSON-RPC message"
end MainLoop

def initAndRunWorker (i o e : FS.Stream) (opts : Options) : IO UInt32 := do
  let i ← maybeTee "fwIn.txt" false i
  let o ← maybeTee "fwOut.txt" true o
  let initParams ← i.readLspRequestAs "initialize" InitializeParams
  let ⟨_, param⟩ ← i.readLspNotificationAs "textDocument/didOpen" DidOpenTextDocumentParams
  let doc := param.textDocument
  /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
    "\n", which should be enough to handle both LF and CRLF correctly.
    This is because LSP always refers to characters by (line, column),
    so if we get the line number correct it shouldn't matter that there
    is a CR there. -/
  let meta : DocumentMeta := ⟨doc.uri, doc.version, doc.text.toFileMap⟩
  let e ← e.withPrefix s!"[{param.textDocument.uri}] "
  let _ ← IO.setStderr e
  try
    let (ctx, st) ← initializeWorker meta i o e initParams.param opts
    let _ ← StateRefT'.run (s := st) <| ReaderT.run (r := ctx) mainLoop
    return (0 : UInt32)
  catch e =>
    IO.eprintln e
    publishDiagnostics meta #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.error, message := e.toString }] o
    return (1 : UInt32)

@[export lean_server_worker_main]
def workerMain (opts : Options) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    let seed ← (UInt64.toNat ∘ ByteArray.toUInt64LE!) <$> IO.getRandomBytes 8
    IO.setRandSeed seed
    let exitCode ← initAndRunWorker i o e opts
    -- HACK: all `Task`s are currently "foreground", i.e. we join on them on main thread exit, but we definitely don't
    -- want to do that in the case of the worker processes, which can produce non-terminating tasks evaluating user code
    o.flush
    e.flush
    IO.Process.exit exitCode.toUInt8
  catch err =>
    e.putStrLn s!"worker initialization error: {err}"
    return (1 : UInt32)

end Lean.Server.FileWorker
