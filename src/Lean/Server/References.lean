import Init.System.IO
import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.Utils
import Lean.Server.InfoUtils
import Lean.Server.Snapshots

namespace Lean.Server
open IO
open Std
open Lsp
open Elab
open Snapshots

/- Representing collected and deduplicated definitions and usages -/

inductive RefIdent where
  | const : Name → RefIdent
  | fvar : FVarId → RefIdent
  deriving BEq, Hashable

namespace RefIdent

def toString : RefIdent → String
  | RefIdent.const n => s!"c:{n}"
  | RefIdent.fvar id => s!"f:{id.name}"

def fromString (s : String) : Except String RefIdent := do
  let sPrefix := s.take 2
  let sName := s.drop 2
  let mk ← match sPrefix with
    | "c:" => RefIdent.const
    | "f:" => fun n => RefIdent.fvar <| FVarId.mk n
    | _ => throw "string must start with 'c:' or 'f:'"
  -- See `FromJson Name`
  let name ← match sName with
    | "[anonymous]" => Name.anonymous
    | _ => match Syntax.decodeNameLit ("`" ++ sName) with
      | some n => n
      | none => throw s!"expected a Name, got {sName}"
  mk name

end RefIdent

structure Reference where
  ident : RefIdent
  range : Lsp.Range
  isDeclaration : Bool
  deriving BEq

structure RefInfo where
  definition : Option Lsp.Range
  usages : Array Lsp.Range

namespace RefInfo

def empty : RefInfo := ⟨ none, #[] ⟩

def addRef : RefInfo → Reference → RefInfo
  | i@{ definition := none, .. }, { range, isDeclaration := true, .. } =>
    { i with definition := range }
  | i@{ usages, .. }, { range, isDeclaration := false, .. } =>
    { i with usages := usages.push range }
  | i, _ => i

def contains (self : RefInfo) (pos : Lsp.Position) : Bool := Id.run do
  if let some range := self.definition then
    if contains range pos then
      return true
  for range in self.usages do
    if contains range pos then
      return true
  false
  where
    contains (range : Lsp.Range) (pos : Lsp.Position) : Bool :=
      range.start <= pos && pos < range.end

end RefInfo

instance : ToJson RefInfo where
  toJson i :=
    let rangeToList (r : Lsp.Range) : List Nat :=
      [r.start.line, r.start.character, r.end.line, r.end.character]
    Json.mkObj [
      ("definition", toJson $ i.definition.map rangeToList),
      ("usages", toJson $ i.usages.map rangeToList)
    ]

instance : FromJson RefInfo where
  fromJson? j := do
    let listToRange (l : List Nat) : Except String Lsp.Range := match l with
      | [sLine, sChar, eLine, eChar] => pure ⟨⟨sLine, sChar⟩, ⟨eLine, eChar⟩⟩
      | _ => throw s!"Expected list of length 4, not {l.length}"
    let definition ← j.getObjValAs? (Option $ List Nat) "definition"
    let definition ← match definition with
      | none => pure none
      | some list => some <$> listToRange list
    let usages ← j.getObjValAs? (Array $ List Nat) "usages"
    let usages ← usages.mapM listToRange
    pure { definition, usages }

/-- References from a single module/file -/
def ModuleRefs := HashMap RefIdent RefInfo

instance : ToJson ModuleRefs where
  toJson m := Json.mkObj <| m.toList.map fun (ident, info) => (ident.toString, toJson info)

instance : FromJson ModuleRefs where
  fromJson? j := do
    let node ← j.getObj?
    node.foldM (init := HashMap.empty) fun m k v => do
      m.insert (← RefIdent.fromString k) (← fromJson? v)

namespace ModuleRefs

def addRef (self : ModuleRefs) (ref : Reference) : ModuleRefs :=
  let refInfo := self.findD ref.ident RefInfo.empty
  self.insert ref.ident (refInfo.addRef ref)

def findAt? (self : ModuleRefs) (pos : Lsp.Position) : Option RefIdent := Id.run do
  for (ident, info) in self.toList do
    if info.contains pos then
      return some ident
  none

end ModuleRefs

/-- References from multiple modules -/
def Bundle := HashMap Name ModuleRefs

namespace Bundle

def empty : Bundle := HashMap.empty

def addModule (self : Bundle) (module : Name) (refs : ModuleRefs) : Bundle :=
  self.insert module refs

def removeModule (self : Bundle) (module : Name) : Bundle :=
  self.erase module

def addBundle (self : Bundle) (other : Bundle) : Bundle := Id.run
  other.toList.foldl (init := self) fun l (module, refs) => l.addModule module refs

end Bundle

/-- Content of individual `.ilean` files -/
structure Ilean where
  version : Nat := 1
  module : Name
  references : ModuleRefs
  deriving FromJson, ToJson

structure IleanBundle where
  version : Nat := 1
  files : Array Ilean
  deriving FromJson, ToJson

namespace IleanBundle

def load (path : System.FilePath) : IO IleanBundle := do
  let content ← FS.readFile path
  match Json.parse content >>= fromJson? with
    | Except.ok bundle => pure bundle
    | Except.error msg => throwServerError s!"Failed to load bundle at {path}: {msg}"

def toBundle (self : IleanBundle) : Bundle :=
  self.files.foldl (init := HashMap.empty) fun mm file => mm.addModule file.module file.references

end IleanBundle

/- Collecting and deduplicating definitions and usages -/

def identOf : Info → Option (RefIdent × Bool)
  | Info.ofTermInfo ti => match ti.expr with
    | Expr.const n .. => some (RefIdent.const n, ti.isBinder)
    | Expr.fvar id .. => some (RefIdent.fvar id, ti.isBinder)
    | _ => none
  | Info.ofFieldInfo fi => some (RefIdent.const fi.projName, false)
  | _ => none

def findReferences (text : FileMap) (trees : List InfoTree) : Array Reference := Id.run do
  let mut refs := #[]
  for tree in trees do
    refs := refs.appendList <| tree.deepestNodes fun _ info _ => Id.run do
      if let some (ident, isDeclaration) := identOf info then
        if let some range := info.range? then
          return some { ident, range := range.toLspRange text, isDeclaration }
      return none
  refs

/--
The `FVarId`s of a function parameter in the function's signature and body
differ. However, they have `TermInfo` nodes with `binder := true` in the exact
same position.

This function changes every such group to use a single `FVarId` and gets rid of
duplicate definitions.
-/
def combineFvars (refs : Array Reference) : Array Reference := Id.run do
  -- Deduplicate definitions based on their exact range
  let mut posMap : HashMap Lsp.Range FVarId := HashMap.empty
  -- Map all `FVarId`s of a group to the first definition's id
  let mut idMap : HashMap FVarId FVarId := HashMap.empty
  for ref in refs do
    if let { ident := RefIdent.fvar id, range, isDeclaration := true } := ref then
      if let some baseId := posMap.find? range then
        idMap := idMap.insert id baseId
      else
        posMap := posMap.insert range id
        idMap := idMap.insert id id

  refs.foldl (init := #[]) fun refs ref => match ref with
    | { ident := RefIdent.fvar id, range, isDeclaration := true } =>
      -- Since deduplication works via definitions, we know that this keeps (at
      -- least) one definition.
      if idMap.contains id then refs.push ref else refs
    | { ident := ident@(RefIdent.fvar _), range, isDeclaration := false } =>
      refs.push { ident := applyIdMap idMap ident, range, isDeclaration := false }
    | _ => refs.push ref
  where
    applyIdMap : HashMap FVarId FVarId → RefIdent → RefIdent
      | m, RefIdent.fvar id => RefIdent.fvar <| m.findD id id
      | _, ident => ident

def findModuleRefs (text : FileMap) (trees : List InfoTree) (localVars : Bool := true)
    : ModuleRefs := Id.run do
  let mut refs := combineFvars <| findReferences text trees
  if !localVars then
    refs := refs.filter fun
      | { ident := RefIdent.fvar _, .. } => false
      | _ => true
  refs.foldl (init := HashMap.empty) fun m ref => m.addRef ref

/- Collecting and maintaining reference info from different sources -/

structure References where
  bundles : HashMap System.FilePath Bundle
  /-- Replaces the corresponding modules in `bundles` -/
  overlays : Bundle

namespace References

def empty : References := { bundles := HashMap.empty, overlays := Bundle.empty }

def addBundle (self : References) (path : System.FilePath) (bundle : IleanBundle) : References :=
  { self with bundles := self.bundles.insert path bundle.toBundle }

def removeBundle (self : References) (path : System.FilePath) : References :=
  { self with bundles := self.bundles.erase path }

def addOverlay (self : References) (module : Name) (map : ModuleRefs) : References :=
  { self with overlays := self.overlays.addModule module map }

def removeOverlay (self : References) (module : Name) : References :=
  { self with overlays := self.overlays.removeModule module }

/-- All bundles and the overlay combined into a single bundle -/
def bundle (self : References) : Bundle :=
  let base := self.bundles.toList.foldl (init := Bundle.empty) fun l (_, r) => l.addBundle r
  base.addBundle self.overlays

def findAt? (self : References) (module : Name) (pos : Lsp.Position) : Option RefIdent := Id.run do
  if let some refs := self.bundle.find? module then
    return refs.findAt? pos
  none

def referingTo (self : References) (ident : RefIdent) (srcSearchPath : SearchPath)
    (includeDefinition : Bool := true) : IO (Array Location) := do
  let mut result := #[]
  for (module, refs) in self.bundle.toList do
    if let some info := refs.find? ident then
      if let some path ← srcSearchPath.findWithExt "lean" module then
        let uri := DocumentUri.ofPath path
        if includeDefinition then
          if let some range := info.definition then
            result := result.push ⟨uri, range⟩
        for range in info.usages do
          result := result.push ⟨uri, range⟩
  result

end References

end Lean.Server
