import Init.System.IO
import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.Utils
import Lean.Server.InfoUtils
import Lean.Server.Snapshots

/- Representing collected and deduplicated definitions and usages -/

namespace Lean.Server
open Lsp

structure Reference where
  ident : RefIdent
  range : Lsp.Range
  isDeclaration : Bool
  deriving BEq

end Lean.Server

namespace Lean.Lsp.RefInfo
open Server

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

end Lean.Lsp.RefInfo

namespace Lean.Lsp.ModuleRefs
open Server

def addRef (self : ModuleRefs) (ref : Reference) : ModuleRefs :=
  let refInfo := self.findD ref.ident RefInfo.empty
  self.insert ref.ident (refInfo.addRef ref)

def findAt? (self : ModuleRefs) (pos : Lsp.Position) : Option RefIdent := Id.run do
  for (ident, info) in self.toList do
    if info.contains pos then
      return some ident
  none

end Lean.Lsp.ModuleRefs

namespace Lean.Server
open IO
open Std
open Lsp
open Elab

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
  overlays : HashMap Name (Nat × ModuleRefs)

namespace References

def empty : References := { bundles := HashMap.empty, overlays := HashMap.empty }

def addBundle (self : References) (path : System.FilePath) (bundle : IleanBundle) : References :=
  { self with bundles := self.bundles.insert path bundle.toBundle }

def removeBundle (self : References) (path : System.FilePath) : References :=
  { self with bundles := self.bundles.erase path }

def addOverlay (self : References) (module : Name) (version : Nat) (refs : ModuleRefs)
    : References := Id.run do
  if let some (oldVersion, _) := self.overlays.find? module then
    if version <= oldVersion then
      return self -- Trying to add an older version
  return { self with overlays := self.overlays.insert module (version, refs) }

def removeOverlay (self : References) (module : Name) : References :=
  { self with overlays := self.overlays.erase module }

def overlayBundle (self : References) : Bundle :=
  self.overlays.toList.foldl (init := Bundle.empty) fun bundle (name, _, refs) => bundle.addModule name refs

/-- All bundles and the overlay combined into a single bundle -/
def bundle (self : References) : Bundle :=
  let base := self.bundles.toList.foldl (init := Bundle.empty) fun l (_, r) => l.addBundle r
  base.addBundle self.overlayBundle

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
        -- Resolve symlinks (such as `src` in the build dir) so that files are
        -- opened in the right folder
        let uri := DocumentUri.ofPath <| ← IO.FS.realPath path
        if includeDefinition then
          if let some range := info.definition then
            result := result.push ⟨uri, range⟩
        for range in info.usages do
          result := result.push ⟨uri, range⟩
  result

end References

end Lean.Server
