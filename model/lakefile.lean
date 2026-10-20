import Lake

open System Lake DSL

package model where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.35.0"
require stoicheia from ".."

def leanExtension (file : FilePath) : Bool :=
  #["lean", "leaN", "leAn", "leAN", "lEan", "lEaN", "lEAn", "lEAN",
    "Lean", "LeaN", "LeAn", "LeAN", "LEan", "LEaN", "LEAn", "LEAN"].contains
    (file.extension.getD "")

def entryKind (file : FilePath) : IO String := do
  match (← file.symlinkMetadata).type with
  | .dir => return "directory"
  | .file => return "file"
  | .symlink => return "symlink"
  | .other => return "other"

def auditedPath (root file : FilePath) : String :=
  "/".intercalate (file.components.drop root.components.length)

def sourceListing (pkg : Package) : IO (Array String) := do
  let some root := pkg.dir.parent
    | throw <| IO.userError s!"no repository above {pkg.dir}"
  let mut entries := #[]
  for file in ← (pkg.dir / "Model").walkDir do
    entries := entries.push s!"{← entryKind file}\t{auditedPath root file}"
  for file in ← (root / "Elements" / "Foundations").walkDir do
    entries := entries.push s!"{← entryKind file}\t{auditedPath root file}"
  for entry in ← pkg.dir.readDir do
    entries := entries.push s!"{← entryKind entry.path}\t{auditedPath root entry.path}"
  return entries.qsort (· < ·)

target sourceListings pkg : Unit := do
  Job.async do
    let entries ← sourceListing pkg
    let hash := entries.foldl (fun hash entry => Hash.mix hash (Hash.ofString entry)) Hash.nil
    setTrace <| BuildTrace.ofHash hash "audited source listings"

input_file axiomsLock where
  path := "../Certificate/axioms.lock"
  text := true

input_file lockHash where
  path := "lock.sha256"
  text := true

input_file generatedLaws where
  path := "Model/Laws.lean"
  text := true

input_file generatedChecks where
  path := "Check/Laws.lean"
  text := true

input_file generatedAssembly where
  path := "Model/Assembly.lean"
  text := true

input_dir planeProofs where
  path := "Model/Euclidean"
  text := true
  filter := fun (file : FilePath) => file.extension == some "lean"

input_file modelRoot where
  path := "Model.lean"
  text := true

input_dir modelSources where
  path := "Model"
  text := true
  filter := leanExtension

input_dir pureSources where
  path := "../Elements/Foundations"
  text := true
  filter := leanExtension

@[default_target]
lean_lib Model

@[default_target]
lean_lib Check where
  needs := #[`@/Model:leanArts, axiomsLock, lockHash, generatedLaws, generatedChecks,
    generatedAssembly, planeProofs, modelRoot, modelSources, pureSources, sourceListings]
