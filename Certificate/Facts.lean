import Lean
import Elements

/-!
# The certificate

Run with `lake env lean Certificate/Facts.lean` (after `lake build`). For every
proposition it records, straight from Lean's own proof terms:

* whether the proof is finished, or still has a `sorry` in it;
* which earlier propositions it cites directly;
* which Common Notions it cites by name;
* exactly which postulates, definitions and tacit rules it rests on
  (via `#print axioms`, i.e. `Lean.collectAxioms`);
* which shared steps it calls on (`Prop30.meet`, `Prop34.bisect`, `Rectangle.eq_rect`),
  and the propositions each one brings in.

The results go to `facts.json`, which `scripts/render.py` turns into
`CERTIFICATE.md`, `GRAPH.md` and the pages under `book/`.
-/

open Lean

namespace Certificate

/-- Lean's own logical foundations: not Euclid's assumptions, but listed. -/
def leanFoundations : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The Common Notions are theorems in Lean, so `collectAxioms` can't see them;
we notice them when a proof cites them by name. -/
def commonNotions : List (Name × String) :=
  [(``Elements.CommonNotion1, "C.N. 1"), (``Elements.CommonNotion2, "C.N. 2"),
   (``Elements.CommonNotion3, "C.N. 3"), (``Elements.CommonNotion4, "C.N. 4"),
   (``Elements.CommonNotion4.angle, "C.N. 4"), (``Elements.CommonNotion4.triangle, "C.N. 4"),
   (``Elements.CommonNotion5, "C.N. 5")]

/-- The books, their Lean namespaces and how many propositions each has. A proposition
of a later book may cite one of an earlier book, and the walk below records it by its
own book: `"I.47"` among the citations of II.9. -/
def books : List (String × Name × Nat) :=
  [("I", `Elements.BookI, 48), ("II", `Elements.BookII, 14), ("III", `Elements.BookIII, 37)]

/-- Is `n` declared in one of this project's own modules (or in this file)? -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx => (`Elements).isPrefixOf (env.header.moduleNames[idx.toNat]!)

/-- A porism is part of its proposition: `Elements.BookIII.Prop1.porism` belongs to
`Elements.BookIII.Prop1`, as Heath's "[III. 1, Por.]" cites III. 1. -/
def porismOf (props : NameSet) : Name → Option Name
  | .str p "porism" => if props.contains p then some p else none
  | _ => none

/-- Walk the proof of `root`, passing through helper lemmas and auxiliary
declarations, stopping at other propositions and at their porisms (a porism counts
as citing its proposition). Returns the propositions cited, the Common Notions
cited, the axioms used directly (not through another proposition), and whether a
`sorry` appears along the way. -/
partial def directDeps (env : Environment) (props : NameSet) (root : Name) :
    NameSet × NameSet × NameSet × Bool := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut cites : NameSet := {}
  let mut notions : NameSet := {}
  let mut direct : NameSet := {}
  let mut hasSorry := false
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for d in v.getUsedConstants do
      if d == ``sorryAx then hasSorry := true
      else if props.contains d && d != root then cites := cites.insert d
      else if let some p := porismOf props d then
        if p != root then cites := cites.insert p
      else if (env.find? d).any (·.isAxiom) then direct := direct.insert d
      else if (commonNotions.map (·.1)).contains d then notions := notions.insert d
      else if isLocal env d && !seen.contains d then todo := todo.push d
  return (cites, notions, direct, hasSorry)

/-- The shared steps the proof of `root` calls on itself: this project's own lemmas
and definitions that live outside `root`'s namespace, such as a lemma of Book Zero,
`Prop30.meet`, the corollary `Prop34.bisect` or `Rectangle.eq_rect`. The walk passes
through `root`'s own helpers (`Prop7.figure`) and Lean's auxiliary declarations, and
stops at each shared step, as at propositions, axioms and Common Notions: what a
shared step calls on in turn is its own business, counted by `directDeps` from it. -/
def sharedSteps (env : Environment) (props : NameSet) (root : Name) : NameSet :=
  Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut steps : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let some v := ci.value? (allowOpaque := true) | continue
    for d in v.getUsedConstants do
      if props.contains d || (porismOf props d).isSome then continue
      if (env.find? d).any (·.isAxiom) then continue
      if (commonNotions.map (·.1)).contains d || !isLocal env d then continue
      if root.isPrefixOf d || d.isInternal then todo := todo.push d
      else steps := steps.insert d
  return steps

/-- Where `n` is declared, as a path from the repository root and the line of its
name: `("Elements/BookII/Rectangles.lean", 98)` for `Rectangle.eq_rect`. -/
def declaredAt {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]
    (n : Name) : m (String × Nat) := do
  let env ← getEnv
  let file := match env.getModuleIdxFor? n with
    | some idx => (env.header.moduleNames[idx.toNat]!.toString.replace "." "/") ++ ".lean"
    | none => ""
  let line := match ← findDeclarationRanges? n with
    | some r => r.selectionRange.pos.line
    | none => 0
  return (file, line)

/-- `Elements.BookI.Prop12` ↦ `"I.12"`, `Elements.BookII.Prop4` ↦ `"II.4"`,
`Elements.BookIII.Prop31` ↦ `"III.31"`. -/
def refOf (n : Name) : String :=
  let book := match n.getPrefix with
    | Name.str _ s => (s.drop 4).toString   -- "BookI" ↦ "I", "BookIII" ↦ "III"
    | _ => "?"
  let num := match n with
    | Name.str _ s => (s.drop 4).toString   -- "Prop12" ↦ "12"
    | _ => "?"
  s!"{book}.{num}"

def nameStr (n : Name) : String :=
  (n.toString.replace "Elements." "")

end Certificate

open Certificate in
run_cmd do
  let env ← getEnv
  let mut props : Array Name := #[]
  for (_, ns, count) in books do
    for i in [1:count+1] do
      let n := ns ++ Name.mkSimple s!"Prop{i}"
      if env.contains n then props := props.push n
  let propSet := NameSet.ofList props.toList
  let mut entries : Array Json := #[]
  for p in props do
    let axs ← collectAxioms p
    let (cites, notions, direct, sorryHere) := directDeps env propSet p
    let restsOnSorry := axs.contains ``sorryAx
    /- A proposition is not finished until its porism is. -/
    let por := Name.str p "porism"
    let (porSorry, porPending) ← if env.contains por then do
        let (_, _, _, s) := directDeps env propSet por
        pure (s, (← collectAxioms por).contains ``sorryAx)
      else pure (false, false)
    let status := if sorryHere || porSorry then "sketched"
      else if restsOnSorry || porPending then "proved-pending" else "proved"
    let euclid := axs.filter fun a => !leanFoundations.contains a && a != ``sorryAx
    let foundations := axs.filter fun a => leanFoundations.contains a
    let notionRefs := (commonNotions.filter fun (n, _) => notions.contains n).map (·.2)
    let doc ← findDocString? env p
    /- The shared steps that bring in at least one proposition, each with the
    propositions it brings in, in the order of the books. -/
    let mut shared : Array Json := #[]
    for s in (sharedSteps env propSet p).toList.toArray.qsort (nameStr · < nameStr ·) do
      let (reached, _, _, _) := directDeps env propSet s
      if reached.isEmpty then continue
      let (file, line) ← declaredAt s
      shared := shared.push <| Json.mkObj [
        ("name", Json.str (nameStr s)),
        ("brings_in", Json.arr ((props.filter reached.contains).map (Json.str ∘ refOf))),
        ("file", Json.str file),
        ("line", toJson line)]
    entries := entries.push <| Json.mkObj [
      ("ref", Json.str (refOf p)),
      ("name", Json.str (nameStr p)),
      ("status", Json.str status),
      ("cites", Json.arr ((cites.toList.map refOf).toArray.qsort (· < ·) |>.map Json.str)),
      ("common_notions", Json.arr (notionRefs.eraseDups.toArray.map Json.str)),
      ("axioms", Json.arr ((euclid.map nameStr).qsort (· < ·) |>.map Json.str)),
      ("direct_axioms", Json.arr ((direct.toList.map nameStr).toArray.qsort (· < ·) |>.map Json.str)),
      ("lean_foundations", Json.arr (foundations.map (Json.str ∘ nameStr))),
      ("shared_steps", Json.arr shared),
      ("enunciation", Json.str (doc.getD ""))]
  let out := Json.mkObj [("lean_version", Json.str Lean.versionString),
    ("propositions", Json.arr entries)]
  IO.FS.writeFile "facts.json" (out.pretty ++ "\n")
  logInfo m!"certificate: {props.size} propositions written to facts.json"
