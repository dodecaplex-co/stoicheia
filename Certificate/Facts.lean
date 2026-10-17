import Lean
import Elements

/-!
# The certificate

Run with `lake env lean Certificate/Facts.lean` (after `lake build`). It writes
`facts.json`, whose fields `Certificate/FIELDS.md` sets out. There is an entry for
every proposition, for every porism (`Prop1.porism`, "III.1 Por."), and for every
companion theorem proved beside a proposition (none yet). For each it records, straight
from Lean's own proof terms:

* its statement, printed with every name written out and no notation;
* whether the proof is finished, or still has a `sorry` in it;
* which other entries it cites directly;
* exactly which postulates, definitions and tacit rules it rests on
  (via `#print axioms`, i.e. `Lean.collectAxioms`), and which of them it uses itself;
* which Common Notions it rests on, found by a walk that goes wherever
  `collectAxioms` goes, so that, like the postulates, they include those of the
  entries it cites;
* which shared steps it calls on (`Prop30.meet`, `Prop34.bisect`, `Rectangle.eq_rect`),
  and the entries each one brings in.

Every walk reads a declaration in the same way, through `mentions`: its type, its value
and an inductive type's constructors, as `collectAxioms` reads them. And the run checks
itself against Lean: for every entry, the axioms `collectAxioms` finds must be exactly
those the entry uses itself, together with those of the entries it cites and of the
Common Notions it calls on. If they ever differ, the run fails.

For the whole environment it also records the module that declares every axiom of
this project, and of every axiom an entry rests on; the `opaque` words; the exact
statement of every axiom; and the vocabulary those statements are written in. So
`scripts/check_fidelity.py` can check from Lean itself, not from the source text, that
every axiom lives in `Elements/Foundations/`, that the primitive words stay opaque, and
that no axiom has changed what it says.

The results go to `facts.json`, which `scripts/render.py` turns into
`CERTIFICATE.md`, `GRAPH.md` and the pages under `book/`.
-/

open Lean

namespace Certificate

/-- Lean's own logical foundations: not Euclid's assumptions, but listed. -/
def leanFoundations : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The Common Notions are theorems in Lean, so `collectAxioms` can't see them;
`allNotions` finds them by a walk of its own. -/
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

/-- The theorems proved beside a proposition, each with its reference: a more general
form of its statement, say, as `(``Elements.BookI.Prop40.general, "I.40 general")`. Each
is an entry of its own, attached to its proposition, whose namespace it lives in. There
are none yet; stage 2 of brief 0005 adds them. -/
def companions : List (Name × String) := []

/-- Is `n` declared in one of this project's own modules (or in this file)? -/
def isLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx => (`Elements).isPrefixOf (env.header.moduleNames[idx.toNat]!)

/-- Everything the declaration `ci` mentions: the constants of its type, of its value (a
theorem's proof and an opaque's hidden value included), and an inductive type's
constructors. These are the places `collectAxioms` looks. Every walk below reads a
declaration through this one function, so what one of them sees, the others see too. -/
def mentions (ci : ConstantInfo) : Array Name := Id.run do
  let mut used := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
  if let .inductInfo v := ci then used := used ++ v.ctors.toArray
  return used

/-- What `directDeps` finds beneath a declaration. -/
structure Deps where
  /-- The entries it cites: propositions, porisms and companions. -/
  cites : NameSet := {}
  /-- The axioms it uses itself, not through an entry it cites or a Common Notion. -/
  direct : NameSet := {}
  /-- The Common Notions it calls on itself. -/
  notions : NameSet := {}
  /-- Whether a `sorry` appears along the way. -/
  hasSorry : Bool := false

/-- Walk the declaration `root` through `mentions`, passing through helper lemmas,
definitions and Lean's auxiliary declarations, and stopping at the other entries, at the
axioms and at the Common Notions. A use of a porism is recorded as the porism itself,
"III.1 Por.", not as its proposition.

At an axiom of this project the walk goes on through its statement, as `collectAxioms`
does: an axiom stated in words that themselves rested on axioms would bring those in
too. -/
def directDeps (env : Environment) (entries : NameSet) (root : Name) : Deps := Id.run do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut deps : Deps := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    for d in mentions ci do
      if d == ``sorryAx then deps := { deps with hasSorry := true }
      else if d == root then continue
      else if entries.contains d then deps := { deps with cites := deps.cites.insert d }
      else if cns.contains d then deps := { deps with notions := deps.notions.insert d }
      else if (env.find? d).any (·.isAxiom) then
        deps := { deps with direct := deps.direct.insert d }
        if isLocal env d && !seen.contains d then todo := todo.push d
      else if isLocal env d && !seen.contains d then todo := todo.push d
  return deps

/-- Every Common Notion beneath `root`, as `collectAxioms` finds every axiom beneath it:
the walk goes through everything `mentions` gives, its shared steps, the entries it cites
and what they cite in turn, and stops only at the Common Notions themselves and at
declarations from outside this project, which cannot use them. So the Common Notions are
counted like the postulates, definitions and tacit rules, including those of the entries
a proof cites. -/
def allNotions (env : Environment) (root : Name) : NameSet := Id.run do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut notions : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if cns.contains c then
      notions := notions.insert c
      continue
    unless isLocal env c do continue
    let some ci := env.find? c | continue
    for d in mentions ci do
      unless seen.contains d do todo := todo.push d
  return notions

/-- The shared steps `root` calls on itself: this project's own lemmas and definitions
that live outside the namespace `home`, such as a lemma of Book Zero, `Prop30.meet`, the
corollary `Prop34.bisect` or `Rectangle.eq_rect`. `home` is a proposition's own name, and
for a porism or a companion its proposition's, so that `Prop1.middle` is III.1 Por.'s
own helper, as it is III.1's. The walk passes through the helpers in `home`
(`Prop7.figure`) and Lean's auxiliary declarations, and stops at each shared step, as at
entries, axioms and Common Notions: what a shared step calls on in turn is its own
business, counted by `directDeps` from it. -/
def sharedSteps (env : Environment) (entries : NameSet) (root home : Name) : NameSet :=
  Id.run do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut steps : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    for d in mentions ci do
      if entries.contains d then continue
      if (env.find? d).any (·.isAxiom) then continue
      if cns.contains d || !isLocal env d then continue
      if home.isPrefixOf d || d.isInternal then todo := todo.push d
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
def propRef (n : Name) : String :=
  let book := match n.getPrefix with
    | Name.str _ s => (s.drop 4).toString   -- "BookI" ↦ "I", "BookIII" ↦ "III"
    | _ => "?"
  let num := match n with
    | Name.str _ s => (s.drop 4).toString   -- "Prop12" ↦ "12"
    | _ => "?"
  s!"{book}.{num}"

/-- The reference of an entry, in its one written form (Certificate/FIELDS.md):
`"III.1"` for `Elements.BookIII.Prop1`, `"III.1 Por."` for `Elements.BookIII.Prop1.porism`,
and a companion's as `companions` gives it, `"I.40 general"`. -/
def refOf (n : Name) : String :=
  match companions.lookup n with
  | some r => r
  | none => match n with
    | .str p "porism" => s!"{propRef p} Por."
    | _ => propRef n

def nameStr (n : Name) : String :=
  (n.toString.replace "Elements." "")

/-- The module that declares `n`, or `""` for a declaration of this file. -/
def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | none => ""
  | some idx => (env.header.moduleNames[idx.toNat]!).toString

/-- Every axiom and every `opaque` constant declared in this project's own modules
(`Elements` and below), with the module that declares it. -/
def projectDecls (env : Environment) : Array (Name × String) × Array Name := Id.run do
  let mut axs : Array (Name × String) := #[]
  let mut opaques : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`Elements).isPrefixOf m do continue
    if ci.isAxiom then axs := axs.push (n, m.toString)
    if let .opaqueInfo _ := ci then opaques := opaques.push n
  return (axs, opaques)

/-- The words the axioms are stated in: every definition, instance, theorem, opaque,
inductive type, structure and constructor of this project that the axioms' statements
reach. The walk starts from the constants of the statements of `axs`, goes on through a
definition's or an instance's type and value and through an inductive type's
constructors, and stops at Lean's own constants and at the axioms themselves. An
opaque's value is not read: that Lean cannot see it is the point. -/
def vocabulary (env : Environment) (axs : Array Name) : Array Name := Id.run do
  let mut todo : Array Name := #[]
  for a in axs do
    if let some ci := env.find? a then todo := todo ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut words : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless isLocal env c do continue
    let some ci := env.find? c | continue
    if ci.isAxiom then continue
    words := words.push c
    match ci with
    | .defnInfo v => todo := todo ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | .inductInfo v => todo := todo ++ v.ctors.toArray
    | _ => pure ()
  return words

/-- What kind of declaration a word of the vocabulary is. -/
def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  if Meta.isInstanceCore env ci.name then "instance" else
  match ci with
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => if isStructure env ci.name then "structure" else "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quotient"

/-- The options every statement is printed with (Certificate/FIELDS.md): every name
written out in full, and nothing behind notation. -/
def printOptions (o : Options) : Options :=
  o |>.setBool `pp.notation false |>.setBool `pp.fullNames true
    |>.setBool `pp.funBinderTypes true |>.setBool `pp.fieldNotation false
    |>.setBool `pp.structureInstances false |>.set `format.width (100000 : Nat)

/-- `s` on one line: every run of whitespace made one space, and the ends trimmed. -/
def oneLine (s : String) : String := Id.run do
  let mut out := ""
  let mut space := false
  for c in s.toList do
    if c.isWhitespace then space := true
    else
      if space && !out.isEmpty then out := out.push ' '
      out := out.push c
      space := false
  return out

/-- `e` printed with `printOptions`, on one line. -/
def printExpr (e : Expr) : MetaM String := withOptions printOptions do
  return oneLine ((← Meta.ppExpr e).pretty 100000)

/-- An entry of the certificate: a proposition, a porism or a companion. -/
structure Subject where
  name : Name
  ref : String
  /-- `"proposition"`, `"porism"` or `"companion"`. -/
  kind : String
  /-- The proposition it belongs to: a proposition's own name, a porism's or a
  companion's proposition. Its helpers are the entry's own helpers. -/
  home : Name

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
  /- The companions must be declared, each in the namespace of a proposition, and
     listed by the reference their names give. A porism is never a companion. -/
  for (c, r) in companions do
    unless env.contains c do logError m!"companion {c} is not declared"
    match c with
    | .str p s =>
      unless propSet.contains p do logError m!"companion {c} is not in a proposition's namespace"
      if s == "porism" then logError m!"companion {c}: a porism is an entry of its own, not a companion"
      else unless r == s!"{propRef p} {s}" do
        logError m!"companion {c} should be listed as \"{propRef p} {s}\", not \"{r}\""
    | _ => logError m!"companion {c} is not in a proposition's namespace"
  /- Every entry, in the order of `heath.prop_key`: each proposition, then its porism,
     then its companions. -/
  let mut ordered : Array Subject := #[]
  for p in props do
    ordered := ordered.push ⟨p, refOf p, "proposition", p⟩
    let por := Name.str p "porism"
    if env.contains por then ordered := ordered.push ⟨por, refOf por, "porism", p⟩
    let mine := (companions.filter fun (c, _) => c.getPrefix == p).toArray
    for (c, r) in mine.qsort (·.2 < ·.2) do
      ordered := ordered.push ⟨c, r, "companion", p⟩
  let entrySet := NameSet.ofList (ordered.map (·.name)).toList
  /- facts.json lists the propositions, then the porisms, then the companions. -/
  let subjects := ordered.filter (·.kind == "proposition") ++ ordered.filter (·.kind == "porism")
    ++ ordered.filter (·.kind == "companion")
  let attachedTo (p : Name) := ordered.filter fun t => t.kind != "proposition" && t.home == p
  /- Lean's own axioms, and what the walk finds, for every entry. -/
  let mut axiomsOf : Std.HashMap Name (Array Name) := {}
  let mut depsOf : Std.HashMap Name Deps := {}
  for s in ordered do
    axiomsOf := axiomsOf.insert s.name (← collectAxioms s.name)
    depsOf := depsOf.insert s.name (directDeps env entrySet s.name)
  for (cn, _) in commonNotions do
    axiomsOf := axiomsOf.insert cn (← collectAxioms cn)
  let euclidOnly (xs : Array Name) : Array Name :=
    xs.filter fun a => !leanFoundations.contains a && a != ``sorryAx
  let mut entries : Array Json := #[]
  /- Every axiom any entry rests on, with its module, beside those this project
     declares: an axiom from anywhere else shows up here with the module it came from. -/
  let (declared, opaques) := projectDecls env
  let mut modules : Std.HashMap String String := {}
  let mut axiomNames : Std.HashMap String Name := {}
  for (n, m) in declared do
    modules := modules.insert (nameStr n) m
    axiomNames := axiomNames.insert (nameStr n) n
  for s in subjects do
    let p := s.name
    let axs := axiomsOf.getD p #[]
    for a in euclidOnly axs do
      modules := modules.insert (nameStr a) (moduleOf env a)
      axiomNames := axiomNames.insert (nameStr a) a
    let deps := depsOf.getD p {}
    /- The self-check: Lean's own axioms of the entry are exactly those it uses itself,
       with those of the entries it cites and of the Common Notions it calls on. -/
    let mut expected : NameSet := {}
    for a in euclidOnly deps.direct.toList.toArray do expected := expected.insert a
    for c in deps.cites.toList ++ deps.notions.toList do
      for a in euclidOnly (axiomsOf.getD c #[]) do expected := expected.insert a
    let found := euclidOnly axs
    let missing := found.filter (!expected.contains ·)
    let extra := expected.toList.filter (!found.contains ·)
    unless missing.isEmpty && extra.isEmpty do
      logError m!"{s.ref}: the walk does not account for Lean's axioms: collectAxioms has \
        {missing.toList} beyond what it finds, and it finds {extra} that collectAxioms does not"
    let notions := allNotions env p
    /- A proposition is not finished until its porism is; a companion changes no other
       entry's status. -/
    let porisms := if s.kind == "proposition" then
        (attachedTo p).filter (·.kind == "porism") |>.map (·.name) else #[]
    let sorryHere := deps.hasSorry || porisms.any fun q => (depsOf.getD q {}).hasSorry
    let pending := axs.contains ``sorryAx ||
      porisms.any fun q => (axiomsOf.getD q #[]).contains ``sorryAx
    let status := if sorryHere then "sketched" else if pending then "proved-pending" else "proved"
    let foundations := axs.filter fun a => leanFoundations.contains a
    let notionRefs := (commonNotions.filter fun (n, _) => notions.contains n).map (·.2)
    let doc ← findDocString? env p
    let some ci := env.find? p | throwError "{p} vanished"
    let statement ← Elab.Command.liftTermElabM <| printExpr ci.type
    /- The shared steps that bring in at least one entry, each with the entries it brings
       in, in the order of the books. -/
    let mut shared : Array Json := #[]
    for st in (sharedSteps env entrySet p s.home).toList.toArray.qsort (nameStr · < nameStr ·) do
      let reached := (directDeps env entrySet st).cites
      if reached.isEmpty then continue
      let (file, line) ← declaredAt st
      shared := shared.push <| Json.mkObj [
        ("name", Json.str (nameStr st)),
        ("brings_in", Json.arr ((ordered.filter (reached.contains ·.name)).map (Json.str ·.ref))),
        ("file", Json.str file),
        ("line", toJson line)]
    let family : List (String × Json) := if s.kind == "proposition" then
        [("attached", Json.arr ((attachedTo p).map (Json.str ·.ref)))]
      else [("of", Json.str (refOf s.home))]
    entries := entries.push <| Json.mkObj <| [
      ("ref", Json.str s.ref),
      ("name", Json.str (nameStr p)),
      ("kind", Json.str s.kind)] ++ family ++ [
      ("status", Json.str status),
      ("cites", Json.arr ((deps.cites.toList.map refOf).toArray.qsort (· < ·) |>.map Json.str)),
      ("common_notions", Json.arr (notionRefs.eraseDups.toArray.map Json.str)),
      ("axioms", Json.arr ((found.map nameStr).qsort (· < ·) |>.map Json.str)),
      ("direct_axioms", Json.arr ((deps.direct.toList.map nameStr).toArray.qsort (· < ·)
        |>.map Json.str)),
      ("lean_foundations", Json.arr (foundations.map (Json.str ∘ nameStr))),
      ("shared_steps", Json.arr shared),
      ("enunciation", Json.str (doc.getD "")),
      ("statement", Json.str statement)]
  let axiomModules := modules.toArray.qsort (fun a b => a.1 < b.1)
  /- The statement of every axiom, and every word those statements are written in. -/
  let mut axiomTypes : Array (String × Json) := #[]
  for (key, _) in axiomModules do
    let some ci := (axiomNames.get? key).bind env.find? | throwError "axiom {key} vanished"
    axiomTypes := axiomTypes.push (key, Json.str (← Elab.Command.liftTermElabM <| printExpr ci.type))
  let mut words : Array (String × Json) := #[]
  for w in vocabulary env (axiomModules.filterMap fun (key, _) => axiomNames.get? key) do
    let some ci := env.find? w | continue
    let kind := kindOf env ci
    let type ← Elab.Command.liftTermElabM <| printExpr ci.type
    let value ← match ci.value? (allowOpaque := true) with
      | some v => if kind == "def" || kind == "instance" then
          pure s!" := {← Elab.Command.liftTermElabM <| printExpr v}" else pure ""
      | none => pure ""
    words := words.push (nameStr w, Json.str s!"{kind} : {type}{value}")
  let out := Json.mkObj [("lean_version", Json.str Lean.versionString),
    ("propositions", Json.arr entries),
    ("axiom_modules", Json.mkObj (axiomModules.toList.map fun (n, m) => (n, Json.str m))),
    ("opaque", Json.arr ((opaques.map nameStr).qsort (· < ·) |>.map Json.str)),
    ("axiom_types", Json.mkObj axiomTypes.toList),
    ("vocabulary", Json.mkObj words.toList)]
  IO.FS.writeFile "facts.json" (out.pretty ++ "\n")
  let count (k : String) := (subjects.filter (·.kind == k)).size
  logInfo m!"certificate: {count "proposition"} propositions, {count "porism"} porisms and \
    {count "companion"} companions written to facts.json, with {axiomTypes.size} axioms and \
    {words.size} words of their vocabulary"
