import Lean
import Elements

/-!
# The certificate

Run with `lake env lean Certificate/Facts.lean` (after `lake build`). It writes
`facts.json`, whose fields `Certificate/FIELDS.md` sets out. There is an entry for
every proposition, for every porism (`Prop1.porism`, "III.1 Por."), and for every
companion that `Elements/Companions.lean` lists, each checked here. For each it records,
straight from Lean's own proof terms:

* its statement, printed with every name written out and no notation;
* whether the proof is finished, or still has a `sorry` in it;
* which other entries it cites directly;
* exactly which postulates, definitions and tacit rules it rests on
  (via `#print axioms`, i.e. `Lean.collectAxioms`), and which of them it uses itself;
* of those it uses itself, which its own Lean names (in its own declaration, or a helper
  written for its proposition), and which it inherits through a lemma of Book Zero or a
  shared step, each with the lemma that brings it in;
* which Common Notions it rests on, found by a walk that goes wherever
  `collectAxioms` goes, so that, like the postulates, they include those of the
  entries it cites, with the calculus's `Coincidence.step` counted as Common Notion 4
  when named in a walked local declaration's value;
* which proved rules it rests on: the tacit rules that are theorems now, which
  `collectAxioms` passes through without a trace, found by a walk that goes wherever it
  goes and must find exactly the axioms it finds;
* which shared steps it calls on (`Prop30.meet`, `Prop34.bisect`, `Rectangle.eq_rect`),
  and the entries each one brings in;
* for I.4 and I.8, whose derivations cite laws inside a hypothetical placement, each law
  their own Lean names, the theorems that prove it, and the construction rules beneath
  those proofs (`cited_laws`).

Every walk reads a declaration in the same way, through `mentions`: its type, its value
and an inductive type's constructors, as `collectAxioms` reads them. The walks reject a
constant from any imported module outside `Elements`, `Init`, `Std` and `Lean`, naming
the declaration and its module. Only Lean's own modules may end a walk at this boundary:
those under `Init`, `Std` and `Lean` whose `.olean`, as the search path finds it, lies in
the library of the running Lean toolchain. A module's name is not evidence of its origin.
The run checks itself against Lean: for every entry, the axioms `collectAxioms` finds must be exactly
those the entry uses itself, together with those of the entries it cites and of the
Common Notions it calls on; those it uses itself must be exactly those its own Lean
names, together with those it inherits; and the walk that finds its proved rules must find
exactly the axioms `collectAxioms` finds. If they ever differ, the run fails.

For the whole environment it also records the module that declares every axiom of
this project, and of every axiom an entry rests on; the `opaque` words; the exact
statement of every axiom; the vocabulary that the axioms' statements and the
entries' statements are written in; and which of the axioms are construction rules
(docs/FORMALIZATION.md, section 9), read from their statements. So
`scripts/check_fidelity.py` can check from Lean
itself, not from the source text, that every axiom lives in `Elements/Foundations/`,
that the primitive words stay opaque, that no axiom has changed what it says, and that
no word a statement uses (`Touches`, `rect`, `Parallel`) has changed what it means.

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

/-- The restricted calculus's marker for Common Notion 4. Each congruence constructor
takes a `Coincidence` argument; a derivation taking the step supplies `Coincidence.step`.
Like `#print axioms`, this records proof-term dependencies: count the step when a walked
local declaration's value names it, without evaluating the proof. A transformer that
only passes a derivation's own marker along as a bound variable does not introduce a step.
Reaching the marker through a type's constructor list alone does not count either.
The single backtick permits this tooling to land before the calculus declares the name.
The marker changes only the reported notions. -/
def coincidenceStep : Name := `Elements.Superposition.Coincidence.step

/-- The books, their Lean namespaces and how many propositions each has. A proposition
of a later book may cite one of an earlier book, and the walk below records it by its
own book: `"I.47"` among the citations of II.9. -/
def books : List (String × Name × Nat) :=
  [("I", `Elements.BookI, 48), ("II", `Elements.BookII, 14), ("III", `Elements.BookIII, 37)]

/-- The companions, as the edition lists them: `Elements.companions`, whose note in
`Elements/Companions.lean` says what they are. The checks are this file's: the run below
refuses an entry that is not declared, is not in a proposition's namespace, is a porism,
or is not listed by the reference its name gives. -/
def companions : List (Name × String) := Elements.companions

variable {m : Type → Type} [Monad m] [MonadError m]

/-- The imported modules that Lean's own toolchain supplies: those under the roots
`Init`, `Std` and `Lean` whose `.olean`, as the search path finds it for the import, lies
in the library directory of the running `lean`, both paths resolved. A module of any
other origin under those roots, such as a separately compiled `Lean.Hidden`, is left
out, so a walk that reaches it is refused. -/
def toolchainModules (env : Environment) : IO NameSet := do
  let lib ← IO.FS.realPath (← getLibDir (← getBuildDir))
  let mut mods : NameSet := {}
  for mod in env.header.moduleNames do
    unless [`Init, `Std, `Lean].any (·.isPrefixOf mod) do continue
    let file ← IO.FS.realPath (← findOLean mod)
    if lib.components.isPrefixOf file.components then mods := mods.insert mod
  return mods

/-- Is `n` declared in `Elements` or this file? Only the modules in `toolchain`, which
`toolchainModules` gives, may be treated as external leaves. Refuse every other declaring
module before any walk can stop at it; a declaration's namespace is not evidence of its
module, nor a module's name of where it came from. -/
def isLocal (env : Environment) (toolchain : NameSet) (n : Name) : m Bool := do
  match env.getModuleIdxFor? n with
  | none => return true
  | some idx =>
    let mod := env.header.moduleNames[idx.toNat]!
    if (`Elements).isPrefixOf mod then return true
    if toolchain.contains mod then return false
    throwError "certificate: declaration {n.toString} is declared in unsupported module \
      {mod.toString}; expected Elements, or Init, Std or Lean from the running Lean toolchain"

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
def directDeps (env : Environment) (toolchain entries : NameSet) (root : Name) : m Deps := do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut deps : Deps := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    let some ci := env.find? c | continue
    for d in mentions ci do
      let isProject ← isLocal env toolchain d
      if d == ``sorryAx then deps := { deps with hasSorry := true }
      else if d == root then continue
      else if entries.contains d then deps := { deps with cites := deps.cites.insert d }
      else if cns.contains d then deps := { deps with notions := deps.notions.insert d }
      else if (env.find? d).any (·.isAxiom) then
        deps := { deps with direct := deps.direct.insert d }
        if isProject && !seen.contains d then todo := todo.push d
      else if isProject && !seen.contains d then todo := todo.push d
  return deps

/-- Every Common Notion beneath `root`, as `collectAxioms` finds every axiom beneath it:
the walk goes through everything `mentions` gives, its shared steps, the entries it cites
and what they cite in turn, and stops only at the Common Notions themselves and at
declarations from Lean's own modules. Any other module outside `Elements` is refused.
So the Common Notions are counted like the postulates, definitions and tacit rules,
including those of the entries
a proof cites. A walked local declaration's value naming `Coincidence.step` also records
Common Notion 4. As with `#print axioms`, this follows named proof-term dependencies:
passing a marker along as a bound variable adds no step, while naming the constant in
a helper counts even if evaluation would not take that branch. -/
def allNotions (env : Environment) (toolchain : NameSet) (root : Name) : m NameSet := do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut notions : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    if cns.contains c then
      notions := notions.insert c
      continue
    let some ci := env.find? c | continue
    if let some v := ci.value? (allowOpaque := true) then
      let used := v.getUsedConstants
      if used.contains coincidenceStep then
        notions := notions.insert ``Elements.CommonNotion4
    for d in mentions ci do
      unless seen.contains d do todo := todo.push d
  return notions

/-- What `beneath` finds under a declaration. -/
structure Beneath where
  /-- Every axiom it rests on, as `collectAxioms` finds them. -/
  axioms : NameSet := {}
  /-- Every proved rule it rests on. -/
  rules : NameSet := {}

/-- Every axiom and every proved rule beneath `root`. A proved rule is one of `rules`, the
tacit rules that are theorems now (`proved_rules`, below). The walk goes wherever
`collectAxioms` goes, through everything `mentions` gives: the entries `root` cites and
what they cite in turn, the Common Notions, the shared steps, and the proved rules
themselves, so that a rule proved from another brings in both. It records an axiom where
`directDeps` does, at a mention, and stops only at declarations from Lean's own modules;
any other module outside `Elements` is refused. A proved rule is a theorem, so
`collectAxioms` passes through it without a trace, and an axiom list can only show the
axioms beneath it. The run checks, for every entry, that this walk finds exactly the
axioms `collectAxioms` finds, Lean's own aside, so the proved rules come from the walk
that finds the entry's axioms. -/
def beneath (env : Environment) (toolchain rules : NameSet) (root : Name) : m Beneath := do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut found : Beneath := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    let some ci := env.find? c | continue
    for d in mentions ci do
      if (env.find? d).any (·.isAxiom) then found := { found with axioms := found.axioms.insert d }
      if rules.contains d then found := { found with rules := found.rules.insert d }
      unless seen.contains d do todo := todo.push d
  return found

/-- The shared steps `root` calls on itself: this project's own lemmas and definitions
that live outside the namespace `home`, such as a lemma of Book Zero, `Prop30.meet`, the
corollary `Prop34.bisect` or `Rectangle.eq_rect`. `home` is a proposition's own name, and
for a porism or a companion its proposition's, so that `Prop1.middle` is III.1 Por.'s
own helper, as it is III.1's. The walk passes through the helpers in `home`
(`Prop7.figure`) and Lean's auxiliary declarations, and stops at each shared step, as at
entries, axioms and Common Notions: what a shared step calls on in turn is its own
business, counted by `directDeps` from it. -/
def sharedSteps (env : Environment) (toolchain entries : NameSet) (root home : Name) :
    m NameSet := do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut steps : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    let some ci := env.find? c | continue
    for d in mentions ci do
      let isProject ← isLocal env toolchain d
      if entries.contains d then continue
      if (env.find? d).any (·.isAxiom) then continue
      if cns.contains d || !isProject then continue
      if home.isPrefixOf d || d.isInternal then todo := todo.push d
      else steps := steps.insert d
  return steps

/-- What `ownDeps` finds beneath a declaration: the part of its `direct` axioms that its
own Lean names, and the lemmas through which it inherits the rest. -/
structure Own where
  /-- The axioms its own declarations name: the declaration itself, the helpers in the
  namespace `home` (`Prop7.figure`, and `Prop1.middle` for III.1 Por.) and Lean's
  auxiliary declarations. -/
  axioms : NameSet := {}
  /-- The lemmas those declarations call on: this project's own declarations outside
  `home` that are not entries, axioms or Common Notions, such as a lemma of Book Zero
  (`EqualCircles.radii`) or a shared step (`Prop5.base`, or `Prop1.perpendicular` for
  III.19). What a lemma brings in is counted by `directDeps` from it. -/
  lemmas : NameSet := {}
  /-- Its own declarations themselves: the declaration, its helpers in `home` and Lean's
  auxiliary declarations for them, as the walk visits them. `cited_laws` reads the laws
  they name. -/
  decls : NameSet := {}

/-- Walk `root` as `directDeps` does, through `mentions`, and in the same steps, but pass
only through its own declarations, as `sharedSteps` does: the helpers in `home` and Lean's
auxiliary declarations. At any other declaration of this project that is not an entry, an
axiom or a Common Notion, record it as a lemma and stop. So an axiom is `own` when the
proposition's own Lean names it, and every other axiom `directDeps` finds comes in through
one of the `lemmas`; the run checks that it does. At an axiom of this project the walk
reads its statement, as `directDeps` and `collectAxioms` do. -/
def ownDeps (env : Environment) (toolchain entries : NameSet) (root home : Name) : m Own := do
  let cns := commonNotions.map (·.1)
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut own : Own := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    let some ci := env.find? c | continue
    unless ci.isAxiom do own := { own with decls := own.decls.insert c }
    for d in mentions ci do
      let isProject ← isLocal env toolchain d
      if d == ``sorryAx || d == root || entries.contains d || cns.contains d then continue
      if (env.find? d).any (·.isAxiom) then
        own := { own with axioms := own.axioms.insert d }
        if isProject && !seen.contains d then todo := todo.push d
      else if !isProject || seen.contains d then continue
      else if home.isPrefixOf d || d.isInternal then todo := todo.push d
      else own := { own with lemmas := own.lemmas.insert d }
  return own

/-! ## Construction rules, and the laws a derivation cites

A construction rule is an axiom whose conclusion, once this project's definitions are
unfolded, asserts `Exists` in positive position (docs/FORMALIZATION.md, "Construction
rules"). The names below take a single backtick, as `coincidenceStep` does, so that the
certificate also runs on a library without the restricted calculus. -/

/-- The laws a restricted derivation may cite, as a type. -/
def citedType : Name := `Elements.Superposition.Cited

/-- What a cited law asserts in an interpretation: `Cited.Holds I c`. -/
def citedHolds : Name := `Elements.Superposition.Cited.Holds

/-- The interpretation in Euclid's own words, in which the restricted rule is assumed. -/
def primitivesName : Name := `Elements.primitives

/-- How deep a statement is read, an unfolded definition counting as a step down: far more
than any statement here needs, so a definition that unfolds without end fails the run
instead of being followed for ever. -/
def readDepth : Nat := 1000

/-- `e` with the definition at its head unfolded and applied to `e`'s arguments, when that
head is a definition of this project; `none` for anything else (Lean's own definitions, an
opaque word, an axiom, a theorem, a constructor or an inductive type). -/
def unfoldHead? (env : Environment) (toolchain : NameSet) (e : Expr) : m (Option Expr) := do
  let .const n us := e.getAppFn | return none
  unless ← isLocal env toolchain n do return none
  let some ci@(.defnInfo _) := env.find? n | return none
  return some ((ci.instantiateValueLevelParams! us).beta e.getAppArgs)

/-- Field `i` of the structure value `s`: `s`'s head unfolded while it is a definition of
this project, and a `let` at its head substituted into its body, until it is a constructor
applied to its arguments. A projection at its head, of a structure nested in another or of
a field that is a function, is read the same way, and the field it names, applied to the
projection's arguments, takes its place. `none` when there is never a constructor, as for
a structure given by an opaque word or a variable. -/
def projField? (env : Environment) (toolchain : NameSet) (s : Expr) (i : Nat) :
    m (Option Expr) := do
  let mut s := s.consumeMData.headBeta
  let mut pending : List (Nat × Array Expr) := [(i, #[])]
  for _ in [0:readDepth] do
    match s.getAppFn with
    | .proj _ j t =>
      pending := (j, s.getAppArgs) :: pending
      s := t.consumeMData.headBeta
    | .letE _ _ v b _ => s := (mkAppN (b.instantiate1 v) s.getAppArgs).consumeMData.headBeta
    | .const n _ =>
      if let some (.ctorInfo c) := env.find? n then
        match pending with
        | [] => return none
        | (j, args) :: rest =>
          let some f := s.getAppArgs[c.numParams + j]? | return none
          let f := (f.beta args).consumeMData.headBeta
          if rest.isEmpty then return some f
          pending := rest
          s := f
      else match ← unfoldHead? env toolchain s with
        | some s' => s := s'.consumeMData.headBeta
        | none => return none
    | _ => return none
  throwError "certificate: a structure value is too deep to read for construction rules"

/-- Does `e`, read at polarity `pos`, assert `Exists` in positive position? `And` and `Or`
keep the polarity of their parts, `Not` and the left of an implication (a `∀` binder's type)
flip it, and both sides of an `Iff` are read at both. A definition of this project is
unfolded where it stands, a `let` is substituted into its body, a projection of a structure
that a definition of this project gives (an instance's `≤`) is read through that
definition, and anything else is a leaf that asserts no existence. -/
def assertsExists (env : Environment) (toolchain : NameSet) (fuel : Nat) (pos : Bool)
    (e : Expr) : m Bool := do
  match fuel with
  | 0 => throwError "certificate: a statement is too deep to read for construction rules"
  | fuel + 1 =>
    let go := assertsExists env toolchain fuel
    match e.consumeMData with
    | .forallE _ d b _ => return (← go (!pos) d) || (← go pos b)
    | .lam _ _ b _ => go pos b
    | .letE _ _ v b _ => go pos (b.instantiate1 v)
    | .proj _ i s =>
      match ← projField? env toolchain s i with
      | some f => go pos f
      | none => return false
    | e =>
      let args := e.getAppArgs
      match e.getAppFn with
      | .lam .. => go pos e.headBeta
      | .letE _ _ v b _ => go pos (mkAppN (b.instantiate1 v) args)
      | .const n _ =>
        if n == ``Exists then
          if pos then return true
          match args.back? with
          | some p => go pos p
          | none => return false
        else if (n == ``And || n == ``Or) && args.size == 2 then
          return (← go pos args[0]!) || (← go pos args[1]!)
        else if n == ``Not && args.size == 1 then go (!pos) args[0]!
        else if n == ``Iff && args.size == 2 then
          for a in args do
            if (← go true a) || (← go false a) then return true
          return false
        else if let some p := env.getProjectionFnInfo? n then
          match args[p.numParams]? with
          | some s =>
            match ← projField? env toolchain s p.i with
            | some f => go pos (f.beta (args.extract (p.numParams + 1) args.size))
            | none => return false
          | none => return false
        else match ← unfoldHead? env toolchain e with
          | some e' => go pos e'
          | none => return false
      | _ => return false

/-- What a statement concludes: its type with the leading `∀` binders and the hypotheses of
its implications stripped off. -/
def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | .mdata _ e => conclusion e
  | e => e

/-- Is an axiom stated as `ty` a construction rule: does its conclusion assert `Exists` in
positive position, once this project's definitions are unfolded? -/
def constructs (env : Environment) (toolchain : NameSet) (ty : Expr) : m Bool :=
  assertsExists env toolchain readDepth true (conclusion ty)

/-- The constructor `c` of `Cited` that the statement `ty` says holds in Euclid's own
words: `ty` is exactly `Cited.Holds primitives c`. -/
def provesLaw? (ty : Expr) : Option Name :=
  match ty.consumeMData.getAppFn, ty.consumeMData.getAppArgs with
  | .const h _, #[.const i _, .const c _] =>
    if h == citedHolds && i == primitivesName then some c else none
  | _, _ => none

/-- The theorems beneath `root` that prove a cited law, by its constructor among `laws`:
each a theorem whose statement is exactly `Cited.Holds primitives c`. The walk reads every
declaration through `mentions`, goes through every declaration of this project, and stops
at the other entries: a law proved only inside a proposition that `root` cites is not
found. -/
def lawProofs (env : Environment) (toolchain entries : NameSet) (root : Name)
    (laws : Array Name) : m (Std.HashMap Name (Array Name)) := do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut found : Std.HashMap Name (Array Name) := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    let some ci := env.find? c | continue
    if let .thmInfo _ := ci then
      if let some law := provesLaw? ci.type then
        if laws.contains law then found := found.insert law ((found.getD law #[]).push c)
    for d in mentions ci do
      if d != root && entries.contains d then continue
      unless seen.contains d do todo := todo.push d
  return found

/-- The theorems among `decls` that prove a cited law among `laws`, by its constructor, as
`lawProofs` recognises them. Given an entry's own declarations and the lemmas they call on
(`Own.decls` and `Own.lemmas`), these are the proofs its own Lean names directly. -/
def namedProofs (env : Environment) (decls : NameSet) (laws : Array Name) :
    Std.HashMap Name (Array Name) := Id.run do
  let mut found : Std.HashMap Name (Array Name) := {}
  for d in decls.toList do
    if let some ci@(.thmInfo _) := env.find? d then
      if let some law := provesLaw? ci.type then
        if laws.contains law then found := found.insert law ((found.getD law #[]).push d)
  return found

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

/-- The words the axioms and the entries are stated in: every definition, instance,
theorem, opaque, inductive type, structure and constructor of this project that the
statement of an axiom, a proposition, a porism or a companion reaches. The walk starts
from the constants of the statements of `roots`, goes on through every word's type, a
definition's or an instance's value and an inductive type's constructors, and stops at
Lean's own constants and at the axioms themselves. An opaque's value is not read: that
Lean cannot see it is the point. So `Touches`, which only Book III's statements use, is a
word, and a change to it fails the lock as a changed axiom would. -/
def vocabulary (env : Environment) (toolchain : NameSet) (roots : Array Name) : m (Array Name) := do
  let mut todo : Array Name := #[]
  for a in roots do
    let _ ← isLocal env toolchain a
    if let some ci := env.find? a then todo := todo ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut words : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless ← isLocal env toolchain c do continue
    let some ci := env.find? c | continue
    if ci.isAxiom then continue
    words := words.push c
    todo := todo ++ ci.type.getUsedConstants
    match ci with
    | .defnInfo v => todo := todo ++ v.value.getUsedConstants
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
  let toolchain ← toolchainModules env
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
    depsOf := depsOf.insert s.name (← directDeps env toolchain entrySet s.name)
  for (cn, _) in commonNotions do
    axiomsOf := axiomsOf.insert cn (← collectAxioms cn)
  let euclidOnly (xs : Array Name) : Array Name :=
    xs.filter fun a => !leanFoundations.contains a && a != ``sorryAx
  /- Proved tacit rules keep their names when they leave the axiom lock. Record what
     Lean finds beneath each, so the policy check can still refuse a forbidden rule, and
     the entries each cites, found by the entries' own walk, `directDeps`: an entry whose
     proof uses a proved rule is found to cite every entry in the rule's list. They are
     listed before the entries, so that each entry records which of them it rests on, and
     a pin can refuse an entry that comes to use one. -/
  let mut provedRules : Array (String × Json) := #[]
  let mut provedRuleCites : Array (String × Json) := #[]
  let mut ruleSet : NameSet := {}
  for (n, ci) in env.constants.toList do
    -- Only this project's own tacit rules, by declaring module, as `isLocal` decides; a
    -- listing, not a walk, so a constant from another module is skipped here, not refused.
    let own := (env.getModuleIdxFor? n).all fun idx =>
      (`Elements).isPrefixOf env.header.moduleNames[idx.toNat]!
    unless own && (`Elements.Tacit).isPrefixOf n do continue
    if let .thmInfo _ := ci then
      let axs := euclidOnly (← collectAxioms n)
      provedRules := provedRules.push
        (nameStr n, toJson ((axs.map nameStr).qsort (· < ·)))
      let cites := (← directDeps env toolchain entrySet n).cites
      provedRuleCites := provedRuleCites.push
        (nameStr n, toJson ((cites.toList.map refOf).toArray.qsort (· < ·)))
      ruleSet := ruleSet.insert n
  let mut entries : Array Json := #[]
  /- What each lemma an entry calls brings in, found once. -/
  let mut lemmaAxioms : Std.HashMap Name (Array Name) := {}
  /- Every axiom any entry rests on, with its module, beside those this project
     declares: an axiom from anywhere else shows up here with the module it came from. -/
  let (declared, opaques) := projectDecls env
  let mut modules : Std.HashMap String String := {}
  let mut axiomNames : Std.HashMap String Name := {}
  for (n, m) in declared do
    modules := modules.insert (nameStr n) m
    axiomNames := axiomNames.insert (nameStr n) n
  /- The construction rules: of the axioms `axiom_modules` lists, those this project
     declares and those an entry rests on, the ones whose conclusion asserts existence. -/
  let mut known : NameSet := NameSet.ofList (declared.map (·.1)).toList
  for s in subjects do
    for a in euclidOnly (axiomsOf.getD s.name #[]) do known := known.insert a
  let mut construction : NameSet := {}
  for a in known.toList do
    let some ci := env.find? a | continue
    if ← constructs env toolchain ci.type then construction := construction.insert a
  /- The laws a derivation may cite, in the order of their type. -/
  let laws : Array Name := match env.find? citedType with
    | some (.inductInfo v) => v.ctors.toArray
    | _ => #[]
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
    /- The proved rules it rests on, from a walk that must find exactly Lean's axioms of
       the entry: a proved rule leaves no trace in them but the axioms beneath it. -/
    let under ← beneath env toolchain ruleSet p
    let walked := euclidOnly under.axioms.toList.toArray
    let unwalked := found.filter (!walked.contains ·)
    let unfound := walked.filter (!found.contains ·)
    unless unwalked.isEmpty && unfound.isEmpty do
      logError m!"{s.ref}: the walk for its proved rules does not find Lean's axioms: \
        collectAxioms has {unwalked.toList} beyond what it finds, and it finds \
        {unfound.toList} that collectAxioms does not"
    /- Its own axioms, and those it inherits: each axiom it uses itself that its own Lean
       does not name, with every lemma it calls that brings the axiom in, in name order. -/
    let own ← ownDeps env toolchain entrySet p s.home
    let ownFound := euclidOnly own.axioms.toList.toArray
    let mut inherited : Std.HashMap Name (Array Name) := {}
    for lem in own.lemmas.toList.toArray.qsort (nameStr · < nameStr ·) do
      unless lemmaAxioms.contains lem do
        lemmaAxioms := lemmaAxioms.insert lem
          (euclidOnly (← directDeps env toolchain entrySet lem).direct.toList.toArray)
      for a in lemmaAxioms.getD lem #[] do
        unless ownFound.contains a do inherited := inherited.insert a ((inherited.getD a #[]).push lem)
    /- The second self-check: what the entry uses itself is exactly what its own Lean
       names, with what it inherits through its lemmas. -/
    let direct := euclidOnly deps.direct.toList.toArray
    let split := ownFound ++ inherited.toArray.map (·.1)
    let unsplit := direct.filter (!split.contains ·)
    let unused := split.filter (!direct.contains ·)
    unless unsplit.isEmpty && unused.isEmpty do
      logError m!"{s.ref}: its own axioms and those it inherits do not make up its direct \
        axioms: {unsplit.toList} are direct but neither, and {unused.toList} are one but not direct"
    let mut inheritedJson : Array (String × Json) := #[]
    for (a, lems) in inherited.toArray.qsort (nameStr ·.1 < nameStr ·.1) do
      let mut through : Array Json := #[]
      for lem in lems do
        let (file, line) ← declaredAt lem
        through := through.push <| Json.mkObj [
          ("name", Json.str (nameStr lem)), ("file", Json.str file), ("line", toJson line)]
      inheritedJson := inheritedJson.push (nameStr a, Json.arr through)
    let notions ← allNotions env toolchain p
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
    let steps ← sharedSteps env toolchain entrySet p s.home
    for st in steps.toList.toArray.qsort (nameStr · < nameStr ·) do
      let reached := (← directDeps env toolchain entrySet st).cites
      if reached.isEmpty then continue
      let (file, line) ← declaredAt st
      shared := shared.push <| Json.mkObj [
        ("name", Json.str (nameStr st)),
        ("brings_in", Json.arr ((ordered.filter (reached.contains ·.name)).map (Json.str ·.ref))),
        ("file", Json.str file),
        ("line", toJson line)]
    /- The laws its own declarations name, each with the theorems that prove it and the
       construction rules beneath those proofs. A law named with no proof found fails the
       run: an empty list of rules would claim a law proved with none. -/
    let mut citedJson : Array Json := #[]
    let mut named : Array Name := #[]
    for law in laws do
      if own.decls.toList.any fun d => (env.find? d).any fun ci => (mentions ci).contains law then
        named := named.push law
    unless named.isEmpty do
      let reached ← lawProofs env toolchain entrySet p named
      let direct := namedProofs env (own.lemmas.toList.foldl (·.insert ·) own.decls) named
      for law in named do
        let all := reached.getD law #[]
        if all.isEmpty then
          logError m!"{s.ref}: its own Lean names the law {law}, but no theorem stating \
            exactly `Cited.Holds primitives {law}` is reached from it without passing \
            through another entry"
        /- The proofs its own Lean names directly, when there are any and every proof
           reached lies beneath one of them; otherwise every proof reached. -/
        let mine := direct.getD law #[]
        let mut beneath : NameSet := {}
        for d in mine do
          for x in (← lawProofs env toolchain entrySet d #[law]).getD law #[] do
            beneath := beneath.insert x
        let found := (if !mine.isEmpty && all.all beneath.contains then mine else all).qsort
          (nameStr · < nameStr ·)
        let rulesBeneath (proofs : Array Name) : Elab.Command.CommandElabM NameSet := do
          let mut rules : NameSet := {}
          for proof in proofs do
            for a in ← collectAxioms proof do
              if construction.contains a then rules := rules.insert a
          return rules
        let rules ← rulesBeneath found
        /- The self-check: the proofs listed have beneath them every construction rule
           beneath any proof reached. If they ever differ, the run fails. -/
        let everyRule ← rulesBeneath all
        unless rules.toList == everyRule.toList do
          logError m!"{s.ref}: the proofs listed for the law {law} have the construction \
            rules {rules.toList} beneath them, but the proofs reached have {everyRule.toList}"
        let mut proofsJson : Array Json := #[]
        for proof in found do
          let (file, line) ← declaredAt proof
          proofsJson := proofsJson.push <| Json.mkObj [
            ("name", Json.str (nameStr proof)), ("file", Json.str file), ("line", toJson line)]
        let short := match law with
          | .str _ x => x
          | _ => law.toString
        citedJson := citedJson.push <| Json.mkObj [
          ("law", Json.str short),
          ("proofs", Json.arr proofsJson),
          ("construction_rules", Json.arr ((rules.toList.map nameStr).toArray.qsort (· < ·)
            |>.map Json.str))]
    let cited : List (String × Json) :=
      if citedJson.isEmpty then [] else [("cited_laws", Json.arr citedJson)]
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
      ("proved_rules", Json.arr ((under.rules.toList.map nameStr).toArray.qsort (· < ·)
        |>.map Json.str)),
      ("direct_axioms", Json.arr ((deps.direct.toList.map nameStr).toArray.qsort (· < ·)
        |>.map Json.str)),
      ("own_axioms", Json.arr ((ownFound.map nameStr).qsort (· < ·) |>.map Json.str)),
      ("inherited", Json.mkObj inheritedJson.toList),
      ("lean_foundations", Json.arr (foundations.map (Json.str ∘ nameStr))),
      ("shared_steps", Json.arr shared),
      ("enunciation", Json.str (doc.getD "")),
      ("statement", Json.str statement)] ++ cited
  let axiomModules := modules.toArray.qsort (fun a b => a.1 < b.1)
  /- The statement of every axiom, and every word those statements and the entries'
     statements are written in. -/
  let mut axiomTypes : Array (String × Json) := #[]
  for (key, _) in axiomModules do
    let some ci := (axiomNames.get? key).bind env.find? | throwError "axiom {key} vanished"
    axiomTypes := axiomTypes.push (key, Json.str (← Elab.Command.liftTermElabM <| printExpr ci.type))
  let mut words : Array (String × Json) := #[]
  let roots := (axiomModules.filterMap fun (key, _) => axiomNames.get? key) ++ subjects.map (·.name)
  for w in ← vocabulary env toolchain roots do
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
    ("vocabulary", Json.mkObj words.toList),
    ("proved_rules", Json.mkObj (provedRules.qsort (·.1 < ·.1)).toList),
    ("proved_rule_cites", Json.mkObj (provedRuleCites.qsort (·.1 < ·.1)).toList),
    ("construction_rules", Json.arr ((construction.toList.map nameStr).toArray.qsort (· < ·)
      |>.map Json.str))]
  IO.FS.writeFile "facts.json" (out.pretty ++ "\n")
  let count (k : String) := (subjects.filter (·.kind == k)).size
  logInfo m!"certificate: {count "proposition"} propositions, {count "porism"} porisms and \
    {count "companion"} companions written to facts.json, with {axiomTypes.size} axioms and \
    {words.size} words of the vocabulary they and the entries are stated in"
