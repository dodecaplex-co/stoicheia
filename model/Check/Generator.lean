import Lean

/-!
# The generator: the laws, from the library's own declarations

`Model/Laws.lean` states every law of the library over a signature `S`, as the fields of one
structure, `Laws S`. This file writes it, and two files that check it, from the library's
declarations as Lean elaborated them, never from their printed text; and it checks, at every
build, that what is committed is what it writes, and that each law it wrote translates back
to the library's axiom. The [README](../README.md) says why, and how the pieces fit.

* **What it reads.** The axioms declared in the modules of `Elements.Foundations`: exactly
  the names in the `[axioms]` of `Certificate/axioms.lock`, each with the statement printed
  there, the lock being the one whose sha256 `model/lock.sha256` holds.
* **How it translates.** A statement is an expression, and the translation replaces every
  constant of the project in it, and nothing else: each of the seventeen opaque words by the
  field of `S` that stands for it (`fields`), `Elements.Kind` and its constructors by
  `Model.Kind`'s (`kinds`), and each defined word by a definition over `S`. The eight defined
  words behind the magnitudes are written by hand in `Model/Signature.lean`
  (`signatureWords`) and checked here; every other defined word a law reaches is translated
  in the same way, once, and written out. Lean's own constants, those of `Init`, stay as
  they are. Constants declared in exactly the four `pureModules` are shared by identity,
  with their universe arguments preserved and their transitive types and values audited by
  `checkPureModules`. Any other constant is an error.
* **What it writes.** `Model/Laws.lean`, with the translated words, each law as a
  definition named as in the lock (`Law.Postulate1 S`), and the structures `Neutral S` and
  `Laws S`; `Check/Laws.lean`, the round trip by the kernel; and `Model/Assembly.lean`,
  which gathers the proofs in the plane into `euclidean_laws`.
* **What it checks.** `checkFiles` (run by `Check/Generated.lean`) writes the three files
  again in memory and compares them with the committed ones, after checking the lock, its
  hash and the axioms; `checkRoundTrip` (run by `Check/RoundTrip.lean`) takes the laws and
  words as Lean elaborated them from the committed `Model/Laws.lean`, translates them back,
  and compares each with the library's declaration, binder by binder. `checkModelImports`,
  also run by `Check/RoundTrip.lean`, checks the import headers of Model and the pure modules;
  `checkModelImportClosure` checks the graph of compiled imports rooted at `Model`.

This file is a metaprogram, so it lives in `Check/`, apart from the proofs: nothing under
`Model/` imports it, and it imports nothing but Lean.

The plan it carries out, reading the elaborated declarations rather than their text,
translating by structure, refusing any untranslated constant, checking that each law put back
in the library's words is the library's, and pinning the vocabulary, is Astra's, from the third
outside answer, on issue #73; our warm thanks. Its walk of the vocabulary and its printing of
the lock's statements follow `Certificate/Facts.lean`, so that the two read the lock alike.
-/

open Lean Meta Elab Command

namespace Check.Generator

/-! ## The lock's hash

Lean has no sha256 of its own, so here is one, after FIPS 180-4, the standard that defines
it: enough for the generator to check the hash in `model/lock.sha256` itself, so that `lake
build` alone notices a lock the model was not brought up to date with. -/

/-- The 64 round constants of SHA-256. -/
private def sha256Rounds : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The sha256 of `msg` in lower-case hexadecimal, as `shasum -a 256` prints it. -/
def sha256 (msg : ByteArray) : String := Id.run do
  let rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do
    m := m.push 0
  let bits : UInt64 := msg.size.toUInt64 * 8
  for i in [0:8] do
    m := m.push (bits >>> (8 * (7 - i)).toUInt64).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f,
    0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for chunk in [0:m.size / 64] do
    let mut w : Array UInt32 := Array.replicate 64 0
    for i in [0:16] do
      let byte (j : Nat) : UInt32 := (m.get! (chunk * 64 + 4 * i + j)).toUInt32
      w := w.set! i ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3)
    for i in [16:64] do
      let s0 := rotr w[i-15]! 7 ^^^ rotr w[i-15]! 18 ^^^ (w[i-15]! >>> 3)
      let s1 := rotr w[i-2]! 17 ^^^ rotr w[i-2]! 19 ^^^ (w[i-2]! >>> 10)
      w := w.set! i (w[i-16]! + s0 + w[i-7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for i in [0:64] do
      let t1 := hh + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) +
        sha256Rounds[i]! + w[i]!
      let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + hh]
  let hex (x : UInt32) : String :=
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    "".pushn '0' (8 - s.length) ++ s
  return String.join (h.toList.map hex)

/-! ## The lock -/

/-- A table of `Certificate/axioms.lock`: the count its header gives, and its entries, each a
name and its printed statement, in the lock's order. -/
structure LockTable where
  count : Nat := 0
  entries : Array (String × String) := #[]

/-- `Certificate/axioms.lock`, read: the `[axioms]` and the `[vocabulary]`. -/
structure Lock where
  axioms : LockTable
  vocabulary : LockTable

/-- The lock read from its text: the two tables of TOML strings that
`scripts/check_fidelity.py` writes, each string as JSON writes it. -/
def parseLock (text : String) : Except String Lock := do
  let mut axioms : LockTable := {}
  let mut vocabulary : LockTable := {}
  let mut table : Option String := none
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    if line.startsWith "[" then
      let header := (line.splitOn "#")
      let name := header[0]!.trimAscii.toString
      let count := (header[1]?.map (·.trimAscii.toString.toNat?)).join
      let some count := count | throw s!"the lock's header `{line}` gives no count"
      if name == "[axioms]" then
        axioms := { axioms with count }
        table := some "axioms"
      else if name == "[vocabulary]" then
        vocabulary := { vocabulary with count }
        table := some "vocabulary"
      else throw s!"the lock has a table `{name}`, not [axioms] or [vocabulary]"
      continue
    let parts := line.splitOn "\" = \""
    unless line.startsWith "\"" && line.endsWith "\"" && parts.length ≥ 2 do
      throw s!"the lock has a line that is not an entry: `{line}`"
    let key ← Json.parse (parts[0]! ++ "\"") >>= (·.getStr?)
    let value ← Json.parse ("\"" ++ "\" = \"".intercalate parts.tail!) >>= (·.getStr?)
    match table with
    | some "axioms" => axioms := { axioms with entries := axioms.entries.push (key, value) }
    | some "vocabulary" =>
      vocabulary := { vocabulary with entries := vocabulary.entries.push (key, value) }
    | _ => throw s!"the lock has an entry before its first table: `{line}`"
  for (name, t) in [("[axioms]", axioms), ("[vocabulary]", vocabulary)] do
    unless t.count == t.entries.size do
      throw s!"the lock's {name} says {t.count} entries and has {t.entries.size}"
  return { axioms, vocabulary }

/-- The options `Certificate/Facts.lean` prints a statement with for the lock: every name
written out in full, and nothing behind notation. -/
def lockOptions (o : Options) : Options :=
  o |>.setBool `pp.notation false |>.setBool `pp.fullNames true
    |>.setBool `pp.funBinderTypes true |>.setBool `pp.fieldNotation false
    |>.setBool `pp.structureInstances false |>.set `format.width (100000 : Nat)

/-- `s` on one line, as `Certificate/Facts.lean` writes a statement: every run of white
space made one space, and the ends trimmed. -/
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

/-- `e` as the lock prints it. -/
def lockPrint (e : Expr) : MetaM String :=
  withTheReader Core.Context (fun c => { c with currNamespace := .anonymous, openDecls := [] }) <|
    withOptions lockOptions do return oneLine ((← ppExpr e).pretty 100000)

/-- What kind of declaration a word is, in the lock's terms. -/
def lockKind (env : Environment) (ci : ConstantInfo) : String :=
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

/-- A word's entry in the lock's `[vocabulary]`: its kind, its type, and a definition's or an
instance's value. -/
def lockWord (ci : ConstantInfo) : MetaM String := do
  let kind := lockKind (← getEnv) ci
  let type ← lockPrint ci.type
  let value ← match ci.value? (allowOpaque := true) with
    | some v =>
      if kind == "def" || kind == "instance" then pure s!" := {← lockPrint v}" else pure ""
    | none => pure ""
  return s!"{kind} : {type}{value}"

/-! ## The vocabulary: what each word of the library becomes -/

/-- The seventeen opaque words of the library, each with the field of `Model.Signature` that
stands for it. -/
def fields : Array (Name × Name) := #[
  (`Elements.Point, `Model.Signature.Point),
  (`Elements.Line, `Model.Signature.Line),
  (`Elements.Circle, `Model.Signature.Circle),
  (`Elements.OnLine, `Model.Signature.OnLine),
  (`Elements.SameSide, `Model.Signature.SameSide),
  (`Elements.Between, `Model.Signature.Between),
  (`Elements.OnCircle, `Model.Signature.OnCircle),
  (`Elements.InsideCircle, `Model.Signature.InsideCircle),
  (`Elements.Centre, `Model.Signature.Centre),
  (`Elements.MagnitudeImpl, `Model.Signature.MagnitudeImpl),
  (`Elements.Magnitude.zero, `Model.Signature.zero),
  (`Elements.Magnitude.add, `Model.Signature.add),
  (`Elements.Magnitude.lt, `Model.Signature.lt),
  (`Elements.len, `Model.Signature.len),
  (`Elements.ang, `Model.Signature.ang),
  (`Elements.area, `Model.Signature.area),
  (`Elements.rightAngle, `Model.Signature.rightAngle)]

/-- `Elements.Kind` and its constructors, with the model's copies. -/
def kinds : Array (Name × Name) := #[
  (`Elements.Kind, `Model.Kind),
  (`Elements.Kind.length, `Model.Kind.length),
  (`Elements.Kind.angle, `Model.Kind.angle),
  (`Elements.Kind.area, `Model.Kind.area)]

/-- The defined words that `Model/Signature.lean` writes by hand: the carriers of the
magnitudes and their instances, which the signature's own fields need to be used at all. The
generator checks each against the library's and does not write it. -/
def signatureWords : Array (Name × Name) := #[
  (`Elements.Magnitude, `Model.Signature.Magnitude),
  (`Elements.Length, `Model.Signature.Length),
  (`Elements.Angle, `Model.Signature.Angle),
  (`Elements.Area, `Model.Signature.Area),
  (`Elements.instAddMagnitude, `Model.Signature.instAddMagnitude),
  (`Elements.instOfNatMagnitudeOfNatNat, `Model.Signature.instOfNatMagnitude),
  (`Elements.instLTMagnitude, `Model.Signature.instLTMagnitude),
  (`Elements.instLEMagnitude, `Model.Signature.instLEMagnitude)]

/-- The universe levels at which the laws use a word of the library: none, for every word but
`Elements.MagnitudeImpl`. Lean declares that one at every universe, since it generalizes the
level of `NonemptyType` in its type, and `Elements.Magnitude`, a `Type`, uses it at universe 0.
The model's field is that one, at universe 0. -/
def levelsOf (lib : Name) : List Level :=
  if lib == `Elements.MagnitudeImpl then [Level.zero] else []

/-- The library's rules that hold only in the Euclidean plane: Postulate 5, and any rule
declared in `Elements.Tacit.Euclidean` (FORMALIZATION, section 7). They stand apart, in
`Laws` and not in `Neutral`, so that a hyperbolic plane can satisfy the rest and fail them. -/
def isEuclidean (n : Name) : Bool :=
  n == `Elements.Postulate5 ||
    ((`Elements.Tacit.Euclidean).isPrefixOf n && n != `Elements.Tacit.Euclidean)

/-- What a constant of the library becomes: a constant of the model, which takes the
signature `S` as its first argument when it is a field or a word over `S`, and not when it
is `Model.Kind`, one of its constructors or a shared pure declaration. -/
structure Target where
  name : Name
  overS : Bool
  /-- The universe levels at which the laws use the library's word (`levelsOf`). -/
  levels : List Level := []
  /-- A shared pure declaration: identity translation at every universe level. -/
  identity : Bool := false
  deriving Inhabited

/-- A non-empty module name whose string components each denote one relative path
component. `Lean.modToFilePath` joins components with `FilePath.join`, so an absolute
component discards the preceding path and `..` can leave the package. Numeric components
are invalid imports. Reject separators and NUL, and also colons and trailing dots or
spaces: Windows gives those drive, stream or normalisation meanings. Harmless escaped
identifiers such as `areas-p5` remain valid. This checks names, not symlinks or provenance. -/
def isCanonicalModuleName : Name → Bool
  | .str p s =>
    !s.isEmpty && s != "." && s != ".." &&
    !(s.contains '/' || s.contains '\\' || s.contains ':' || s.contains '\x00') &&
    !s.endsWith "." && !s.endsWith " " &&
    (p.isAnonymous || isCanonicalModuleName p)
  | _ => false

/-- The module that declares `c`. This is the recorded name, without a trust decision. -/
def moduleOf? (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- `c` is a word of the project: declared in a module of `Elements`. -/
def isProject (env : Environment) (c : Name) : Bool :=
  match moduleOf? env c with
  | some m => isCanonicalModuleName m && (`Elements).isPrefixOf m
  | none => false

/-- The core boundary also checks the imported module's package metadata. The pinned
Lean 4.35 toolchain's Init modules have no package identifier; a named package is refused.
Lean retains no resolved `.olean` path, so an unlabelled replacement cannot be distinguished
here from a toolchain file. The configured toolchain and search path remain assumptions. -/
def isLeanCoreModule (m : Name) (package? : Option PkgId) : Bool :=
  isCanonicalModuleName m && m.getRoot == `Init && package?.isNone

/-- Decide core membership from the constant's declaring module. -/
def isLeanCore (env : Environment) (c : Name) : Bool :=
  (env.getModuleIdxFor? c).any fun i =>
    isLeanCoreModule env.header.moduleNames[i.toNat]! (env.getModulePackageByIdx? i)

/-- The complete shared-definition boundary, decided by declaring module, not namespace. -/
def pureModules : Array Name := #[
  `Elements.Foundations.Superposition.Syntax,
  `Elements.Foundations.Superposition.Semantics,
  `Elements.Foundations.Superposition.Soundness,
  `Elements.Foundations.Superposition.Restriction]

/-- Sharing by declaring module, with a supplied boundary for regression fixtures. -/
def isSharedModuleWith (modules : Array Name) (m : Name) : Bool :=
  isCanonicalModuleName m && modules.contains m

/-- Sharing uses the same module decision for actual declarations. -/
def isSharedWith (modules : Array Name) (env : Environment) (c : Name) : Bool :=
  (moduleOf? env c).any (isSharedModuleWith modules)

/-- A constant declared in one of the four approved pure modules. -/
def isShared (env : Environment) (c : Name) : Bool :=
  isSharedWith pureModules env c

/-- Check the transitive types and values of the shared declarations, including theorem
proofs, opaque values, constructors and recursor rules. Only the four pure modules and
`Init` are admissible, and only Lean's three logical axioms. A visited set handles mutual
inductives and recursive definitions without leaving any dependency unchecked. -/
def checkPureWith (env : Environment) (find? : Name → Option ConstantInfo)
    (roots : Array Name) (modules : Array Name := pureModules) : Except String Unit := do
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c == `sorryAx then throw "shared calculus reaches `sorryAx`"
    unless isSharedWith modules env c || isLeanCore env c do
      throw s!"shared calculus reaches `{c}`, outside the four pure modules and `Init`"
    let some ci := find? c | throw s!"shared calculus reaches undeclared `{c}`"
    if ci.isAxiom && !([`propext, `Classical.choice, `Quot.sound].contains c) then
      throw s!"shared calculus reaches unapproved axiom `{c}`"
    todo := todo ++ ci.type.getUsedConstants
    if let some value := ci.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
    match ci with
    | .inductInfo v => todo := todo ++ v.ctors.toArray
    | .recInfo v =>
      for rule in v.rules do todo := todo ++ rule.rhs.getUsedConstants
    | _ => pure ()

/-- Audit the actual declarations. `checkPureWith` also accepts an isolated declaration
lookup for regression fixtures; production always uses the environment's own lookup. -/
def checkPure (env : Environment) (roots : Array Name) : Except String Unit :=
  checkPureWith env env.find? roots

/-- Collect and audit every declaration in the supplied modules, including words no law
reaches. The supplied lookup permits isolated regression data without changing Lean's
environment. Production supplies `pureModules` and the environment's own lookup. -/
def checkPureModulesWith (modules : Array Name) (env : Environment)
    (find? : Name → Option ConstantInfo) : Except String Unit := do
  for m in modules do
    unless isCanonicalModuleName m do throw s!"non-canonical shared module `{m}`"
  let mut roots := #[]
  for i in [:env.header.moduleNames.size] do
    if modules.contains env.header.moduleNames[i]! then
      roots := roots ++ env.header.moduleData[i]!.constNames
  checkPureWith env find? roots modules

/-- Audit every declaration in every imported pure module, even if no law reaches it. -/
def checkPureModules (env : Environment) : Except String Unit :=
  checkPureModulesWith pureModules env env.find?

/-- The library's name for a word or a law, without `Elements.`: the lock's key. -/
def lockKey (n : Name) : String := (n.replacePrefix `Elements .anonymous).toString

/-! ## Translating, and translating back -/

/-- `e`, translated: every constant of the project replaced by its target in `vocab`, with
the signature `S` put in where the target is over `S`. Lean's own constants stay. A constant
of the project that `vocab` does not translate, or any constant that is neither the
project's nor Lean's own, is an error. -/
def translate (env : Environment) (vocab : NameMap Target) (S : Expr) (what : String)
    (e : Expr) : Except String Expr := do
  let mut bad : Array String := #[]
  for c in e.getUsedConstants do
    if vocab.contains c then continue
    if isProject env c then
      bad := bad.push s!"`{c}` is a word of the project with no translation: neither a field \
        of the signature, nor `Kind`, nor a defined word the generator translates"
    else unless isLeanCore env c do
      bad := bad.push s!"`{c}` is neither Lean's own (from `Init`) nor a word of the project"
  let atLevel := e.find? fun
    | .const c ls => match vocab.find? c with
      | some t => !t.identity && ls != t.levels
      | none => false
    | _ => false
  if let some (.const c ls) := atLevel then
    bad := bad.push s!"`{c}` is used at the universe levels {ls}, not those the model's word has"
  unless bad.isEmpty do throw s!"{what}: {"; ".intercalate bad.toList}"
  return e.replace fun
    | .const c ls => (vocab.find? c).map fun t =>
        if t.identity then .const t.name ls
        else if t.overS then mkApp (.const t.name []) S else .const t.name []
    | _ => none

/-- `e`, translated back: each target applied to the signature `S` (or, for `Model.Kind`
and shared declarations, on its own) replaced by the library's constant. It is an error if
`S` or a constant of the model is left over: the signature used other than through one of
its words. -/
def untranslate (inverse : NameMap Target) (S : Expr) (what : String) (e : Expr) :
    Except String Expr := do
  let e' := e.replace fun
    | .app (.const c []) s =>
      if s == S then (inverse.find? c).bind fun t =>
        if t.overS then some (.const t.name t.levels) else none
      else none
    | .const c ls => (inverse.find? c).bind fun t =>
        if t.identity then some (.const t.name ls)
        else if t.overS || !ls.isEmpty then none else some (.const t.name t.levels)
    | _ => none
  if e'.containsFVar S.fvarId! then
    throw s!"{what}: the signature is used other than through one of its words"
  for c in e'.getUsedConstants do
    if (`Model).isPrefixOf c && !(inverse.find? c).any (·.identity) then
      throw s!"{what}: `{c}` is a word of the model that does not translate back to the \
        library's"
  return e'

/-- The carrier of the magnitudes of kind `k`, `(Elements.MagnitudeImpl k).type`. -/
def carrierOf (k : Expr) : Expr :=
  mkApp (.const ``NonemptyType.type [Level.zero])
    (mkApp (.const `Elements.MagnitudeImpl (levelsOf `Elements.MagnitudeImpl)) k)

/-- `e` with the four carrier words of the magnitudes unfolded (`Elements.Magnitude`,
`Length`, `Angle` and `Area`), and with no metadata. The fields of `Model.Signature` write the
carriers out (`(S.MagnitudeImpl .length).type` for `S.Length`), since a structure's fields
cannot use a word defined from those fields, so a law whose sides are lengths comes back from
Lean with the carrier written out where the library has `Length`. The round trip by syntax
unfolds these four words, and only these, on both sides before it compares. -/
partial def unfoldCarriers (e : Expr) : Expr :=
  e.replace fun
    | .const `Elements.Length [] => some (carrierOf (.const `Elements.Kind.length []))
    | .const `Elements.Angle [] => some (carrierOf (.const `Elements.Kind.angle []))
    | .const `Elements.Area [] => some (carrierOf (.const `Elements.Kind.area []))
    | .app (.const `Elements.Magnitude []) k => some (carrierOf (unfoldCarriers k))
    | .mdata _ b => some (unfoldCarriers b)
    | _ => none

/-- A short description of `e` for a message, its bound variables named from `names`. -/
partial def describe (e : Expr) (names : List Name) : String :=
  match e with
  | .bvar i => (names[i]?.map toString).getD s!"#{i}"
  | .fvar _ => "a variable"
  | .mvar _ => "a hole"
  | .sort .zero => "Prop"
  | .sort _ => "a sort"
  | .const c _ => c.toString
  | .lit (.natVal n) => toString n
  | .lit (.strVal t) => t.quote
  | .app .. => s!"{describe e.getAppFn names} …"
  | .lam n .. => s!"fun {n} => …"
  | .forallE n t b _ => if b.hasLooseBVar 0 then s!"∀ {n}, …" else s!"{describe t names} → …"
  | .letE n .. => s!"let {n} := …"
  | .mdata _ e => describe e names
  | .proj s i _ => s!"the projection {s}.{i}"

/-- How a binder takes its argument, in words. -/
def binderKind : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict implicit"
  | .instImplicit => "an instance argument"

/-- Where `a` first differs from `b`, if it does, in words, `b` being what `theirs` has: the
same expressions, constant for constant and binder for binder. A binder's kind (explicit,
implicit, instance) and its type always count; its name counts wherever the bound variable is
used, since an unused hypothesis's name is no part of what a law says (Lean prints it as an
arrow). Metadata does not count. `names` names the variables bound so far, the last first. -/
partial def firstDifference (theirs : String) (a b : Expr) (names : List Name := []) :
    Option String :=
  let here (x y : Expr) : Option String :=
    some s!"`{describe x names}` where {theirs} has `{describe y names}`"
  match a, b with
  | .mdata _ a, b => firstDifference theirs a b names
  | a, .mdata _ b => firstDifference theirs a b names
  | .bvar i, .bvar j => if i == j then none else here a b
  | .fvar x, .fvar y => if x == y then none else here a b
  | .sort u, .sort v => if u == v then none else here a b
  | .const c us, .const d vs =>
    if c != d then here a b
    else if us != vs then some s!"`{c}` at the universe levels {us} where {theirs} has {vs}"
    else none
  | .lit l, .lit m => if l == m then none else here a b
  | .app f x, .app g y =>
    (firstDifference theirs f g names).orElse fun _ => firstDifference theirs x y names
  | .lam n t x i, .lam m u y j => binder n t x i m u y j
  | .forallE n t x i, .forallE m u y j => binder n t x i m u y j
  | .letE n t v x _, .letE m u w y _ =>
    if n != m then some s!"the variable `{n}` where {theirs} has `{m}`" else
    (firstDifference theirs t u names).orElse fun _ =>
      (firstDifference theirs v w names).orElse fun _ => firstDifference theirs x y (n :: names)
  | .proj s i x, .proj t j y =>
    if s == t && i == j then firstDifference theirs x y names else here a b
  | a, b => here a b
where
  binder (n : Name) (t x : Expr) (i : BinderInfo) (m : Name) (u y : Expr) (j : BinderInfo) :
      Option String :=
    if i != j then
      some s!"the binder `{n}` is {binderKind i} where {theirs}'s `{m}` is {binderKind j}"
    else if x.hasLooseBVar 0 && n != m then
      some s!"the variable `{n}` where {theirs} has `{m}`"
    else (firstDifference theirs t u names).orElse fun _ => firstDifference theirs x y (n :: names)

/-! ## Reading the library -/

/-- The axioms the library declares in the modules of `Elements.Foundations`, in the lock's
order. -/
def foundationAxioms (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for i in [0:env.header.moduleNames.size] do
    unless isCanonicalModuleName env.header.moduleNames[i]! do continue
    unless (`Elements.Foundations).isPrefixOf env.header.moduleNames[i]! do continue
    for c in env.header.moduleData[i]!.constNames do
      if let some (.axiomInfo _) := env.find? c then out := out.push c
  return out.qsort (lockKey · < lockKey ·)

/-- The modules of `Elements.Foundations`, one for each file under `Elements/Foundations/`
in the repository at `root`. -/
def foundationModules (root : System.FilePath) : IO (Array Name) := do
  let files ← System.FilePath.walkDir (root / "Elements" / "Foundations")
  let mut mods : Array Name := #[]
  for f in files do
    unless f.extension == some "lean" do continue
    let comps := (f.withExtension "").components.drop root.components.length
    mods := mods.push (comps.foldl Name.mkStr .anonymous)
  return mods.qsort (·.toString < ·.toString)

/-- The words of the project the laws reach: every definition, instance, opaque word,
inductive type and constructor that the statement of a law reaches, through words' types,
definitions' and instances' values and inductive types' constructors, as
`Certificate/Facts.lean` walks the vocabulary. In the lock's order. -/
def reachedWords (env : Environment) (laws : Array Name) : Array Name := Id.run do
  let mut todo : Array Name := #[]
  for a in laws do
    if let some ci := env.find? a then todo := todo ++ ci.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut words : Array Name := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    unless isProject env c do continue
    let some ci := env.find? c | continue
    if ci.isAxiom then continue
    words := words.push c
    todo := todo ++ ci.type.getUsedConstants
    match ci with
    | .defnInfo v => todo := todo ++ v.value.getUsedConstants
    | .inductInfo v => todo := todo ++ v.ctors.toArray
    | _ => pure ()
  return words.qsort (lockKey · < lockKey ·)

/-- The defined words in an order in which each comes after the words its type and value
use: the lock's order, with a word moved after those it needs. -/
def dependencyOrder (env : Environment) (words : Array Name) : Array Name := Id.run do
  let set := NameSet.ofList words.toList
  let mut done : NameSet := {}
  let mut out : Array Name := #[]
  let mut left := words
  while !left.isEmpty do
    let mut next : Array Name := #[]
    let mut progress := false
    for w in left do
      let some ci := env.find? w | continue
      let uses := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map
        (·.getUsedConstants) |>.getD #[])
      if uses.all fun u => u == w || !set.contains u || done.contains u then
        out := out.push w
        done := done.insert w
        progress := true
      else next := next.push w
    if !progress then return out ++ next
    left := next
  return out

/-! ## The translation of the whole vocabulary -/

/-- Everything the generator derives from the library before it prints anything. -/
structure Plan where
  /-- The laws: the library's axioms, in the lock's order. -/
  laws : Array Name
  /-- The words of the lock's vocabulary the laws reach, in the lock's order. -/
  reached : Array Name
  /-- The defined words the generator writes, in dependency order. -/
  generated : Array Name
  /-- What each word of the library becomes. -/
  vocab : NameMap Target
  /-- The inverse: what each word of the model becomes in the library. -/
  inverse : NameMap Target
  deriving Inhabited

/-- The model's name for a law: `Model.Law.Postulate1` for `Elements.Postulate1`. -/
def lawName (n : Name) : Name := n.replacePrefix `Elements `Model.Law

/-- The field of `Laws` for a law: the last part of its name, `circles_meet` for
`Elements.Tacit.circles_meet`. -/
def fieldName (n : Name) : Name := .mkSimple n.getString!

/-- The model's name for a word the generator writes: `Model.Signature.Collinear` for
`Elements.Collinear`. -/
def generatedName (n : Name) : Name := n.replacePrefix `Elements `Model.Signature

/-- Construct the plan with an explicit sharing boundary and additional reached words for
fixtures. Production uses the four pure modules and only the words the laws reach. -/
def planWith (modules : Array Name) (env : Environment) (extraWords : Array Name := #[]) :
    Except String Plan := do
  checkPureModulesWith modules env env.find?
  let laws := foundationAxioms env
  let reached := reachedWords env laws ++ extraWords
  let mut vocab : NameMap Target := {}
  for (lib, field) in fields do
    vocab := vocab.insert lib { name := field, overS := true, levels := levelsOf lib }
  for (lib, k) in kinds do vocab := vocab.insert lib { name := k, overS := false }
  for (lib, w) in signatureWords do vocab := vocab.insert lib { name := w, overS := true }
  let mut generated : Array Name := #[]
  let mut bad : Array String := #[]
  for w in reached do
    if vocab.contains w then continue
    if isSharedWith modules env w then
      vocab := vocab.insert w { name := w, overS := false, identity := true }
      continue
    match env.find? w with
    | none => bad := bad.push s!"`{w}` is not declared"
    | some (.defnInfo _) =>
      if Meta.isInstanceCore env w then
        bad := bad.push s!"`{w}` is an instance, and the generator writes none: the \
          instances the laws use are written by hand in `Model/Signature.lean`"
      else if !(w.getPrefix == `Elements) then
        bad := bad.push s!"`{w}` is not in the namespace `Elements` itself, so it would have \
          no name over the signature"
      else
        generated := generated.push w
        vocab := vocab.insert w { name := generatedName w, overS := true }
    | some (.opaqueInfo _) =>
      bad := bad.push s!"`{w}` is an opaque word with no field in the signature"
    | some ci => bad := bad.push s!"`{w}` is declared as `{lockKind env ci}` in the project, \
        and the generator translates no such word"
  for (lib, _) in fields ++ kinds ++ signatureWords do
    unless env.contains lib do bad := bad.push s!"the library has no `{lib}`"
  unless bad.isEmpty do throw ("; ".intercalate bad.toList)
  let mut inverse : NameMap Target := {}
  for (lib, t) in vocab do
    inverse := inverse.insert t.name {
      name := lib, overS := t.overS, levels := t.levels, identity := t.identity }
  return { laws, reached, generated := dependencyOrder env generated, vocab, inverse }

/-- The production plan, with the four approved modules as the shared boundary. -/
def plan (env : Environment) : Except String Plan :=
  planWith pureModules env

/-! ## Printing Lean a reader can read -/

/-- The options the generated Lean is printed with: Lean's notation, the signature's words
as `S.Point`, the types of the variables of `∃`, nothing cut short, and lines of 100
characters. -/
def readable (o : Options) : Options :=
  o |>.setBool `pp.notation true |>.setBool `pp.fullNames false
    |>.setBool `pp.funBinderTypes true |>.setBool `pp.piBinderTypes true
    |>.setBool `pp.fieldNotation true |>.setBool `pp.fieldNotation.generalized true
    |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (1000000 : Nat)
    |>.setBool `pp.unicode.fun false |>.set `format.width (100 : Nat)

/-- `e` printed as it reads in the namespace `ns` of the generated file. -/
def ppIn (ns : Name) (e : Expr) : MetaM Format :=
  withTheReader Core.Context (fun c => { c with currNamespace := ns, openDecls := [] }) <|
    withOptions readable (ppExpr e)

/-- The binders `xs` as a declaration states them: consecutive binders of one kind and one
type grouped, `(A B : S.Point)`. -/
def ppBinders (ns : Name) (xs : Array Expr) : MetaM String := do
  let mut groups : Array (BinderInfo × Expr × Array Name) := #[]
  for x in xs do
    let d ← x.fvarId!.getDecl
    match groups.back? with
    | some (bi, t, names) =>
      if bi == d.binderInfo && t == d.type then
        groups := groups.pop.push (bi, t, names.push d.userName)
      else groups := groups.push (d.binderInfo, d.type, #[d.userName])
    | none => groups := groups.push (d.binderInfo, d.type, #[d.userName])
  let parts ← groups.mapM fun (bi, t, names) => do
    let ty := (← ppIn ns t).pretty 100000
    let ns := " ".intercalate (names.toList.map toString)
    pure <| match bi with
      | .implicit => s!"\{{ns} : {ty}}"
      | .strictImplicit => "⦃" ++ ns ++ " : " ++ ty ++ "⦄"
      | .instImplicit => "[" ++ ns ++ " : " ++ ty ++ "]"
      | .default => "(" ++ ns ++ " : " ++ ty ++ ")"
  return " ".intercalate parts.toList

/-- Printed Lean that would not read back as what was printed: a term cut short, a name Lean
made inaccessible, a `sorry`. -/
def unreadable (s : String) : Bool :=
  (s.splitOn "⋯").length > 1 || (s.splitOn "✝").length > 1 || (s.splitOn "sorry").length > 1

/-! ### Laying a statement out

Lean's printer lays a long implication out as a staircase, each `→` a step further in. A law
reads better as its hypotheses one after another, filling the line, as `Model/Hand.lean`
writes them. So a statement is cut along its right spine (binders, hypotheses, the parts of a
conjunction or a disjunction, the variables of `∃`), each piece is printed by Lean, and the
pieces fill lines of 100 characters. Each piece is parenthesized as its place needs, by how
tightly its notation binds; `Check/RoundTrip.lean` checks that every law reads back as the
expression the generator printed. -/

/-- How tightly the notation `e` is printed in binds, for parenthesizing: 0 for a binder (`∀`,
`∃`, `fun`), which reaches to the end; 20 for `↔`, 25 for `→`, 30 for `∨`, 35 for `∧`, 40 for
`¬`, 50 for a relation (`=`, `≠`, `<`, `≤`, `∈`), 65 for `+`, and 1024 for an application of a
word, or a name. -/
partial def tightness (e : Expr) : Nat :=
  match e with
  | .mdata _ e => tightness e
  | .forallE _ _ b bi => if b.hasLooseBVar 0 || bi != .default then 0 else 25
  | .lam .. | .letE .. => 0
  | _ =>
    let n := e.getAppNumArgs
    match e.getAppFn with
    | .const ``Exists _ => if n == 2 then 0 else 1024
    | .const ``Iff _ => if n == 2 then 20 else 1024
    | .const ``Or _ => if n == 2 then 30 else 1024
    | .const ``And _ => if n == 2 then 35 else 1024
    | .const ``Not _ => if n == 1 then 40 else 1024
    | .const ``Eq _ | .const ``Ne _ => if n == 3 then 50 else 1024
    | .const ``LT.lt _ | .const ``LE.le _ | .const ``GT.gt _ | .const ``GE.ge _ =>
      if n == 4 then 50 else 1024
    | .const ``Membership.mem _ => if n == 5 then 50 else 1024
    | .const ``HAdd.hAdd _ => if n == 6 then 65 else 1024
    | _ => 1024

/-- `e` printed on one line, in parentheses if it binds no more tightly than `bound`. -/
def atom (ns : Name) (e : Expr) (bound : Nat) : MetaM String := do
  let s := (← ppIn ns e).pretty 100000
  return if tightness e ≤ bound then "(" ++ s ++ ")" else s

/-- The two sides of `e` if it is `a ∧ b` (or `a ∨ b`, for `Or`). -/
def binary? (c : Name) (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity c 2 then some (e.appFn!.appArg!, e.appArg!) else none

mutual

/-- The statement `e`, cut along its right spine into pieces, each ending with what joins it
to the next (`,` after binders, `→`, `∧`, `∨`). -/
partial def pieces (ns : Name) (e : Expr) : MetaM (Array String) := do
  match e with
  | .mdata _ e => pieces ns e
  | .forallE n t b bi =>
    if b.hasLooseBVar 0 || bi != .default then binderPieces ns e #[]
    else
      let h ← atom ns t 25
      withLocalDecl n bi t fun x => return #[h ++ " →"] ++ (← pieces ns (b.instantiate1 x))
  | _ =>
    if let some (ty, .lam n t b .default) := exists? e then
      existsPieces ns ty n t b #[]
    else if let some (a, b) := binary? ``And e then chain ns ``And "∧" 35 a b
    else if let some (a, b) := binary? ``Or e then chain ns ``Or "∨" 30 a b
    else return #[← atom ns e 0]

/-- The binders at the head of `e` that a `∀` prints (those its body uses, and any that is not
explicit), as one piece `∀ {A B : S.Point} {L : S.Line},`, then the rest. -/
partial def binderPieces (ns : Name) (e : Expr) (xs : Array Expr) : MetaM (Array String) := do
  match e with
  | .forallE n t b bi =>
    if b.hasLooseBVar 0 || bi != .default then
      withLocalDecl n bi t fun x => binderPieces ns (b.instantiate1 x) (xs.push x)
    else finish e
  | _ => finish e
where
  finish (rest : Expr) : MetaM (Array String) := do
    return #["∀ " ++ (← ppBinders ns xs) ++ ","] ++ (← pieces ns rest)

/-- The variables of a run of `∃` over one type, as one piece `∃ B' C' : S.Point,`, then the
rest. -/
partial def existsPieces (ns : Name) (ty : Expr) (n : Name) (t b : Expr) (names : Array Name) :
    MetaM (Array String) := do
  withLocalDecl n .default t fun x => do
    let body := b.instantiate1 x
    let names := names.push n
    if let some (ty', .lam n' t' b' .default) := exists? body then
      if ty' == ty && t' == t then
        return ← existsPieces ns ty n' t' b' names
    let tyText := (← ppIn ns t).pretty 100000
    let vars := " ".intercalate (names.toList.map toString)
    return #["∃ " ++ vars ++ " : " ++ tyText ++ ","] ++ (← pieces ns body)

/-- A conjunction (or a disjunction) `a ∧ b ∧ …`, cut at each `∧`: every part but the last
printed as a whole, the last cut further if it is a binder, which reaches to the end. -/
partial def chain (ns : Name) (c : Name) (op : String) (bound : Nat) (a b : Expr) :
    MetaM (Array String) := do
  let first := (← atom ns a bound) ++ " " ++ op
  if let some (a', b') := binary? c b then
    return #[first] ++ (← chain ns c op bound a' b')
  if tightness b == 0 then return #[first] ++ (← pieces ns b)
  return #[first, ← atom ns b (bound - 1)]

/-- The type and the predicate of `e` if it is `∃ x, p`. -/
partial def exists? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Exists 2 then some (e.appFn!.appArg!, e.appArg!) else none

end

/-- The pieces filling lines of 100 characters, the first line indented by `first` spaces
and the others by `rest`. -/
def fill (ps : Array String) (first rest : Nat) : String := Id.run do
  let mut out := "".pushn ' ' first
  let mut col := first
  let mut start := true
  for p in ps do
    if start then
      out := out ++ p
      col := col + p.length
      start := false
    else if col + 1 + p.length ≤ 100 then
      out := out ++ " " ++ p
      col := col + 1 + p.length
    else
      out := out ++ "\n" ++ "".pushn ' ' rest ++ p
      col := rest + p.length
  return out

/-- The statement `e` as the body of a declaration: on the line after `:=`, indented by two,
its continuation lines by four. -/
def statement (ns : Name) (e : Expr) : MetaM String := do
  return fill (← pieces ns e) 2 4

/-! ## What the generator writes -/

/-- The three files the generator writes. -/
structure Output where
  laws : String
  checks : String
  assembly : String

/-- The fields of `Laws` for the laws, in the lock's order, with whether each stands apart
as Euclidean. -/
def lawFields (laws : Array Name) : Array (Name × Name × Bool) :=
  laws.map fun n => (n, fieldName n, isEuclidean n)

/-- The lines of the header table of `Model/Laws.lean`: each word of the vocabulary the laws
reach, with what it becomes. -/
def vocabularyTable (p : Plan) : Array String := Id.run do
  let mut rows : Array String := #[]
  let byS := fields.map (·.1)
  let byKind := kinds.map (·.1)
  let bySignature := signatureWords.map (·.1)
  for w in p.reached do
    let some t := p.vocab.find? w | continue
    let short := (t.name.replacePrefix `Model.Signature .anonymous).toString
    let here :=
      if t.identity then s!"`{w}`, shared unchanged from its pure module"
      else if byS.contains w then s!"`S.{short}`, a field of `Signature`"
      else if byKind.contains w then s!"`{t.name.replacePrefix `Model .anonymous}`"
      else if bySignature.contains w then s!"`S.{short}`, in `Model/Signature.lean`"
      else s!"`S.{short}`, below"
    rows := rows.push s!"| `{w}` | {here} |"
  return rows

/-- Run `k` with the signature `S` as a local variable named `S`. -/
def withSignature (k : Expr → MetaM α) : MetaM α :=
  withLocalDeclD `S (.const `Model.Signature []) k

/-- Shared imports in boundary order, once per reached module. An empty list contributes
no newline. Production supplies `pureModules`; fixtures can exercise a non-empty header
before those modules exist. -/
def sharedImportHeaderWith (modules : Array Name) (env : Environment)
    (reached : Array Name) : String :=
  let imports := modules.filter fun m =>
    isCanonicalModuleName m && reached.any fun w => moduleOf? env w == some m
  String.join (imports.toList.map (s!"\npublic import {·}"))

/-- The text of `Model/Laws.lean`. It adds the generated words, and the laws as definitions,
to the environment as it goes, so that each prints with the words before it (the caller runs
it inside `withoutModifyingEnv`). -/
def lawsText (p : Plan) (hash : String) : MetaM String := withSignature fun S => do
  let env ← getEnv
  let liftE {α} (x : Except String α) : MetaM α := match x with
    | .ok a => pure a
    | .error e => throwError e
  -- The words.
  let mut words : Array String := #[]
  for w in p.generated do
    let some ci := env.find? w | throwError "`{w}` vanished"
    let some value := ci.value? | throwError "`{w}` has no value"
    let type ← liftE <| translate env p.vocab S s!"the word `{w}`" ci.type
    let value ← liftE <| translate env p.vocab S s!"the word `{w}`" value
    let name := generatedName w
    let text ← lambdaTelescope value fun xs body => do
      let result ← instantiateForall type xs
      let binders ← ppBinders `Model.Signature xs
      let head := if xs.isEmpty then "" else " " ++ binders
      let keyword := match getReducibilityStatusCore env w with
        | .reducible => "abbrev"
        | .irreducible => "@[irreducible] def"
        | _ => "def"
      let nc := if isNoncomputable env w then "noncomputable " else ""
      let resultText := (← ppIn `Model.Signature result).pretty 100000
      pure s!"/-- `{w}`, translated. -/\n{nc}{keyword} {name.getString!}{head} : {resultText} :=\n\
        {← statement `Model.Signature body}"
    addDecl <| .defnDecl {
      name, levelParams := [], type := ← mkForallFVars #[S] type,
      value := ← mkLambdaFVars #[S] value, hints := .regular 0, safety := .safe }
    words := words.push text
  -- The laws, in blocks by namespace.
  let mut blocks : Array (Name × Array String) := #[]
  for n in p.laws do
    let some ci := env.find? n | throwError "`{n}` vanished"
    let type ← liftE <| translate env p.vocab S s!"the law `{lockKey n}`" ci.type
    let name := lawName n
    let ns := name.getPrefix
    let text := s!"/-- `{n}`, translated. -/\ndef {name.getString!} : Prop :=\n\
      {← statement ns type}"
    addDecl <| .defnDecl {
      name, levelParams := [], type := ← mkArrow (.const `Model.Signature []) (.sort 0),
      value := ← mkLambdaFVars #[S] type, hints := .regular 0, safety := .safe }
    blocks := match blocks.back? with
      | some (m, texts) => if m == ns then blocks.pop.push (m, texts.push text)
        else blocks.push (ns, #[text])
      | none => blocks.push (ns, #[text])
  let all := "\n".intercalate (words.toList ++ blocks.toList.flatMap (·.2.toList))
  if unreadable all then throwError "a generated declaration would not read back: {all}"
  -- The structures.
  let fs := lawFields p.laws
  let neutral := fs.filter (!·.2.2)
  let euclidean := fs.filter (·.2.2)
  let field (n : Name × Name × Bool) : String :=
    s!"  {n.2.1} : {(lawName n.1).replacePrefix `Model .anonymous} S"
  let sharedHeader := sharedImportHeaderWith pureModules env p.reached
  let header := s!"module

public import Model.Signature{sharedHeader}

/-!
# The laws

**This file is generated: do not edit it.** `Check/Generator.lean` writes it from the axioms
declared in `Elements/Foundations/`, as Lean elaborated them, and `lake build` fails while it
differs from what the generator writes. To write it again, run `lake lean Check/Write.lean` in
`model/`. The [README](../README.md) says how the laws are translated and checked.

It was written from the lock, `Certificate/axioms.lock`, whose sha256 is
`{hash}`,
the hash that `model/lock.sha256` holds. The lock has {p.laws.size} laws, and they reach \
{p.reached.size} words of its
vocabulary. Each law here is the library's axiom with the words of a signature `S` put for the
library's words:

| The library's word | Here |
|---|---|
{"\n".intercalate (vocabularyTable p).toList}

Each law is a definition named as in the lock: `Law.Postulate1 S` for `Postulate1`. A model of
the laws is a signature `S` with `Laws S`, the structure at the end, which has a field for each
law: those of `Neutral S`, every law but Postulate 5, and Postulate 5 apart from them.
`Check/RoundTrip.lean` translates each word and law here back and compares it with the
library's declaration, binder by binder, and `Check/Laws.lean` asks the kernel whether each,
with the library's own words put back for `S`, is the library's declaration.
-/

@[expose] public section

namespace Model
"
  let wordsPart := if words.isEmpty then "" else
    s!"\n/-! ## The words the laws reach -/\n\nnamespace Signature\n\nvariable (S : Signature)\n\n\
      {"\n\n".intercalate words.toList}\n\nend Signature\n"
  let lawsPart := "\n".intercalate <| blocks.toList.map fun (ns, texts) =>
    let rel := ns.replacePrefix `Model .anonymous
    s!"\nnamespace {rel}\n\nvariable (S : Signature)\n\n\
      {"\n\n".intercalate texts.toList}\n\nend {rel}"
  let structures := s!"
/-! ## The laws as one structure -/

/-- Every law but those that hold only in the Euclidean plane: Postulate 5, and any rule the
library declares in `Elements.Tacit.Euclidean`. A hyperbolic plane is to satisfy these and
fail Postulate 5. -/
structure Neutral (S : Signature) : Prop where
{"\n".intercalate (neutral.toList.map field)}

/-- Every law of the lock, a field for each: those of `Neutral`, and Postulate 5. A model of
the laws is a signature `S` with `Laws S`. -/
structure Laws (S : Signature) : Prop extends Neutral S where
{"\n".intercalate (euclidean.toList.map field)}

end Model
"
  return header ++ wordsPart ++ "\n/-! ## The laws -/\n" ++ lawsPart ++ "\n" ++ structures

/-- The shape of a law's or a word's type with respect to the kinds of magnitude: no binder
of type `Elements.Kind`, a first binder of that type (`∀ {k : Kind}, …`), or anything else. -/
inductive KindShape where
  | none
  | first (bi : BinderInfo)
  | other

/-- How `type` binds a kind of magnitude. -/
def kindShape (type : Expr) : KindShape :=
  let bindsKind (e : Expr) : Bool := (e.find? fun
    | .forallE _ t _ _ | .lam _ t _ _ => t.isConstOf `Elements.Kind
    | _ => false).isSome
  match type with
  | .forallE _ t body bi =>
    if t.isConstOf `Elements.Kind then (if bindsKind body then .other else .first bi)
    else if bindsKind type then .other else .none
  | _ => if bindsKind type then .other else .none

/-- The proof that a translated statement over every kind, put at `original`, is the library's:
each direction is the other statement at the matching kind. -/
def kindProof : String :=
  "  ⟨fun h {k} => by\n    cases k with\n    | length => exact @h .length\n    \
    | angle => exact @h .angle\n    | area => exact @h .area,\n    fun h => h⟩"

/-- The text of `Check/Laws.lean`: for each word the generator wrote and each law, the
kernel's round trip. -/
def checksText (env : Environment) (p : Plan) (imports : Array Name) : Except String String := do
  let mut words : Array String := #[]
  for w in p.generated do
    let some ci := env.find? w | throw s!"`{w}` vanished"
    match kindShape ci.type with
    | .none =>
      let line := s!"example : original.{w.getString!} = {w} := rfl"
      words := words.push <| if line.length ≤ 100 then line
        else s!"example : original.{w.getString!} =\n    {w} := rfl"
    | _ => throw s!"the word `{w}` binds a kind of magnitude, which the generator cannot yet \
        check by the kernel"
  let mut laws : Array String := #[]
  for n in p.laws do
    let some ci := env.find? n | throw s!"`{n}` vanished"
    let lhs := s!"{(lawName n).replacePrefix `Model .anonymous} original"
    match kindShape ci.type with
    | .none =>
      let line := s!"example : {lhs} = type_of% @{n} := rfl"
      laws := laws.push <| if line.length ≤ 100 then line
        else s!"example : {lhs} =\n    type_of% @{n} := rfl"
    | .first .implicit => laws := laws.push s!"example : {lhs} ↔ type_of% @{n} :=\n{kindProof}"
    | _ => throw s!"the law `{n}` binds a kind of magnitude other than first and implicitly, \
        which the generator cannot yet check by the kernel"
  return s!"{"\n".intercalate (imports.toList.map (s!"import {·}"))}
import Model.Laws
import Check.Original

/-!
# The generated laws and words, checked by the kernel

**This file is generated: do not edit it.** `Check/Generator.lean` writes it with
`Model/Laws.lean`; to write it again, run `lake lean Check/Write.lean` in `model/`.

For each word and each law of `Model/Laws.lean`, the library's own words are put back for the
signature (`original`), and the kernel is asked whether the result is the library's
declaration. Each check is `rfl`: the kernel accepts it only if the two are the same
proposition, up to unfolding definitions. A law over every kind of magnitude makes the same
check up to relabelling the kinds, since the model's `Kind` is a copy of the library's: each
direction is the other statement at the matching kind. The words written by hand in
`Model/Signature.lean` are checked in `Check/Hand.lean`.

`Check/RoundTrip.lean` makes the stricter check by syntax, which also sees binder kinds and the
order of the binders. This file reads the library's axioms only through `type_of%`, which takes
a declaration's statement and does not use it.
-/

namespace Check

open Model

/-! ## The words -/

{"\n".intercalate words.toList}

/-! ## The laws -/

{"\n\n".intercalate laws.toList}

end Check
"

/-- A theorem's name, if `line` declares one: `theorem circles_meet : …`, perhaps after
attributes and `protected`. -/
def declaredTheorem (line : String) : Option String := Id.run do
  let mut s : String := line.trimAsciiStart.toString
  if s.startsWith "@[" then
    match s.splitOn "]" with
    | _ :: rest => s := ("]".intercalate rest).trimAsciiStart.toString
    | [] => pure ()
  if s.startsWith "protected " then
    s := (s.drop "protected ".length).toString.trimAsciiStart.toString
  unless s.startsWith "theorem " do return none
  let rest : String := (s.drop "theorem ".length).toString.trimAsciiStart.toString
  let name : String :=
    (rest.takeWhile fun c => !(c.isWhitespace || c == ':' || c == '(' || c == '{')).toString
  if name.isEmpty then none else some name

/-- The theorems of `Model/Euclidean/` named as a field of `Laws`, each with the module that
declares it, found in the files under `Model/Euclidean/` of the model at `modelDir`. -/
def provedInPlane (modelDir : System.FilePath) (fieldNames : Array Name) :
    IO (Array (Name × Name)) := do
  let files ← System.FilePath.walkDir (modelDir / "Model" / "Euclidean")
  let files := (files.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)
  let mut found : Array (Name × Name) := #[]
  for f in files do
    let comps := (f.withExtension "").components.drop modelDir.components.length
    let mod := comps.foldl Name.mkStr .anonymous
    for line in (← IO.FS.readFile f).splitOn "\n" do
      if let some t := declaredTheorem line then
        let n := Name.mkSimple t
        if fieldNames.contains n then
          if found.any (·.1 == n) then
            throw <| IO.userError s!"two theorems of Model/Euclidean/ are named `{n}`"
          found := found.push (n, mod)
  return found

/-- The text of `Model/Assembly.lean`, from the fields of `Laws` and the theorems that prove
them in the plane. -/
def assemblyText (laws : Array Name) (proved : Array (Name × Name)) : String :=
  let fs := lawFields laws
  let isProved (f : Name) := proved.any (·.1 == f)
  let open_ := fs.filter fun (_, f, _) => !isProved f
  let mods := (proved.map (·.2)).toList.eraseDups.toArray.qsort (·.toString < ·.toString)
  let law (n : Name) := (lawName n).replacePrefix `Model .anonymous
  let hyps := open_.toList.map fun (n, f, _) =>
    let line := s!"    ({f} : {law n} Euclidean.plane)"
    if line.length ≤ 100 then line else s!"    ({f} :\n      {law n} Euclidean.plane)"
  let assign := fs.toList.map fun (_, f, _) =>
    if isProved f then s!"  {f} := Euclidean.{f}" else s!"  {f} := {f}"
  let theorem_ := if open_.isEmpty then
      s!"/-- **The plane satisfies every law.** -/
theorem euclidean_laws : Laws Euclidean.plane where
{"\n".intercalate assign}

/-- **The laws have a model:** the ordinary plane. -/
theorem model_exists : ∃ S : Signature, Laws S :=
  ⟨Euclidean.plane, euclidean_laws⟩"
    else
      s!"/-- **The plane satisfies the laws,** given the {open_.size} not yet proved in it. -/
theorem euclidean_laws
{"\n".intercalate hyps} :
    Laws Euclidean.plane where
{"\n".intercalate assign}"
  let stand := if open_.isEmpty then
      s!"All {fs.size} laws are proved in the plane, so `euclidean_laws` has no hypothesis, and
`model_exists` follows from it."
    else
      s!"So far {proved.size} of the {fs.size} laws are proved in the plane. Until the rest are,
`euclidean_laws` takes them as hypotheses, so that it states exactly what is proved: the plane
satisfies every law, given the {open_.size} that are not yet proved in it. When none is left,
the generator writes it with no hypothesis, and `model_exists` after it."
  s!"module

public import Model.Laws
public import Model.Euclidean
{"\n".intercalate (mods.toList.map (s!"public import {·}"))}

/-!
# The plane satisfies the laws

**This file is generated: do not edit it.** `Check/Generator.lean` writes it, and `lake build`
fails while it differs from what the generator writes. To write it again, run
`lake lean Check/Write.lean` in `model/`.

A theorem of `Model/Euclidean/` named as a field of `Laws` (`Euclidean.circles_meet` for the
field `circles_meet`) proves that law in the plane, and `euclidean_laws` gathers them; Lean
checks here that each proves the law the generator wrote.

{stand}
-/

@[expose] public section

namespace Model

{theorem_}

end Model
"

/-! ## Running it -/

/-- The directory of the model package, from the path of the file being elaborated, which is
in `model/Check/`. -/
def modelDir : CommandElabM System.FilePath := do
  let file : System.FilePath := ← getFileName
  let file ← if file.isAbsolute then pure file else pure ((← IO.currentDir) / file)
  let some check := file.parent | throwError "no directory for {file}"
  let some dir := check.parent | throwError "no directory for {check}"
  unless ← (dir / "Model" / "Signature.lean").pathExists do
    throwError "{dir} is not the model package"
  return dir

/-- The repository's root: the directory of the model package's parent. -/
def repoRoot (modelDir : System.FilePath) : CommandElabM System.FilePath := do
  let some root := modelDir.parent | throwError "no repository above {modelDir}"
  return root

/-- The source path of a pure module, relative to the repository. -/
def pureModuleFile (m : Name) : String :=
  m.toString.replace "." "/" ++ ".lean"

/-- The permitted external module roots, recorded here alone. Package names come from
`model/lake-manifest.json`; roots come from their pinned Lake library configurations.
`stoicheia` is deliberately excluded. Lean's toolchain supplies `Init`, `Std`, `Lean` and
`Lake`; Mathlib's compiled closure reaches `Lake.Util.Version` through ImportGraph.
The other entries include the packages' test and auxiliary libraries as well as their
main libraries; ProofWidgets.Demos has the same root as ProofWidgets. -/
def modelImportPackages : Array (String × Array Name) := #[
  ("lean", #[`Init, `Std, `Lean, `Lake]),
  ("mathlib", #[`Mathlib, `Cache, `MathlibTest, `Archive, `Counterexamples, `Wanted, `docs]),
  ("plausible", #[`Plausible, `PlausibleTest]),
  ("LeanSearchClient", #[`LeanSearchClient, `LeanSearchClientTest]),
  ("importGraph", #[`ImportGraph, `ImportGraphTest]),
  ("proofwidgets", #[`ProofWidgets, `test]),
  ("aesop", #[`Aesop, `AesopTest]),
  ("Qq", #[`Qq, `QqTest]),
  ("batteries", #[`Batteries, `BatteriesTest]),
  ("Cli", #[`Cli, `CliTest])]

/-- The Model boundary, shared by the source and compiled-import checks. -/
def isModelImport (m : Name) : Bool :=
  isCanonicalModuleName m && (m.getRoot == `Model || pureModules.contains m ||
    modelImportPackages.any (fun (_, roots) => roots.contains m.getRoot))

/-- Check imports recorded for source files, with paths relative to the repository.
Model files may import only `Model`, its submodules, the four pure modules and the external
roots in `modelImportPackages`. Pure modules may import only each other and `Init`.
Every Model source is audited. Under the configured package roots and unmodified external
dependencies, these direct imports bound the local closure. This name-based check does not
authenticate external files, search paths or symlink targets. It needs no environment. -/
def checkModelImportsWith (files : List (String × List Name)) : Except String Unit := do
  for (file, imports) in files do
    let shared := pureModules.any fun m => pureModuleFile m == file
    for m in imports do
      unless isCanonicalModuleName m do
        throw s!"{file}: import `{m}` has a non-canonical module name"
      if shared then
        unless m.getRoot == `Init || pureModules.contains m do
          throw s!"{file}: pure module imports `{m}`, outside the four pure modules and `Init`"
      else if m.getRoot == `Elements && !pureModules.contains m then
        throw s!"{file}: Model imports `{m}`, outside the four pure modules"
      else unless isModelImport m do
        throw s!"{file}: Model imports `{m}`, outside the approved import roots"

/-- Read just the header with Lean's own parser. It handles comments, blank lines,
`module` and import modifiers, and stops at the first command after the imports.
Malformed headers are refused, with the parser's diagnostics. No module is loaded. -/
def modelImportHeader (file source : String) : IO (List Name) := do
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source file)
  if messages.hasErrors then
    let errors ← messages.toList.mapM fun m => m.toString
    throw <| IO.userError (String.join errors)
  return (HeaderSyntax.imports header (includeInit := false)).toList.map (·.module)

/-- Apply the import check to source text supplied as data. Regression cases use the same
header parser and pure decision as the real files, without writing planted source files. -/
def checkModelImportFixture (files : List (String × String)) : CommandElabM Unit := do
  let mut imports := []
  for (file, source) in files do
    imports := imports ++ [(file, ← modelImportHeader file source)]
  match checkModelImportsWith imports with
  | .ok () => pure ()
  | .error e => throwError "{e}"

/-- Check directory listings before selecting sources. Case variants of `.lean` are
errors, not files to ignore: a case-insensitive filesystem can resolve them as sources.
Distinct paths equal after lowercasing are refused too, including directory components.
The input is data so the same regressions run on case-sensitive filesystems. -/
def checkModelSourceListing (files : Array String) : Except String Unit := do
  let mut seen : Array String := #[]
  for file in files do
    if let some other := seen.find? (fun s => s != file && s.toLower == file.toLower) then
      throw s!"source paths differ only in case: `{other}` and `{file}`"
    seen := seen.push file
  for file in files do
    if let some ext := (System.FilePath.mk file).extension then
      if ext.toLower == "lean" && ext != "lean" then
        throw s!"{file}: non-canonical source extension (expected `.lean`)"
    for m in pureModules do
      let expected := pureModuleFile m
      if file != expected && file.toLower == expected.toLower then
        throw s!"{file}: non-canonical pure source path (expected `{expected}`)"

/-- The production listing decision, exercised without creating files. -/
def checkModelSourceListingFixture (files : List String) : CommandElabM Unit := do
  match checkModelSourceListing files.toArray with
  | .ok () => pure ()
  | .error e => throwError "{e}"

/-- Collect source paths once for both import audits. Validate the actual listings under
`Model/` and `Elements/Foundations/`, and the spelling of the Model root file. The latter
directory exists before the pure modules arrive and is also Lake's input directory.
Only Model sources and the four pure sources have their import headers read. -/
def modelSourceFiles (dir : System.FilePath) : CommandElabM (Array String) := do
  let root ← repoRoot dir
  let mut files ← System.FilePath.walkDir (dir / "Model")
  files := files ++ (← System.FilePath.walkDir (root / "Elements" / "Foundations"))
  for entry in ← dir.readDir do
    if entry.fileName.toLower == "model.lean" then files := files.push entry.path
  let relative := (files.map fun file =>
    "/".intercalate (file.components.drop root.components.length)).qsort (· < ·)
  match checkModelSourceListing relative with
  | .ok () => pure ()
  | .error e => throwError "{e}"
  unless relative.contains "model/Model.lean" do
    throwError "model/Model.lean: missing canonical source path"
  return relative.filter fun file =>
    (System.FilePath.mk file).extension == some "lean" &&
      (file == "model/Model.lean" || file.startsWith "model/Model/" ||
        pureModules.any (pureModuleFile · == file))

/-- Audit every Model source, including files nothing imports, and each pure module
present in the repository. This source check complements the compiled-import graph. -/
def checkModelImports : CommandElabM Unit := do
  let dir ← modelDir
  let root ← repoRoot dir
  let mut sources := []
  for file in ← modelSourceFiles dir do
    sources := sources ++ [(file, ← IO.FS.readFile (root / file))]
  checkModelImportFixture sources

/-- Decide the compiled-import boundary from a closure supplied as data. Every source
module must be covered too: the Model library currently builds only the root and its
imports, so an unimported source has no compiled graph to audit and is refused. -/
def checkModelImportClosureWith (closure : Array Name) (sources : Array Name := #[]) :
    Except String Unit := do
  for m in closure do
    unless isCanonicalModuleName m do
      throw s!"Model compiled import closure: non-canonical module name `{m}`"
    unless isModelImport m do
      throw s!"Model compiled import closure reaches `{m}`, outside the approved import roots"
  for m in sources do
    unless closure.contains m do
      throw s!"Model source `{m}` is not in the compiled import closure of `Model`"

/-- Exercise the same decision on planted closures, without installing any modules. -/
def checkModelImportClosureFixture (closure : Array Name) (sources : Array Name := #[]) :
    CommandElabM Unit := do
  match checkModelImportClosureWith closure sources with
  | .ok () => pure ()
  | .error e => throwError "{e}"

/-- Traverse the graph recorded in compiled module headers, starting at `Model`.
`findOLean` resolves each module on the current search path; `readModuleData` reads its
imports, including non-public imports. Names are checked before file lookup. A visited
set handles repeated imports and cycles. This proves the permitted names in that graph;
it does not authenticate the files on the search path or the files an earlier environment
loaded with explicit import artefacts. It neither imports declarations nor runs module
initialisers. Lake must build the Model library before this check runs. -/
def modelImportClosure : IO (Array Name) := do
  let mut todo := #[#[`Model]]
  let mut seen : NameSet := {}
  let mut closure := #[]
  while !todo.isEmpty do
    let path := todo.back!
    let m := path.back!
    todo := todo.pop
    if seen.contains m then continue
    match checkModelImportClosureWith #[m] with
    | .ok () => pure ()
    | .error e =>
      let route := " -> ".intercalate (path.toList.map toString)
      throw <| IO.userError s!"{e}\ncompiled import path: {route}"
    seen := seen.insert m
    closure := closure.push m
    let (data, _) ← readModuleData (← findOLean m)
    todo := todo ++ data.imports.map (fun i => path.push i.module)
  return closure

/-- Check the real compiled graph and compare it with the source audit's Model list.
Lake's Model library has root `Model` and default glob `Glob.one Model`, so all built
Model modules are in this closure. If its globs ever grow, the starting modules and this
coverage check must grow with them. The four pure sources need not yet exist or be used. -/
def checkModelImportClosure : CommandElabM Unit := do
  let files ← modelSourceFiles (← modelDir)
  let sources := (files.filter (·.startsWith "model/")).map fun file =>
    ((file.dropEnd 5).toString.splitOn "/").drop 1 |>.foldl Name.str .anonymous
  checkModelImportClosureFixture (← modelImportClosure) sources

/-- The hash `model/lock.sha256` holds: its one line that is not a comment, before the file
name. -/
def pinnedHash (modelDir : System.FilePath) : IO String := do
  let lines := (← IO.FS.readFile (modelDir / "lock.sha256")).splitOn "\n" |>.filter fun l =>
    !l.trimAscii.toString.isEmpty && !l.startsWith "#"
  match lines with
  | [l] => return (l.splitOn " ")[0]!
  | _ => throw <| IO.userError "model/lock.sha256 should hold one line that is not a comment"

/-- Check the lock against the library's declarations: the hash `model/lock.sha256` holds is
the lock's, every file of `Elements/Foundations/` is imported, the axioms declared there are
exactly the lock's `[axioms]`, each with the statement the lock prints, and every word they
reach is in the lock's `[vocabulary]` as Lean prints it. Returns the lock's hash. -/
def checkLock (root modelDir : System.FilePath) (p : Plan) (checkHash : Bool) :
    CommandElabM String := do
  let env ← getEnv
  let lockFile := root / "Certificate" / "axioms.lock"
  let hash := sha256 (← IO.FS.readBinFile lockFile)
  let mut errors : Array String := #[]
  if checkHash then
    let pinned ← pinnedHash modelDir
    unless pinned == hash do
      errors := errors.push s!"model/lock.sha256 holds {pinned}, but the lock's sha256 is \
        {hash}: bring the model up to date with the lock, then renew model/lock.sha256 \
        (model/README.md, \"How the lock ties it\")"
  for m in ← foundationModules root do
    unless env.header.moduleNames.contains m do
      errors := errors.push s!"`{m}` is not imported here: add it to the imports, so that the \
        generator reads every axiom of the foundations"
  let lock ← match parseLock (← IO.FS.readFile lockFile) with
    | .ok l => pure l
    | .error e => throwError "Certificate/axioms.lock: {e}"
  let lockAxioms := lock.axioms.entries.map (·.1)
  let declared := p.laws.map lockKey
  for a in declared do
    unless lockAxioms.contains a do
      errors := errors.push s!"`{a}` is declared in the foundations but not in the lock's [axioms]"
  for a in lockAxioms do
    unless declared.contains a do
      errors := errors.push s!"`{a}` is in the lock's [axioms] but not declared in the foundations"
  for (key, printed) in lock.axioms.entries do
    let some n := p.laws.find? (lockKey · == key) | continue
    let some ci := env.find? n | continue
    let now ← liftTermElabM <| lockPrint ci.type
    unless now == printed do
      errors := errors.push s!"`{key}`: the lock prints `{printed}`, and Lean now prints `{now}`"
  for w in p.reached do
    let key := lockKey w
    let some ci := env.find? w | continue
    let now ← liftTermElabM <| lockWord ci
    match lock.vocabulary.entries.find? (·.1 == key) with
    | none =>
      errors := errors.push s!"`{key}`, a word the laws reach, is not in the lock's [vocabulary]"
    | some (_, printed) =>
      unless now == printed do
        errors := errors.push s!"`{key}`: the lock prints `{printed}`, and Lean now prints `{now}`"
  unless errors.isEmpty do throwError "{"\n".intercalate errors.toList}"
  return hash

/-- The library's modules this run reads, as the generated `Check/Laws.lean` imports them:
those of `Elements.Foundations`. -/
def importedFoundations : CommandElabM (Array Name) := do
  let env ← getEnv
  return (env.header.moduleNames.filter fun m =>
    isCanonicalModuleName m && (`Elements.Foundations).isPrefixOf m).qsort
    (·.toString < ·.toString)

/-- The three files, written in memory from the declarations in the environment. -/
def generate (modelDir : System.FilePath) (checkHash : Bool) : CommandElabM Output := do
  let root ← repoRoot modelDir
  let env ← getEnv
  let p ← match plan env with
    | .ok p => pure p
    | .error e => throwError "the generator cannot translate the laws: {e}"
  let hash ← checkLock root modelDir p checkHash
  let laws ← liftTermElabM <| withoutModifyingEnv <| lawsText p hash
  let checks ← match checksText env p (← importedFoundations) with
    | .ok t => pure t
    | .error e => throwError "{e}"
  let proved ← provedInPlane modelDir (p.laws.map fieldName)
  return { laws, checks, assembly := assemblyText p.laws proved }

/-- The files the generator writes, with their paths in the model package. -/
def outputs (o : Output) : List (String × String) :=
  [("Model/Laws.lean", o.laws), ("Check/Laws.lean", o.checks),
   ("Model/Assembly.lean", o.assembly)]

/-- Where `committed` first differs from `generated`, line by line. -/
def lineDifference (committed generated : String) : Option String := Id.run do
  let a := committed.splitOn "\n"
  let b := generated.splitOn "\n"
  for i in [0:max a.length b.length] do
    let x := a[i]?.getD "(the end of the file)"
    let y := b[i]?.getD "(the end of the file)"
    if x != y then return some s!"line {i + 1} reads\n    {x}\nwhere the generator writes\n    {y}"
  return none

/-- Check, at every build, that the committed generated files are what the generator writes
now, after checking the lock, its hash and the axioms (`checkLock`). -/
def checkFiles : CommandElabM Unit := do
  let dir ← modelDir
  let out ← generate dir (checkHash := true)
  let mut errors : Array String := #[]
  for (path, text) in outputs out do
    let file := dir / path
    unless ← file.pathExists do
      errors := errors.push s!"{path} is missing"
      continue
    if let some d := lineDifference (← IO.FS.readFile file) text then
      errors := errors.push s!"{path} is not what the generator writes: {d}"
  unless errors.isEmpty do
    throwError "{"\n".intercalate errors.toList}\nTo write the generated files again, run \
      `lake lean Check/Write.lean` in model/."

/-- Write the generated files. The lock's hash is not checked against `model/lock.sha256`
here: the files record the lock's own hash, and the build checks the two agree. -/
def writeFiles : CommandElabM Unit := do
  let dir ← modelDir
  let out ← generate dir (checkHash := false)
  for (path, text) in outputs out do
    IO.FS.writeFile (dir / path) text
  let pinned ← pinnedHash dir
  let hash := sha256 (← IO.FS.readBinFile ((← repoRoot dir) / "Certificate" / "axioms.lock"))
  logInfo m!"wrote {", ".intercalate ((outputs out).map (·.1))}"
  unless pinned == hash do
    logWarning m!"model/lock.sha256 holds {pinned}, but the lock's sha256 is {hash}: once the \
      model is up to date with the lock, renew model/lock.sha256, or lake build fails"

/-! ## The round trip by syntax -/

/-- The value of the definition `n`, and its type. -/
def definition (n : Name) : MetaM (Expr × Expr) := do
  let some ci := (← getEnv).find? n | throwError "`{n}` is not declared"
  let some v := ci.value? | throwError "`{n}` is not a definition"
  return (v, ci.type)

/-- Compare a statement of the model, over the signature `S`, translated back, with the
library's `lib`, after unfolding the carrier words when `carriers` is set. -/
def compareBack (p : Plan) (S : Expr) (what : String) (model lib : Expr) (carriers : Bool) :
    MetaM (Option String) := do
  match untranslate p.inverse S what model with
  | .error e => return some e
  | .ok back =>
    let (x, y) := if carriers then (unfoldCarriers back, unfoldCarriers lib) else (back, lib)
    return (firstDifference "the library" x y).map fun d => s!"{what}: {d}"

/-- A definition of the model over the signature, `fun S => …`, against the library's word or
law: its value against the library's, and its type, after the signature, against the
library's type. For a law, whose library counterpart is an axiom, `libValue` is the axiom's
statement and the type is `Prop`. -/
def compareDefinition (p : Plan) (model : Name) (libValue libType : Expr) (carriers : Bool) :
    MetaM (Array String) := do
  let (value, type) ← definition model
  withSignature fun S => do
    let mut errors : Array String := #[]
    let body := value.beta #[S]
    if let some e ← compareBack p S s!"`{model}`" body libValue carriers then
      errors := errors.push e
    match type with
    | .forallE _ (.const `Model.Signature []) rest _ =>
      if let some e ← compareBack p S s!"the type of `{model}`" (rest.instantiate1 S) libType
          carriers then
        errors := errors.push e
    | _ => errors := errors.push s!"`{model}` does not take a signature first"
    return errors

/-- Each field of `Model.Signature` has the type of the library's opaque word, translated,
up to the carrier words and the names of its binders. -/
def compareFields (p : Plan) : MetaM (Array String) := do
  let env ← getEnv
  let mut errors : Array String := #[]
  let declared := getStructureFields env `Model.Signature
  unless declared.toList == (fields.map (·.2.getString!)).toList.map Name.mkSimple do
    errors := errors.push s!"the fields of `Model.Signature` are {declared}, not the seventeen \
      words of `Check.Generator.fields`, in that order"
  for (lib, field) in fields do
    let (some libCi, some fieldCi) := (env.find? lib, env.find? field) | do
      errors := errors.push s!"no `{lib}` or no `{field}`"
      continue
    unless libCi matches .opaqueInfo _ do errors := errors.push s!"`{lib}` is not opaque"
    let libType := libCi.instantiateTypeLevelParams (levelsOf lib)
    let e ← withSignature fun S => do
      match fieldCi.type with
      | .forallE _ _ rest _ =>
        let mine := rest.instantiate1 S
        match translate env p.vocab S s!"`{lib}`" libType with
        | .error e => return some e
        | .ok _ =>
          let erase := fun (e : Expr) => (unfoldCarriers e).replace fun
            | .forallE _ t b bi => some (.forallE .anonymous t b bi)
            | _ => none
          match untranslate p.inverse S s!"the field `{field}`" mine with
          | .error e => return some e
          | .ok back =>
            let d := firstDifference "the library" (erase back) (erase libType)
            return d.map fun d => s!"the type of the field `{field}`, against `{lib}`: {d}"
      | _ => return some s!"`{field}` is not a projection"
    if let some e := e then errors := errors.push e
  return errors

/-- `Check.original` puts the library's own words for the signature's fields: each field is the
library's opaque word, or for the four over the kind of magnitude, the library's word at the
matching kind. -/
def compareOriginal : MetaM (Array String) := do
  let env ← getEnv
  let some ci := env.find? `Check.original | return #["`Check.original` is not declared"]
  let some v := ci.value? | return #["`Check.original` is not a definition"]
  let args := v.getAppArgs
  unless v.isAppOf `Model.Signature.mk && args.size == fields.size do
    return #["`Check.original` is not one `Model.Signature.mk` with a value for each field"]
  let kindFn := Expr.const `Check.kind []
  let mut errors : Array String := #[]
  for ((lib, field), arg) in fields.zip args do
    let expected : Expr := match field with
      | `Model.Signature.MagnitudeImpl =>
        .lam `k (.const `Model.Kind [])
          (mkApp (.const lib (levelsOf lib)) (mkApp kindFn (.bvar 0))) .default
      | `Model.Signature.zero | `Model.Signature.add | `Model.Signature.lt =>
        .lam `k (.const `Model.Kind [])
          (mkApp (.const lib (levelsOf lib)) (mkApp kindFn (.bvar 0))) .implicit
      | _ => .const lib (levelsOf lib)
    let erase := fun (e : Expr) => e.replace fun
      | .lam _ t b bi => some (.lam .anonymous t b bi)
      | _ => none
    if let some d := firstDifference "the library" (erase arg) (erase expected) then
      errors := errors.push s!"`Check.original` gives the field `{field}` other than `{lib}`: {d}"
  return errors

/-- The round trip by syntax, on the laws and words as Lean elaborated them from the committed
`Model/Laws.lean`: each translated back and compared with the library's declaration (up to
the carrier words, `unfoldCarriers`); the words written by hand in `Model/Signature.lean`, and
the signature's fields, likewise; `Neutral` and `Laws`, with exactly a field for each law, of
type `Law.… S`; each law of `Model/Hand.lean` against the law generated for it; and
`Check.original`. -/
def checkRoundTrip : CommandElabM Unit := do
  let env ← getEnv
  let p ← match plan env with
    | .ok p => pure p
    | .error e => throwError "the generator cannot translate the laws: {e}"
  let errors ← liftTermElabM do
    let mut errors : Array String := #[]
    -- The laws.
    for n in p.laws do
      let some ci := env.find? n | continue
      unless moduleOf? env (lawName n) == some `Model.Laws do
        errors := errors.push s!"`{lawName n}` is not declared in `Model/Laws.lean`"
        continue
      errors := errors ++ (← compareDefinition p (lawName n) ci.type (.sort 0) true)
    -- The generated words.
    for w in p.generated do
      let some ci := env.find? w | continue
      let some v := ci.value? | continue
      unless moduleOf? env (generatedName w) == some `Model.Laws do
        errors := errors.push s!"`{generatedName w}` is not declared in `Model/Laws.lean`"
        continue
      errors := errors ++ (← compareDefinition p (generatedName w) v ci.type true)
    -- The words written by hand in the signature's file: exactly, with nothing unfolded.
    for (lib, model) in signatureWords do
      let some ci := env.find? lib | continue
      let some v := ci.value? | continue
      errors := errors ++ (← compareDefinition p model v ci.type false)
    -- The fields.
    errors := errors ++ (← compareFields p)
    -- The structures.
    let fs := lawFields p.laws
    let laws := getStructureFieldsFlattened env `Model.Laws (includeSubobjectFields := false)
    unless laws.toList == (fs.filter (!·.2.2) ++ fs.filter (·.2.2)).toList.map (·.2.1) do
      errors := errors.push s!"the fields of `Model.Laws` are {laws}, not one for each law of \
        the lock, the Euclidean ones last"
    let neutral := getStructureFieldsFlattened env `Model.Neutral (includeSubobjectFields := false)
    unless neutral.toList == (fs.filter (!·.2.2)).toList.map (·.2.1) do
      errors := errors.push s!"the fields of `Model.Neutral` are {neutral}, not one for each law \
        but the Euclidean ones"
    for (n, f, euclid) in fs do
      let proj := (if euclid then `Model.Laws else `Model.Neutral) ++ f
      let some ci := env.find? proj | do
        errors := errors.push s!"no field `{proj}`"
        continue
      let expected ← withLocalDecl `S .implicit (.const `Model.Signature []) fun S => do
        let structName := if euclid then `Model.Laws else `Model.Neutral
        withLocalDeclD `self (mkApp (.const structName []) S) fun self =>
          mkForallFVars #[S, self] (mkApp (.const (lawName n) []) S)
      let ty := ci.type.replace fun
        | .forallE _ t b bi => some (.forallE .anonymous t b bi)
        | _ => none
      let expected := expected.replace fun
        | .forallE _ t b bi => some (.forallE .anonymous t b bi)
        | _ => none
      if let some d := firstDifference s!"`{lawName n} S`" ty expected then
        errors := errors.push s!"the field `{f}` is not of type `{lawName n} S`: {d}"
    -- The hand translations.
    for (n, f, _) in fs do
      let hand := `Model.Hand ++ f
      unless env.contains hand do continue
      let (handValue, _) ← definition hand
      let (lawValue, _) ← definition (lawName n)
      let d ← withSignature fun S => do
        match untranslate p.inverse S s!"`{hand}`" (handValue.beta #[S]) with
        | .error e => return some e
        | .ok h =>
          match untranslate p.inverse S s!"`{lawName n}`" (lawValue.beta #[S]) with
          | .error e => return some e
          | .ok l =>
            let d := firstDifference "the generated law" (unfoldCarriers h) (unfoldCarriers l)
            return d.map fun d => s!"`{hand}`, written by hand, against `{lawName n}`: {d}"
      if let some d := d then errors := errors.push d
    -- The signature the kernel's round trip puts back.
    if env.contains `Check.original then errors := errors ++ (← compareOriginal)
    return errors
  unless errors.isEmpty do throwError "{"\n".intercalate errors.toList}"

/-- Compare the definition `planted`, over the signature, with the library's axiom `lib`, as
`checkRoundTrip` compares a generated law: for the tests that the check catches what it is
meant to. -/
def comparePlanted (planted lib : Name) : CommandElabM Unit := do
  let env ← getEnv
  let p ← match plan env with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let some ci := env.find? lib | throwError "no `{lib}`"
  let errors ← liftTermElabM <| compareDefinition p planted ci.type (.sort 0) true
  unless errors.isEmpty do throwError "{"\n".intercalate errors.toList}"

/-- Compare a planted word with a shared or generated definition, using the same strict
comparison as generated words. Shared words themselves are pinned by the vocabulary lock. -/
def comparePlantedWord (planted lib : Name) : CommandElabM Unit := do
  let env ← getEnv
  let p ← match plan env with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let some ci := env.find? lib | throwError "no `{lib}`"
  let some value := ci.value? | throwError "`{lib}` is not a definition"
  let errors ← liftTermElabM <| compareDefinition p planted value ci.type true
  unless errors.isEmpty do throwError "{"\n".intercalate errors.toList}"

/-- Translate the value of the definition `n`, a statement in the library's words, as the
generator translates a law: for the tests that a constant it does not translate is refused. -/
def translatePlanted (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let p ← match plan env with
    | .ok p => pure p
    | .error e => throwError "{e}"
  let some ci := env.find? n | throwError "no `{n}`"
  let some v := ci.value? | throwError "`{n}` is not a definition"
  liftTermElabM <| withSignature fun S => do
    match translate env p.vocab S s!"`{n}`" v with
    | .error e => throwError e
    | .ok _ => pure ()

/-- Run the purity audit with isolated replacements for existing declarations. -/
def checkPureFixture (roots : Array Name) (replacements : Array ConstantInfo := #[]) :
    CommandElabM Unit := do
  let env ← getEnv
  let lookup := fun n => (replacements.find? (·.name == n)).orElse fun _ => env.find? n
  match checkPureWith env lookup roots with
  | .ok () => pure ()
  | .error e => throwError "{e}"

/-- Plant declaring-module lookup data for the two geometric words from the escape
report. Exercise the same module decisions as `isLeanCore` and `isSharedWith`, without
constructing an environment or installing a module. -/
def checkModuleTrustFixture (m : Name) : CommandElabM Unit := do
  let lookup := fun c =>
    if c == `Elements.Point || c == `Elements.Collinear then some m else none
  for c in [`Elements.Point, `Elements.Collinear] do
    for package? in [none, some "stoicheia"] do
      if (lookup c).any (fun n => isLeanCoreModule n package?) then
        throwError "non-canonical module made `{c}` Lean's own"
    if (lookup c).any (isSharedModuleWith (pureModules.push m)) then
      throwError "non-canonical module made `{c}` shared"

/-- Test the canonical predicate and the decisions that use it, before any pure module
exists. Escaped strings are also passed through Lean's real header parser; anonymous and
numeric names can only be supplied directly as data. No fixture loads an import. -/
def checkCanonicalModuleNames : CommandElabM Unit := do
  let env ← getEnv
  unless isLeanCore env ``Nat && isLeanCore env ``List && isLeanCore env ``propext do
    throwError "installed Init declarations failed the core decision"
  for m in pureModules ++ #[`Init, `Init.Data.List.Basic, `Model.Laws.«areas-p5»,
      `Model.«αβ», `Model.«v1.2», `Model.«123»] do
    unless isCanonicalModuleName m do throwError "canonical module refused: `{m}`"
    unless isLeanCoreModule m none == (m.getRoot == `Init) do
      throwError "wrong core decision for `{m}`"
    for package in ["stoicheia", "model", "lean", "Init", ""] do
      if isLeanCoreModule m (some package) then
        throwError "core decision accepted `{m}` from package {repr package}"
    unless isSharedModuleWith (pureModules.push m) m do
      throwError "canonical shared module refused: `{m}`"
  let badParts := ["", ".", "..", "A/B", "A\\B", "/tmp/Elements/Foundations/Words",
    "\\tmp\\Words", "C:", "C:Words", "C:/Words", "C:\\Words", "Words:stream",
    "\\\\host\\Words", "\x00Words", "Words\x00", "Words.", "Words ", ".. ", "..."]
  let mut badNames := #[Name.anonymous, Name.num .anonymous 0, Name.num `Init 0,
    Name.str (Name.num `Init 0) "Words"]
  for root in [Name.anonymous, `Init, `Model, `Elements.Foundations, `Unknown] do
    for part in badParts do
      let m := Name.str root part
      badNames := badNames.push m |>.push (Name.str m "Words")
      let source := s!"import {if root.isAnonymous then "" else s!"{root}."}«{part}»\n"
      unless (← modelImportHeader "planted header" source) == [m] do
        throwError "header parser changed the escaped component {repr part}"
  for m in badNames do
    if isCanonicalModuleName m then throwError "non-canonical module accepted: `{m}`"
    checkModuleTrustFixture m
    for file in ["model/Model.lean", pureModuleFile pureModules[0]!] do
      match checkModelImportsWith [(file, [m])] with
      | .ok () => throwError "import audit accepted non-canonical `{m}`"
      | .error e =>
        unless e == s!"{file}: import `{m}` has a non-canonical module name" do
          throwError "unexpected non-canonical import refusal: {e}"
    match checkPureModulesWith #[m] (← getEnv) (fun _ => none) with
    | .ok () => throwError "module audit accepted a non-canonical sharing boundary"
    | .error e =>
      unless e == s!"non-canonical shared module `{m}`" do
        throwError "unexpected shared boundary refusal: {e}"

/-- A copy of a definition with a dependency in its type or value. This is lookup data,
never a declaration submitted to the kernel. -/
def pureDependencyCopy (env : Environment) (target dep : Name) (inType : Bool) :
    Except String ConstantInfo := do
  let some (.defnInfo target) := env.find? target
    | throw s!"`{target}` is not a definition"
  let some dependency := env.find? dep | throw s!"no planted dependency `{dep}`"
  let plant (body : Expr) := Expr.letE `planted dependency.type
    (.const dep (dependency.levelParams.map Level.param)) body true
  return .defnInfo <| if inType then { target with type := plant target.type }
    else { target with value := plant target.value }

/-- Plant a dependency in any definition and audit from that definition as the root,
using an isolated lookup. This serves both Init fixtures and the shared calculus. -/
def plantPureDependency (target dep : Name) (inType : Bool := false) : CommandElabM Unit := do
  let replacement ← match pureDependencyCopy (← getEnv) target dep inType with
    | .ok ci => pure ci
    | .error e => throwError "{e}"
  checkPureFixture #[target] #[replacement]

/-- Make `id` reach `Not`, then put the dependency in `Not`'s type or value. Neither
copy is submitted to the kernel as a declaration. -/
def pureDependency (dep : Name) (inType : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let some (.defnInfo root) := env.find? ``id | throwError "no Init identity definition"
  let next ← match pureDependencyCopy env ``Not dep inType with
    | .ok ci => pure ci
    | .error e => throwError "{e}"
  checkPureFixture #[``id] #[
    .defnInfo { root with value := .const ``Not [] }, next]

/-- Check actual identity entries in both dictionaries, then preserve a shared constant
with zero, symbolic and compound universe arguments in both directions. -/
def checkIdentityPlan (p : Plan) (c : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless (p.vocab.find? c).any (fun t => t.identity && t.name == c && !t.overS) &&
      (p.inverse.find? c).any (fun t => t.identity && t.name == c && !t.overS) do
    throwError "`{c}` has no identity entry in both dictionaries"
  let some ci := env.find? c | throwError "no shared declaration `{c}`"
  unless !ci.levelParams.isEmpty do throwError "`{c}` has no universe arguments to test"
  liftTermElabM <| withSignature fun S => do
    for levels in [
        ci.levelParams.map (fun _ => Level.zero),
        ci.levelParams.map Level.param,
        ci.levelParams.map (fun u => Level.succ (.max (.param u) (.param `v)))] do
      let original := Expr.const c levels
      let translated ← match translate env p.vocab S s!"`{c}`" original with
        | .ok e => pure e
        | .error e => throwError "{e}"
      unless translated == original do
        throwError "`{c}` changed in translation at {levels}"
      let restored ← match untranslate p.inverse S s!"`{c}`" translated with
        | .ok e => pure e
        | .error e => throwError "{e}"
      unless restored == original do
        throwError "`{c}` changed in reverse translation at {levels}"

/-- Exercise the same plan construction before the pure modules exist, with the supplied
module boundary and a shared word explicitly included among the reached words. -/
def checkSharedIdentityWith (modules : Array Name) (c : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isSharedWith modules env c do throwError "`{c}` is not shared"
  let p ← match planWith modules env #[c] with
    | .ok p => pure p
    | .error e => throwError "{e}"
  checkIdentityPlan p c

/-- Check the production plan's shared identity entries. A constant outside the four pure
modules is refused before translation. -/
def checkSharedIdentity (c : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isShared env c do throwError "`{c}` is not shared"
  let p ← match plan env with
    | .ok p => pure p
    | .error e => throwError "{e}"
  checkIdentityPlan p c

/-- Collect roots from module data, using an optional isolated replacement. A planted
dependency in an otherwise unused declaration must be found without an explicit root. -/
def checkPureModuleFixture (modules : Array Name) (target : Name)
    (dep : Option Name := none) : CommandElabM Unit := do
  let env ← getEnv
  unless isSharedWith modules env target do throwError "`{target}` is not shared"
  let replacement ← match dep with
    | none => pure none
    | some dep => match pureDependencyCopy env target dep false with
      | .ok ci => pure (some ci)
      | .error e => throwError "{e}"
  let lookup := fun n => (replacement.filter (·.name == n)).orElse fun _ => env.find? n
  match checkPureModulesWith modules env lookup with
  | .ok () => pure ()
  | .error e => throwError "{e}"

/-- The actual shared-header printer includes a reached module once, ignores an unreached
module, and contributes no newline when the production boundary is absent. -/
def checkSharedImportHeader : CommandElabM Unit := do
  let env ← getEnv
  let reached := #[``List.filterMap, ``List.filterMap]
  let header := sharedImportHeaderWith #[`Init.Data.Option.Basic, `Init.Data.List.Basic]
    env reached
  unless header == "\npublic import Init.Data.List.Basic" do
    throwError "unexpected shared import header: {repr header}"
  unless (sharedImportHeaderWith #[] env reached).isEmpty &&
      (sharedImportHeaderWith #[`Init.Data.List.Basic] env #[]).isEmpty do
    throwError "an empty shared import list added text"

/-- A dependency reached only through an opaque value in an isolated lookup. No copy is
submitted to the kernel, and the opaque declaration's type contains no planted dependency. -/
def pureOpaqueDependency : CommandElabM Unit := do
  let env ← getEnv
  let some (.defnInfo root) := env.find? ``id | throwError "no Init identity definition"
  let some next := env.find? ``Not | throwError "no Init negation definition"
  checkPureFixture #[``id] #[
    .defnInfo { root with value := .const ``Not [] },
    .opaqueInfo {
      name := next.name, levelParams := next.levelParams, type := next.type,
      value := .const `Elements.Point [], isUnsafe := false }]

/-- A dependency reached only through a recursor rule in an isolated lookup. The copied
recursor's type is unchanged and a recursor has no ordinary declaration value to inspect. -/
def pureRecursorDependency : CommandElabM Unit := do
  let env ← getEnv
  let some (.recInfo next) := env.find? ``Nat.rec | throwError "no Init natural recursor"
  let rule :: rest := next.rules | throwError "no natural recursor rule"
  checkPureFixture #[``Nat.rec] #[
    .recInfo { next with rules := { rule with rhs := .const `Elements.Point [] } :: rest }]

/-- An axiom-shaped copy of `Not` keeps its Init provenance, so only the axiom check can
refuse it. It is lookup data, never a new axiom in the environment. -/
def pureAxiom : CommandElabM Unit := do
  let env ← getEnv
  let some (.defnInfo root) := env.find? ``id | throwError "no Init identity definition"
  let some next := env.find? ``Not | throwError "no Init negation definition"
  checkPureFixture #[``id] #[
    .defnInfo { root with value := .const ``Not [] },
    .axiomInfo {
      name := next.name, levelParams := next.levelParams, type := next.type, isUnsafe := false }]

/-- Exercise the actual path lookup with both spellings of a Check file. In the relative
case it must ascend to the package directory after resolving against the working directory. -/
def checkModelDirPaths : CommandElabM Unit := do
  let cwd ← IO.currentDir
  let inModel ← (cwd / "Model" / "Signature.lean").pathExists
  let dir := if inModel then cwd else cwd / "model"
  let relative : System.FilePath :=
    if inModel then "Check/RoundTrip.lean" else "model/Check/RoundTrip.lean"
  for file in [relative, cwd / relative] do
    let found ← withReader (fun c => { c with fileName := file.toString }) modelDir
    unless found == dir do
      throwError "modelDir returned {found}, expected the model package {dir}"

end Check.Generator
