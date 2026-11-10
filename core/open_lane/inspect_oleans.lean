/-
What a compiled submission declares, read from its .olean files by Lean itself.

    lean --run inspect_oleans.lean --olean <module>=<file.olean> ... [--protected <module>]
         [--where <constant> ...] [--closure <constant> ...]

Prints one JSON object:

* `modules`: per module given, its imports, the number of constants it declares, and whether it was
  written in the module system (`is_module`: such a file's .olean hides the bodies of its definitions);
* `duplicates`: every constant that more than one of the given modules declares, with those modules;
* `reserved`: every constant named under `Protected._`, the marker used below;
* `where`: per constant asked for, the modules that declare it (one, for a constant that exists once);
* `closures`: per constant asked for, everything it depends on among the constants of the given
  modules, itself included: through types, and through the values of definitions. A theorem counts
  with its statement and never with its proof, since a proof changes nothing a definition computes.
  Each constant comes with the module that declares it, its kind, and a canonical text of its kernel
  terms.

A canonical text does not depend on how a term is shared in memory, on binder names, or on the name
of the protected module: a name that begins with the module given as `--protected` is written with
`Protected._` in its place. So the same definition compiled against two protected modules gives the
same text exactly when its kernel terms are the same up to that one renaming. The pipeline hashes the
texts (core/open_lane/inspect.py) and refuses a submission with a duplicate or a reserved name, where
a text would not say which constant it is about.

With `--library <module>=<file.olean> ...` (the modules of the Lean project's own library, as its
build compiled them) and what a run shows of them, `--shown-whole <module> ...` and
`--shown-lines <module>=<line>,<line>,... ...` (the source lines of a module that the run shows), it
also prints `surface`:

* `classes`: per constant asked for with `--classify`, whether the library declares it and the run
  shows it: `shown` (its module is shown whole, or the line that declares it is one of the lines
  shown), `exposed` (not shown, but the type or the value of a shown constant mentions it, so that
  unfolding what is shown puts it into a term), `closed` (neither) or `absent` (no constant of the
  library);
* `library`: how many modules and constants the library has, how many of them are shown, and the
  exposed ones by name;
* `uses`: every constant of the given modules, the protected module's apart, whose type, value or
  proof mentions a closed constant of the library, with those constants. A projection written as a
  number counts as the field it projects to.

Which line declares a constant is Lean's own record (the declaration ranges it keeps for editors),
read from the library's .olean files. A constant Lean made itself (a recursor, a matcher, an equation)
has none and goes with the declaration its name extends.

Nothing here is trusted by the Lean acceptance service; it reads what the service compiled.
-/
import Lean
open Lean

namespace InspectOleans

/-- What the protected module's name is replaced by. -/
def marker : Name := `Protected ++ `_

/-- `<protected module>.rest` becomes `Protected._.rest`; every other name stays. -/
def normName (prot : Option Name) (n : Name) : Name :=
  match prot with
  | some p => if p.isPrefixOf n then n.replacePrefix p marker else n
  | none => n

partial def lvl : Level → String
  | .zero => "0"
  | .succ l => s!"(s {lvl l})"
  | .max a b => s!"(m {lvl a} {lvl b})"
  | .imax a b => s!"(i {lvl a} {lvl b})"
  | .param n => s!"(p {n})"
  | .mvar _ => "?"

structure St where
  ids : Std.HashMap Expr Nat := {}
  out : Array String := #[]

/-- One line per distinct subterm, children before parents; returns the subterm's line number. -/
partial def ser (prot : Option Name) (e : Expr) : StateM St Nat := do
  if let .mdata _ b := e then return (← ser prot b)
  if let some i := (← get).ids[e]? then return i
  let line ← match e with
    | .bvar i => pure s!"b {i}"
    | .sort l => pure s!"s {lvl l}"
    | .const n ls => pure s!"c {normName prot n} {ls.map lvl}"
    | .app f a => do let i ← ser prot f; let j ← ser prot a; pure s!"a {i} {j}"
    | .lam _ t b _ => do let i ← ser prot t; let j ← ser prot b; pure s!"l {i} {j}"
    | .forallE _ t b _ => do let i ← ser prot t; let j ← ser prot b; pure s!"p {i} {j}"
    | .letE _ t v b _ => do let i ← ser prot t; let j ← ser prot v; let k ← ser prot b; pure s!"z {i} {j} {k}"
    | .lit (.natVal n) => pure s!"n {n}"
    | .lit (.strVal s) => pure s!"t {repr s}"
    | .proj s i b => do let j ← ser prot b; pure s!"j {normName prot s} {i} {j}"
    | .fvar id => pure s!"f {id.name}"
    | .mvar id => pure s!"v {id.name}"
    | .mdata _ _ => pure "unreachable"
  let st ← get
  let i := st.out.size
  set { st with ids := st.ids.insert e i, out := st.out.push line }
  return i

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def hints : ReducibilityHints → String
  | .opaque => "opaque" | .abbrev => "abbrev" | .regular h => s!"regular {h}"

/-- The constants a constant's kernel terms mention: its type; a definition's value (not a theorem's
    proof); an inductive type's constructors; a constructor's type; a recursor's rules. -/
def deps (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => fromType ++ v.value.getUsedConstants
  | .opaqueInfo v => fromType ++ v.value.getUsedConstants
  | .inductInfo v => fromType ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => fromType.push v.induct
  | .recInfo v => v.rules.foldl (fun acc r => acc ++ r.rhs.getUsedConstants |>.push r.ctor) (fromType ++ v.all.toArray)
  | _ => fromType

/-- The constants of `consts` that `root` depends on, itself included. -/
partial def closureOf (consts : Std.HashMap Name ConstantInfo) (root : Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    match consts[n]? with
    | none => continue
    | some ci =>
      seen := seen.insert n
      for d in deps ci do
        if !seen.contains d then todo := todo.push d
  return seen.toArray

/-- The canonical text of one constant: a header, its type, and what its kind adds. -/
def constText (prot : Option Name) (ci : ConstantInfo) : String :=
  let norm := normName prot
  let emit (s : String) : StateM St Unit := modify fun st => { st with out := st.out.push s }
  let go : StateM St Unit := do
    emit s!"K {norm ci.name} {kind ci} {ci.levelParams}"
    emit s!"T {← ser prot ci.type}"
    match ci with
    | .defnInfo v => emit s!"V {← ser prot v.value} {repr v.safety} {hints v.hints}"
    | .opaqueInfo v => emit s!"V {← ser prot v.value} unsafe={v.isUnsafe}"
    | .thmInfo _ => emit "V proof"
    | .inductInfo v =>
      emit s!"I {v.numParams} {v.numIndices} {v.all.map norm} {v.ctors.map norm} rec={v.isRec} unsafe={v.isUnsafe} nested={v.numNested} reflexive={v.isReflexive}"
    | .ctorInfo v => emit s!"C {norm v.induct} {v.cidx} {v.numParams} {v.numFields} unsafe={v.isUnsafe}"
    | .recInfo v =>
      emit s!"R {v.all.map norm} {v.numParams} {v.numIndices} {v.numMotives} {v.numMinors} k={v.k} unsafe={v.isUnsafe}"
      for r in v.rules do
        emit s!"r {norm r.ctor} {r.nfields} {← ser prot r.rhs}"
    | _ => emit "V none"
  let (_, st) := go.run {}
  "\n".intercalate st.out.toList

/-! ## What a run shows of the library -/

/-- The declaration ranges a module's .olean holds: per constant that was written in the source,
    where. They are the entries of `Lean.declRangeExt`, which a file outside the module system
    exports whole (`mkModuleData`); their type is that extension's entry type. -/
unsafe def declRangesImpl (data : ModuleData) : Array (Name × DeclarationRanges) :=
  match data.entries.find? (fun e => e.1 == `Lean.declRangeExt) with
  | some (_, es) => unsafeCast es
  | none => #[]

@[implemented_by declRangesImpl]
opaque declRanges (data : ModuleData) : Array (Name × DeclarationRanges)

/-- What a run shows of one module: all of it, or these lines of its source. -/
inductive Shown where
  | whole
  | lines (ls : Std.HashSet Nat)

structure Library where
  /-- Every constant of the library's modules. -/
  consts : Std.HashMap Name ConstantInfo := {}
  /-- The modules that declare a constant (one, unless two modules declare the same name). -/
  homes : Std.HashMap Name (Array String) := {}
  /-- Per module, the line on which a constant's name is declared, for the constants that have one. -/
  lines : Std.HashMap String (Std.HashMap Name Nat) := {}
  shown : Std.HashMap String Shown := {}

/-- The line that declares `n` in module `m`: its own, or that of the nearest declaration its name
    extends (`f.match_1`, `S.rec` and `S.mk.injEq` go with `f`, `S` and `S.mk`). A private name is
    also looked up as the name the user wrote. -/
def Library.lineOf (lib : Library) (m : String) (n : Name) : Option Nat := Id.run do
  let some ls := lib.lines[m]? | return none
  for start in [n, (privateToUserName? n).getD n] do
    let mut p := start
    while !p.isAnonymous do
      if let some l := ls[p]? then return some l
      p := p.getPrefix
  return none

/-- Whether module `m` shows constant `n`. A constant with no declared line at all (an instance Lean
    derived, say) counts as shown: it is nothing a person wrote. -/
def Library.showsIn (lib : Library) (m : String) (n : Name) : Bool :=
  match lib.shown[m]? with
  | none => false
  | some .whole => true
  | some (.lines ls) =>
    match lib.lineOf m n with
    | some l => ls.contains l
    | none => true

/-- Whether the run shows the library constant `n`: every module that declares it does. -/
def Library.shows (lib : Library) (n : Name) : Bool :=
  match lib.homes[n]? with
  | some ms => ms.all fun m => lib.showsIn m n
  | none => false

/-- The projection function of field `i` of the library structure `s`, by the constructor's binders. -/
def Library.fieldOf (lib : Library) (s : Name) (i : Nat) : Option Name := do
  let .inductInfo v ← lib.consts[s]? | none
  let [c] := v.ctors | none
  let ci ← lib.consts[c]?
  let rec go (t : Expr) (k : Nat) : Option Name :=
    match t, k with
    | .forallE n _ _ _, 0 => some (s ++ n)
    | .forallE _ _ b _, k + 1 => go b k
    | _, _ => none
  go ci.type (v.numParams + i)

/-- Every term of a constant: its type, the value of a definition, the proof of a theorem, the rules
    of a recursor. -/
def allTerms (ci : ConstantInfo) : Array Expr :=
  match ci with
  | .defnInfo v => #[ci.type, v.value]
  | .thmInfo v => #[ci.type, v.value]
  | .opaqueInfo v => #[ci.type, v.value]
  | .recInfo v => v.rules.foldl (fun acc r => acc.push r.rhs) #[ci.type]
  | _ => #[ci.type]

/-- The closed constants of the library that `ci` mentions (`closed` decides), projections included. -/
def closedUses (lib : Library) (closed : Name → Bool) (ci : ConstantInfo) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for e in allTerms ci do
    for n in e.getUsedConstants do
      if closed n && !out.contains n then out := out.push n
    -- a projection by number names no constant: find one that reaches a closed field
    let hit := e.find? fun x => match x with
      | .proj s i _ => match lib.fieldOf s i with
        | some f => closed f
        | none => false
      | _ => false
    if let some (.proj s i _) := hit then
      if let some f := lib.fieldOf s i then
        if !out.contains f then out := out.push f
  return out

def strs (xs : Array String) : Json := Json.arr (xs.map Json.str)

def run (args : List String) : IO UInt32 := do
  let mut oleans : Array (String × String) := #[]
  let mut prot : Option Name := none
  let mut wheres : Array Name := #[]
  let mut closures : Array Name := #[]
  let mut library : Array (String × String) := #[]
  let mut shownSpec : Array (String × Shown) := #[]
  let mut classify : Array Name := #[]
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--olean" :: spec :: more =>
      match spec.splitOn "=" with
      | m :: f :: more => oleans := oleans.push (m, "=".intercalate (f :: more))  -- a path may hold `=`
      | _ => IO.eprintln s!"--olean takes <module>=<file>, not {spec}"; return 2
      rest := more
    | "--protected" :: n :: more => prot := some n.toName; rest := more
    | "--where" :: n :: more => wheres := wheres.push n.toName; rest := more
    | "--closure" :: n :: more => closures := closures.push n.toName; rest := more
    | "--library" :: spec :: more =>
      match spec.splitOn "=" with
      | m :: f :: more => library := library.push (m, "=".intercalate (f :: more))
      | _ => IO.eprintln s!"--library takes <module>=<file>, not {spec}"; return 2
      rest := more
    | "--shown-whole" :: m :: more => shownSpec := shownSpec.push (m, .whole); rest := more
    | "--shown-lines" :: spec :: more =>
      match spec.splitOn "=" with
      | [m, ls] =>
        let nums := (ls.splitOn ",").filterMap fun x => x.toNat?
        shownSpec := shownSpec.push (m, .lines (nums.foldl (fun acc l => acc.insert l) {}))
      | _ => IO.eprintln s!"--shown-lines takes <module>=<line>,<line>,..., not {spec}"; return 2
      rest := more
    | "--classify" :: n :: more => classify := classify.push n.toName; rest := more
    | other :: _ => IO.eprintln s!"unknown argument {other}"; return 2
    | [] => pure ()
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut home : Std.HashMap Name (Array String) := {}
  let mut modules : Array (String × Json) := #[]
  let mut twice : Array Name := #[]
  let mut reserved : Array Name := #[]
  for (m, f) in oleans do
    let (data, _region) ← readModuleData f
    modules := modules.push (m, Json.mkObj [
      ("imports", strs (data.imports.map fun i => i.module.toString)),
      ("constants", Json.num data.constants.size),
      ("is_module", Json.bool data.isModule)])
    for ci in data.constants do
      if consts.contains ci.name && !twice.contains ci.name then twice := twice.push ci.name
      if marker.isPrefixOf ci.name then reserved := reserved.push ci.name
      consts := consts.insert ci.name ci
      home := home.insert ci.name ((home.getD ci.name #[]).push m)
  let byName (a b : Name) : Bool := a.toString < b.toString
  let duplicates := (twice.qsort byName).map fun n => Json.mkObj [("name", Json.str n.toString), ("modules", strs (home.getD n #[]))]
  let whereJson := wheres.map fun n => (n.toString, strs (home.getD n #[]))
  let mut closureJson : Array (String × Json) := #[]
  for root in closures do
    let names := (closureOf consts root).qsort fun a b => byName (normName prot a) (normName prot b)
    let entries := names.filterMap fun n => (consts[n]?).map fun ci => Json.mkObj [
      ("name", Json.str (normName prot n).toString), ("declared", Json.str n.toString),
      ("modules", strs (home.getD n #[])), ("kind", Json.str (kind ci)), ("text", Json.str (constText prot ci))]
    closureJson := closureJson.push (root.toString, Json.mkObj [
      ("found", Json.bool (consts.contains root)), ("constants", Json.arr entries)])
  -- what the run shows of the library, and what the given modules use beyond it
  let mut surface : List (String × Json) := []
  if !library.isEmpty then
    let mut libConsts : Std.HashMap Name ConstantInfo := {}
    let mut libHomes : Std.HashMap Name (Array String) := {}
    let mut libLines : Std.HashMap String (Std.HashMap Name Nat) := {}
    for (m, f) in library do
      let (data, _region) ← readModuleData f
      if data.isModule then
        IO.eprintln s!"{m} is written in the module system: its .olean does not say where its constants are declared"
        return 3
      let ranges := declRanges data
      let own : Std.HashSet Name := data.constants.foldl (fun acc ci => acc.insert ci.name) {}
      if !ranges.isEmpty && !(ranges.any fun r => own.contains r.1) then
        IO.eprintln s!"the declaration ranges of {m} name none of its constants: they were not read as what they are"
        return 3
      libLines := libLines.insert m (ranges.foldl (fun acc r => acc.insert r.1 r.2.selectionRange.pos.line) {})
      for ci in data.constants do
        libConsts := libConsts.insert ci.name ci
        libHomes := libHomes.insert ci.name ((libHomes.getD ci.name #[]).push m)
    let lib : Library := { consts := libConsts, homes := libHomes, lines := libLines,
                           shown := shownSpec.foldl (fun acc (m, sh) => acc.insert m sh) {} }
    let shownSet : Std.HashSet Name := lib.homes.fold (fun acc n _ => if lib.shows n then acc.insert n else acc) {}
    let mut exposed : Std.HashSet Name := {}
    for n in shownSet do
      if let some ci := lib.consts[n]? then
        for d in deps ci do
          if lib.homes.contains d && !shownSet.contains d then exposed := exposed.insert d
    let closed (n : Name) : Bool := lib.homes.contains n && !shownSet.contains n && !exposed.contains n
    let classes := classify.map fun n =>
      (n.toString, Json.str (if !lib.homes.contains n then "absent" else if shownSet.contains n then "shown"
        else if exposed.contains n then "exposed" else "closed"))
    let mut uses : Array Json := #[]
    for (m, f) in oleans do
      if prot == some m.toName then continue
      let (data, _region) ← readModuleData f
      for ci in data.constants do
        let found := (closedUses lib closed ci).qsort byName
        if !found.isEmpty then
          uses := uses.push (Json.mkObj [("constant", Json.str ci.name.toString), ("module", Json.str m),
            ("kind", Json.str (kind ci)), ("closed", strs (found.map (·.toString)))])
    surface := [("surface", Json.mkObj [
      ("library", Json.mkObj [("modules", Json.num library.size), ("constants", Json.num lib.homes.size),
        ("shown", Json.num shownSet.size), ("exposed", strs ((exposed.toArray.qsort byName).map (·.toString)))]),
      ("classes", Json.mkObj classes.toList), ("uses", Json.arr uses)])]
  IO.println (Json.mkObj ([
    ("modules", Json.mkObj modules.toList), ("duplicates", Json.arr duplicates),
    ("reserved", strs ((reserved.qsort byName).map (·.toString))),
    ("where", Json.mkObj whereJson.toList), ("closures", Json.mkObj closureJson.toList)] ++ surface)).compress
  return 0

end InspectOleans

def main (args : List String) : IO UInt32 := InspectOleans.run args
