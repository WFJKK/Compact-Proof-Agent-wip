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

def strs (xs : Array String) : Json := Json.arr (xs.map Json.str)

def run (args : List String) : IO UInt32 := do
  let mut oleans : Array (String × String) := #[]
  let mut prot : Option Name := none
  let mut wheres : Array Name := #[]
  let mut closures : Array Name := #[]
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
  IO.println (Json.mkObj [
    ("modules", Json.mkObj modules.toList), ("duplicates", Json.arr duplicates),
    ("reserved", strs ((reserved.qsort byName).map (·.toString))),
    ("where", Json.mkObj whereJson.toList), ("closures", Json.mkObj closureJson.toList)]).compress
  return 0

end InspectOleans

def main (args : List String) : IO UInt32 := InspectOleans.run args
