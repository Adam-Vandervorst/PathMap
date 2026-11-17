import Lean

/-!
# Export `PrunedModel/Zippy.lean`'s equational laws as Rust

Run from this directory:

    lake env lean --run ZippyLaws.lean > ../differential/src/algebraic/zippy_laws.rs

The program imports the *elaborated* module `PrunedModel.Zippy` and walks its
theorems.  A theorem is exported when every binder is a space, a path or a
byte, or a hypothesis of a supported shape (`≠` on paths or bytes, `∈`/`∉`, `=`
on spaces); its conclusion is an equation of spaces; both sides are built from
the operator vocabulary below; and its proof uses no `sorryAx`.  Everything else
is listed at the end of the output with the reason it was not exported.

Terms are translated by their application head and never unfolded: the point is
to emit the operator the theorem names.
-/

open Lean Meta

namespace ZippyLaws

def zippyNs : Name := `PrunedModel.Zippy
def zippyModule : Name := `PrunedModel.Zippy

inductive VarKind | space | path | byte
  deriving BEq

structure St where
  vars : Std.HashMap FVarId (VarKind × Nat) := {}
  nSpace : Nat := 0
  nPath : Nat := 0
  nByte : Nat := 0

abbrev M := StateT St (ExceptT String MetaM)

def fail {α} (msg : String) : M α := throwThe String msg

def liftMeta {α} (x : MetaM α) : M α := monadLift x

def clean (e : Expr) : MetaM Expr := do
  return (← instantiateMVars e).consumeMData.headBeta

def spaceTy : Expr := mkConst `PrunedModel.Zippy.Space
def pathTy : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``UInt8)
def byteTy : Expr := mkConst ``UInt8

/-- Which variable kind a type is, if any.  Types are compared up to
definitional equality, so `Space`, `PrunedMap Unit`, `Path` and `List UInt8`
are all recognised. -/
def kindOf (ty : Expr) : MetaM (Option VarKind) := do
  let ty ← clean ty
  if ty.isSort then return none
  if ← isDefEq ty spaceTy then return some .space
  if ← isDefEq ty pathTy then return some .path
  if ← isDefEq ty byteTy then return some .byte
  return none

def headName (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => toString n
  | .fvar _ => "a local function"
  | .lam .. => "a lambda"
  | .proj s i _ => s!"projection {s}.{i}"
  | .letE .. => "a let"
  | .lit _ => "a literal"
  | f => s!"{f.ctorName}"

/-- What a space-typed term mentions that is outside the vocabulary. -/
def outside (e : Expr) : String := s!"mentions {headName e}"

def varOf (e : Expr) (k : VarKind) : M (Option Nat) := do
  match e with
  | .fvar id =>
      match (← get).vars.get? id with
      | some (k', i) => if k' == k then return some i else fail s!"variable of the wrong kind"
      | none => fail "unbound local"
  | _ => return none

def litByte (e : Expr) : M (Option Nat) := do
  -- `OfNat.ofNat UInt8 n inst`
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let ty ← liftMeta (clean (e.getArg! 0))
    if ty.isConstOf ``UInt8 then
      match (← liftMeta (clean (e.getArg! 1))) with
      | .lit (.natVal n) => return some (n % 256)
      | _ => return none
  return none

partial def byteTerm (e : Expr) : M String := do
  let e ← liftMeta (clean e)
  if let some i ← varOf e .byte then return s!"bv({i})"
  if let some n ← litByte e then return s!"lit({n})"
  fail s!"byte term {outside e}"

partial def pathTerm (e : Expr) : M String := do
  let e ← liftMeta (clean e)
  if let some i ← varOf e .path then return s!"pv({i})"
  if e.isAppOfArity ``List.nil 1 then return "nil()"
  if e.isAppOfArity ``List.cons 3 then
    return s!"cons({← byteTerm (e.getArg! 1)}, {← pathTerm (e.getArg! 2)})"
  if e.isAppOfArity ``HAppend.hAppend 6 then
    return s!"app({← pathTerm (e.getArg! 4)}, {← pathTerm (e.getArg! 5)})"
  if e.isAppOfArity ``List.append 3 then
    return s!"app({← pathTerm (e.getArg! 1)}, {← pathTerm (e.getArg! 2)})"
  fail s!"path term {outside e}"

/-- The space operators: Lean name, Rust builder, and the kind of each
explicit argument. -/
def ops : List (Name × String × List VarKind) :=
  [ (`PrunedModel.Zippy.empty, "empty", []),
    (`PrunedModel.Zippy.singleton, "singleton", [.path]),
    (`PrunedModel.Zippy.union, "union", [.space, .space]),
    (`PrunedModel.Zippy.inter, "inter", [.space, .space]),
    (`PrunedModel.Zippy.subtr, "subtr", [.space, .space]),
    (`PrunedModel.Zippy.restriction, "restriction", [.space, .space]),
    (`PrunedModel.Zippy.raffination, "raffination", [.space, .space]),
    (`PrunedModel.Zippy.wrap, "wrap", [.path, .space]),
    (`PrunedModel.Zippy.unwrap, "unwrap", [.space, .path]),
    (`PrunedModel.Zippy.head, "head", [.space]),
    (`PrunedModel.Zippy.tailsUnion, "tails_union", [.space]),
    (`PrunedModel.Zippy.tailsInter, "tails_inter", [.space]),
    (`PrunedModel.Zippy.composition, "composition", [.space, .space]),
    (`PrunedModel.Zippy.iterC, "iter_c", [.space, .space]) ]

mutual
partial def spaceTerm (e : Expr) : M String := do
  let e ← liftMeta (clean e)
  if let some i ← varOf e .space then return s!"s({i})"
  let .const f _ := e.getAppFn | fail s!"space term {outside e}"
  let some (_, rust, kinds) := ops.find? (·.1 == f) | fail (outside e)
  let args := e.getAppArgs
  unless args.size == kinds.length do
    fail s!"{f} applied to {args.size} arguments, expected {kinds.length}"
  let mut out := #[]
  for (a, k) in args.toList.zip kinds do
    out := out.push (← anyTerm a k)
  return s!"{rust}({", ".intercalate out.toList})"

partial def anyTerm (e : Expr) (k : VarKind) : M String :=
  match k with
  | .space => spaceTerm e
  | .path => pathTerm e
  | .byte => byteTerm e
end

/-- A hypothesis, as a precondition. -/
def hypothesis (ty : Expr) : M String := do
  let ty ← liftMeta (clean ty)
  -- `a ≠ b`
  if ty.isAppOfArity ``Ne 3 then
    match ← liftMeta (kindOf (ty.getArg! 0)) with
    | some .path => return s!"ne_path({← pathTerm (ty.getArg! 1)}, {← pathTerm (ty.getArg! 2)})"
    | some .byte => return s!"ne_byte({← byteTerm (ty.getArg! 1)}, {← byteTerm (ty.getArg! 2)})"
    | _ => fail "hypothesis is a disequation of neither paths nor bytes"
  -- `p ∈ s` is `@Membership.mem Path Space inst s p`: collection first.
  let memOf (m : Expr) : M (Option String) := do
    let m ← liftMeta (clean m)
    if m.isAppOfArity ``Membership.mem 5 then
      unless (← liftMeta (kindOf (m.getArg! 1))) == some .space do
        fail "hypothesis is membership in something other than a space"
      return some s!"{← pathTerm (m.getArg! 4)}, {← spaceTerm (m.getArg! 3)}"
    return none
  if let some s ← memOf ty then return s!"mem({s})"
  if ty.isAppOfArity ``Not 1 then
    if let some s ← memOf (ty.getArg! 0) then return s!"not_mem({s})"
    fail "hypothesis is a negation other than ∉"
  if ty.isAppOfArity ``Eq 3 then
    unless (← liftMeta (kindOf (ty.getArg! 0))) == some .space do
      fail "hypothesis is an equation not of spaces"
    return s!"eq_space({← spaceTerm (ty.getArg! 1)}, {← spaceTerm (ty.getArg! 2)})"
  if ty.isForall then fail "hypothesis is a ∀"
  fail s!"hypothesis {outside ty}"

structure Law where
  name : String
  spaces : Nat
  paths : Nat
  bytes : Nat
  pre : Array String
  lhs : String
  rhs : String

def conclusionShape (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ =>
      if n == ``Iff then "Iff" else if n == ``Ne then "Ne" else if n == ``Not then "¬"
      else if n == ``Eq then "an equation of another type" else toString n
  | _ => headName e

def translate (ty : Expr) : MetaM (Except String Law) := do
  -- `forallTelescope`, not `…Reducing`: a conclusion like `p ∉ s` must not be
  -- unfolded into another binder.
  forallTelescope ty fun xs body => do
    let go : M Law := do
      let mut pre := #[]
      for x in xs do
        let decl ← liftMeta x.fvarId!.getDecl
        let bty ← liftMeta (clean decl.type)
        match ← liftMeta (kindOf bty) with
        | some k =>
            let st ← get
            let (i, st') := match k with
              | .space => (st.nSpace, { st with nSpace := st.nSpace + 1 })
              | .path => (st.nPath, { st with nPath := st.nPath + 1 })
              | .byte => (st.nByte, { st with nByte := st.nByte + 1 })
            set { st' with vars := st'.vars.insert x.fvarId! (k, i) }
        | none =>
            if ← liftMeta (isProp bty) then
              pre := pre.push (← hypothesis bty)
            else
              fail s!"binder {decl.userName} : {← liftMeta (ppExpr bty)}"
      let body ← liftMeta (clean body)
      unless body.isAppOfArity ``Eq 3 do
        fail s!"conclusion is not an equation of spaces ({conclusionShape body})"
      unless (← liftMeta (kindOf (body.getArg! 0))) == some .space do
        fail s!"conclusion is not an equation of spaces (equation of {← liftMeta (ppExpr (body.getArg! 0))})"
      let lhs ← spaceTerm (body.getArg! 1)
      let rhs ← spaceTerm (body.getArg! 2)
      let st ← get
      return { name := "", spaces := st.nSpace, paths := st.nPath, bytes := st.nByte,
               pre, lhs, rhs }
    match ← (go.run' {}).run with
    | .ok l => return .ok l
    | .error e => return .error e

def relName (n : Name) : String :=
  let comps := n.components.drop zippyNs.components.length
  ".".intercalate (comps.map toString)

def skipName (env : Environment) (n : Name) : Bool :=
  n.isInternal || isPrivateName n || isAuxRecursor env n || isNoConfusion env n ||
  isMatcherCore env n || isRecCore env n ||
  n.components.any fun c =>
    let s := toString c
    s == "eq_def" || s.startsWith "eq_" || s.startsWith "match_" || s.startsWith "proof_" ||
      (s.splitOn "_proof_").length > 1 || s.startsWith "_" || s == "inj" || s == "injEq" ||
      s == "sizeOf_spec"

inductive Outcome
  | law (l : Law)
  | skip (reason : String)

def run : MetaM String := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? zippyModule | throwError "{zippyModule} not imported"
  let mut entries : Array (Nat × String × Outcome) := #[]
  for (n, ci) in env.constants.toList do
    unless zippyNs.isPrefixOf n && n != zippyNs do continue
    unless env.getModuleIdxFor? n == some modIdx do continue
    let .thmInfo info := ci | continue
    if skipName env n then continue
    let line := match ← findDeclarationRanges? n with
      | some r => r.selectionRange.pos.line
      | none => 0
    let name := relName n
    let axioms ← collectAxioms n
    let outcome ←
      if axioms.contains ``sorryAx then pure (.skip "depends on sorryAx")
      else match ← translate info.type with
        | .error e => pure (.skip e)
        | .ok l =>
            if l.spaces > 4 then pure (.skip s!"{l.spaces} space variables (more than 4)")
            else if l.lhs == l.rhs then pure (.skip "both sides translate to the same term")
            else pure (.law { l with name })
    entries := entries.push (line, name, outcome)
  entries := entries.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let laws := entries.filterMap fun
    | (line, _, .law l) => some (line, l)
    | _ => none
  let skips := entries.filterMap fun
    | (line, name, .skip r) => some (line, name, r)
    | _ => none
  let mut out := ""
  out := out ++ "// @generated by lean/ZippyLaws.lean from lean/PrunedModel/Zippy.lean.\n"
  out := out ++ "// Do not edit by hand.  Regenerate with:\n"
  out := out ++ "//   cd lean && lake env lean --run ZippyLaws.lean > ../differential/src/algebraic/zippy_laws.rs\n"
  out := out ++ "//\n"
  out := out ++ "// Every entry is a theorem of PrunedModel.Zippy, checked sorry-free when generated.\n"
  out := out ++ s!"// {laws.size} exported, {skips.size} not exported (listed at the end).\n"
  out := out ++ "\n"
  out := out ++ "use super::laws::zippy::*;\n"
  out := out ++ "\n"
  out := out ++ "pub fn laws() -> Vec<ZippyLaw> {\n"
  out := out ++ "    vec![\n"
  for (line, l) in laws do
    out := out ++ s!"        // Zippy.lean:{line}\n"
    out := out ++ "        ZippyLaw {\n"
    out := out ++ s!"            name: \"{l.name}\",\n"
    out := out ++ s!"            spaces: {l.spaces},\n"
    out := out ++ s!"            paths: {l.paths},\n"
    out := out ++ s!"            bytes: {l.bytes},\n"
    out := out ++ s!"            pre: vec![{", ".intercalate l.pre.toList}],\n"
    out := out ++ s!"            lhs: {l.lhs},\n"
    out := out ++ s!"            rhs: {l.rhs},\n"
    out := out ++ "        },\n"
  out := out ++ "    ]\n"
  out := out ++ "}\n"
  out := out ++ "\n"
  out := out ++ "// Not exported:\n"
  for (line, name, r) in skips do
    out := out ++ s!"//   Zippy.lean:{line} {name}: {r}\n"
  return out

end ZippyLaws

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `PrunedModel.Zippy }] {} (trustLevel := 1024)
  let (out, _) ← (ZippyLaws.run.run' {} {}).toIO
    { fileName := "<ZippyLaws>", fileMap := default, maxHeartbeats := 0 } { env := env }
  IO.print out
