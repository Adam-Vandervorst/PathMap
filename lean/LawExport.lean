import Lean

/-!
Shared exporter for `ZippyLaws.lean` and `PathSetLaws.lean`.

Read elaborated theorem types, preserve supported hypotheses, and reject proofs
that depend on `sorryAx`. Operators are translated by application head; only
finite-space literals and coercions are reduced. Path-set mode also recognizes
extensional equations and their finite-set predicates. Unsupported theorems
are listed with source locations and reasons in the generated output.
-/

open Lean Meta

namespace LawExport

inductive VarKind | space | path | byte
  deriving BEq

structure Config where
  ns : Name
  module : Name
  submodules : Bool := false
  generator : String
  output : String
  namePrefix : String := ""
  ops : List (Name × String × List VarKind)
  pathSets : Bool := false

structure St where
  config : Config

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
def zippyOps : List (Name × String × List VarKind) :=
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
  if (← get).config.pathSets then
    if e.isAppOfArity `PrunedModel.Convex.ofPaths 1 then
      return ← spaceList (e.getArg! 0)
    if e.isAppOf ``Coe.coe || e.isAppOf ``CoeT.coe || e.isAppOf ``CoeHTCT.coe then
      return ← spaceTerm (← liftMeta (whnf e))
    if e.isAppOfArity ``HAppend.hAppend 6 then
      return s!"union({← spaceTerm (e.getArg! 4)}, {← spaceTerm (e.getArg! 5)})"
  let .const f _ := e.getAppFn | fail s!"space term {outside e}"
  let some (_, rust, kinds) := (← get).config.ops.find? (·.1 == f) | fail (outside e)
  let args := e.getAppArgs
  unless args.size == kinds.length do
    fail s!"{f} applied to {args.size} arguments, expected {kinds.length}"
  let mut out := #[]
  for (a, k) in args.toList.zip kinds do
    out := out.push (← anyTerm a k)
  return s!"{rust}({", ".intercalate out.toList})"

partial def spaceList (e : Expr) : M String := do
  let e ← liftMeta (clean e)
  if e.isAppOfArity ``List.nil 1 then return "empty()"
  if e.isAppOfArity ``List.cons 3 then
    let p ← pathTerm (e.getArg! 1)
    let tail ← liftMeta (clean (e.getArg! 2))
    if tail.isAppOfArity ``List.nil 1 then return s!"singleton({p})"
    return s!"union(singleton({p}), {← spaceList tail})"
  fail s!"space literal {outside e}"

partial def anyTerm (e : Expr) (k : VarKind) : M String :=
  match k with
  | .space => spaceTerm e
  | .path => pathTerm e
  | .byte => byteTerm e
end

/-- Translate a membership formula at an arbitrary path back to its space.
Only finite-set connectives are accepted. In particular, a space mentioning
that path cannot be lifted out of the quantifier. -/
partial def membershipSpace (e p : Expr) : MetaM (Option Expr) := do
  let e ← clean e
  if e.isAppOfArity ``Membership.mem 5 then
    if e.getArg! 4 == p then
      let a := e.getArg! 3
      if (← kindOf (e.getArg! 1)) == some .space && !a.containsFVar p.fvarId! then
        return some a
  if e.isConstOf ``False then return some (mkConst `PrunedModel.Zippy.empty)
  if e.isAppOfArity ``Eq 3 then
    unless (← kindOf (e.getArg! 0)) == some .path do return none
    let a := e.getArg! 1
    let b := e.getArg! 2
    let q := if a == p then b else if b == p then a else p
    if !q.containsFVar p.fvarId! then
      return some (mkApp (mkConst `PrunedModel.Zippy.singleton) q)
  if e.isAppOfArity ``Or 2 || e.isAppOfArity ``And 2 then
    let some a ← membershipSpace (e.getArg! 0) p | return none
    let rhs ← clean (e.getArg! 1)
    let neg := e.isAppOf ``And && rhs.isAppOfArity ``Not 1
    let some b ← membershipSpace (if neg then rhs.getArg! 0 else rhs) p | return none
    let op := if neg then `PrunedModel.Zippy.subtr
      else if e.isAppOf ``And then `PrunedModel.Zippy.inter else `PrunedModel.Zippy.union
    return some (mkApp2 (mkConst op) a b)
  return none

/-- Extensional lifting is valid only when the quantified path is unrestricted:
no other binder (including hypotheses) may depend on it. -/
def pointwiseEquation (xs : Array Expr) (body : Expr) : MetaM (Option (FVarId × Expr × Expr)) := do
  unless body.isAppOfArity ``Iff 2 do return none
  for p in xs do
    unless (← kindOf (← inferType p)) == some .path do continue
    if ← xs.anyM (fun x => return (← inferType x).containsFVar p.fvarId!) then continue
    let some a ← membershipSpace (body.getArg! 0) p | continue
    let some b ← membershipSpace (body.getArg! 1) p | continue
    return some (p.fvarId!, a, b)
  return none

/-- Supported extensional relations, represented as equations of finite sets.
These are exact equivalences, so the same translation works for hypotheses. -/
def relation (ty : Expr) : M (Option (String × String)) := do
  let ty ← liftMeta (clean ty)
  if ty.isAppOfArity `PrunedModel.Convex.Same 2 then
    return some (← spaceTerm (ty.getArg! 0), ← spaceTerm (ty.getArg! 1))
  if ty.isAppOfArity `PrunedModel.Convex.Included 2 then
    let a ← spaceTerm (ty.getArg! 0)
    let b ← spaceTerm (ty.getArg! 1)
    return some (s!"inter({a}, {b})", a)
  if ty.isAppOfArity `PrunedModel.Convex.Antichain 1 then
    let a ← spaceTerm (ty.getArg! 0)
    return some (s!"basis({a})", a)
  if ty.isAppOfArity `PrunedModel.Convex.IsClosed 1 then
    let a ← spaceTerm (ty.getArg! 0)
    return some (s!"completion({a})", a)
  if ty.isAppOfArity ``Eq 3 then
    unless (ty.getArg! 2).isConstOf ``Bool.true do return none
    let t ← liftMeta (clean (ty.getArg! 1))
    if t.isAppOfArity `PrunedModel.Convex.equiv 2 then
      return some (← spaceTerm (t.getArg! 0), ← spaceTerm (t.getArg! 1))
    if t.isAppOfArity `PrunedModel.Convex.subset 2 then
      let a ← spaceTerm (t.getArg! 0)
      let b ← spaceTerm (t.getArg! 1)
      return some (s!"inter({a}, {b})", a)
    if t.isAppOfArity `PrunedModel.Convex.covers 2 then
      let a ← spaceTerm (t.getArg! 0)
      let b ← spaceTerm (t.getArg! 1)
      return some (s!"retain({a}, {b})", a)
    if t.isAppOfArity `PrunedModel.Convex.prefixFree 1 then
      let a ← spaceTerm (t.getArg! 0)
      return some (s!"basis({a})", a)
  if ty.isForall then
    let pair ← liftMeta <| forallTelescope ty fun xs body => do
      return (← pointwiseEquation xs body).map fun (_, a, b) => (a, b)
    if let some (a, b) := pair then return some (← spaceTerm a, ← spaceTerm b)
  return none

/-- A hypothesis, as a precondition. -/
def hypothesis (ty : Expr) : M String := do
  let ty ← liftMeta (clean ty)
  if (← get).config.pathSets then
    if let some (a, b) ← relation ty then return s!"eq_space({a}, {b})"
    if ty.isAppOfArity ``Ne 3 then
      if (← liftMeta (kindOf (ty.getArg! 0))) == some .space then
        return s!"ne_space({← spaceTerm (ty.getArg! 1)}, {← spaceTerm (ty.getArg! 2)})"
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

def translate (config : Config) (ty : Expr) : MetaM (Except String Law) := do
  -- `forallTelescope`, not `…Reducing`: a conclusion like `p ∉ s` must not be
  -- unfolded into another binder.
  forallTelescope ty fun xs body => do
    let lifted ← if config.pathSets then pointwiseEquation xs body else pure none
    let go : M Law := do
      let mut pre := #[]
      for x in xs do
        if let some (id, _, _) := lifted then
          if x.fvarId! == id then continue
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
      let pair ← match lifted with
        | some (_, a, b) => pure (some (← spaceTerm a, ← spaceTerm b))
        | none => if config.pathSets then relation body else pure none
      let (lhs, rhs) ← match pair with
        | some p => pure p
        | none => do
            unless body.isAppOfArity ``Eq 3 do
              fail s!"conclusion is not an equation of spaces ({conclusionShape body})"
            unless (← liftMeta (kindOf (body.getArg! 0))) == some .space do
              fail s!"conclusion is not an equation of spaces (equation of {← liftMeta (ppExpr (body.getArg! 0))})"
            pure (← spaceTerm (body.getArg! 1), ← spaceTerm (body.getArg! 2))
      let st ← get
      return { name := "", spaces := st.nSpace, paths := st.nPath, bytes := st.nByte,
               pre, lhs, rhs }
    match ← (go.run' { config }).run with
    | .ok l => return .ok l
    | .error e => return .error e

def relName (config : Config) (n : Name) : String :=
  let comps := n.components.drop config.ns.components.length
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

def run (config : Config) : MetaM String := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? config.module | throwError "{config.module} not imported"
  let mut entries : Array (String × Nat × String × Outcome) := #[]
  for (n, ci) in env.constants.toList do
    unless config.ns.isPrefixOf n && n != config.ns do continue
    let some sourceIdx := env.getModuleIdxFor? n | continue
    let sourceModule := env.header.moduleNames[sourceIdx.toNat]!
    unless sourceIdx == modIdx || (config.submodules && config.module.isPrefixOf sourceModule) do continue
    let source := if config.submodules then
      "/".intercalate (sourceModule.components.map toString) ++ ".lean"
      else s!"{sourceModule.getString!}.lean"
    let .thmInfo info := ci | continue
    if skipName env n then continue
    let line := match ← findDeclarationRanges? n with
      | some r => r.selectionRange.pos.line
      | none => 0
    let name := config.namePrefix ++ relName config n
    let axioms ← collectAxioms n
    let outcome ←
      if axioms.contains ``sorryAx then pure (.skip "depends on sorryAx")
      else match ← translate config info.type with
        | .error e => pure (.skip e)
        | .ok l =>
            if l.spaces > 4 then pure (.skip s!"{l.spaces} space variables (more than 4)")
            else if l.lhs == l.rhs then pure (.skip "both sides translate to the same term")
            else pure (.law { l with name })
    entries := entries.push (source, line, name, outcome)
  entries := entries.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2.1 < b.2.2.1)))
  let laws := entries.filterMap fun
    | (source, line, _, .law l) => some (source, line, l)
    | _ => none
  let skips := entries.filterMap fun
    | (source, line, name, .skip r) => some (source, line, name, r)
    | _ => none
  let mut out := ""
  let origin := "/".intercalate (config.module.components.map toString)
  out := out ++ s!"// @generated by lean/{config.generator}.lean from lean/{origin}{if config.submodules then "/*.lean" else ".lean"}.\n"
  out := out ++ "// Do not edit by hand.  Regenerate with:\n"
  out := out ++ s!"//   cd lean && lake env lean --run {config.generator}.lean > ../differential/src/algebraic/{config.output}.rs\n"
  out := out ++ "//\n"
  out := out ++ s!"// Every entry is a theorem of {config.ns}, checked sorry-free when generated.\n"
  out := out ++ s!"// {laws.size} exported, {skips.size} not exported (listed at the end).\n"
  out := out ++ "\n"
  out := out ++ "use super::laws::zippy::*;\n"
  out := out ++ "\n"
  out := out ++ "pub fn laws() -> Vec<ZippyLaw> {\n"
  out := out ++ "    vec![\n"
  for (source, line, l) in laws do
    out := out ++ s!"        // {source}:{line}\n"
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
  for (source, line, name, r) in skips do
    out := out ++ s!"//   {source}:{line} {name}: {r}\n"
  return out

def generate (config : Config) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := config.module }] {} (trustLevel := 1024)
  let (out, _) ← ((run config).run' {} {}).toIO
    { fileName := s!"<{config.generator}>", fileMap := default, maxHeartbeats := 0 } { env }
  IO.print out

end LawExport
