import Mathlib.Init.Set
import Init.Data.List.Basic
import Init.Data.List.Control
import Std.Data.List.Basic
import Rinha.Term
import Std.Data.HashMap.Basic
import Mathlib.Data.Prod.Basic

open Std (HashMap)
open Std.HashMap.Imp

namespace Rinha.Type

open Rinha.Term

inductive Literal where
| int : Int → Literal
| bool : Bool → Literal
| string : String → Literal
deriving Repr, BEq, Inhabited

inductive T where
| int : T
| bool : T
| string : T
| func : List T → T → T
| var : String → T
| tuple : (T × T) → T
| oneOf : List T → T
deriving Repr, BEq, Inhabited

mutual
def decT (a b : T) : Decidable (a = b) :=
  match a, b with
  | T.int, T.int => isTrue rfl
  | T.bool, T.bool => isTrue rfl
  | T.string, T.string => isTrue rfl
  | T.var a, T.var b => match String.decEq a b with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  | T.func as ar, T.func bs br => match decTList as bs with
    | isTrue h => match decT ar br with
      | isTrue h₂ => isTrue (by rw [h, h₂])
      | isFalse _ => isFalse (by intro h₂; injection h₂; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  | T.tuple (a, b), T.tuple (c, d) =>
    match decTTuple (a, b) (c, d) with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  | T.oneOf as, T.oneOf bs => match decTList as bs with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  | T.int, T.bool => isFalse (by intro; contradiction)
  | T.int, T.string => isFalse (by intro; contradiction)
  | T.bool, T.int => isFalse (by intro; contradiction)
  | T.bool, T.string => isFalse (by intro; contradiction)
  | T.string, T.int => isFalse (by intro; contradiction)
  | T.string, T.bool => isFalse (by intro; contradiction)
  | T.var _, T.int => isFalse (by intro; contradiction)
  | T.var _, T.bool => isFalse (by intro; contradiction)
  | T.var _, T.string => isFalse (by intro; contradiction)
  | T.func _ _, T.int => isFalse (by intro; contradiction)
  | T.func _ _, T.bool => isFalse (by intro; contradiction)
  | T.func _ _, T.string => isFalse (by intro; contradiction)
  | T.tuple _, T.int => isFalse (by intro; contradiction)
  | T.tuple _, T.bool => isFalse (by intro; contradiction)
  | T.tuple _, T.string => isFalse (by intro; contradiction)
  | T.oneOf _, T.int => isFalse (by intro; contradiction)
  | T.oneOf _, T.bool => isFalse (by intro; contradiction)
  | T.oneOf _, T.string => isFalse (by intro; contradiction)
  | T.int, T.var _ => isFalse (by intro; contradiction)
  | T.bool, T.var _ => isFalse (by intro; contradiction)
  | T.string, T.var _ => isFalse (by intro; contradiction)
  | T.int, T.func _ _ => isFalse (by intro; contradiction)
  | T.bool, T.func _ _ => isFalse (by intro; contradiction)
  | T.string, T.func _ _ => isFalse (by intro; contradiction)
  | T.int, T.tuple _ => isFalse (by intro; contradiction)
  | T.bool, T.tuple _ => isFalse (by intro; contradiction)
  | T.string, T.tuple _ => isFalse (by intro; contradiction)
  | T.int, T.oneOf _ => isFalse (by intro; contradiction)
  | T.bool, T.oneOf _ => isFalse (by intro; contradiction)
  | T.string, T.oneOf _ => isFalse (by intro; contradiction)
  | T.func _ _, T.var _ => isFalse (by intro; contradiction)
  | T.tuple _, T.var _ => isFalse (by intro; contradiction)
  | T.oneOf _, T.var _ => isFalse (by intro; contradiction)
  | T.var _, T.func _ _ => isFalse (by intro; contradiction)
  | T.var _, T.tuple _ => isFalse (by intro; contradiction)
  | T.var _, T.oneOf _ => isFalse (by intro; contradiction)
  | T.oneOf _, T.tuple _ => isFalse (by intro; contradiction)
  | T.tuple _, T.oneOf _ => isFalse (by intro; contradiction)
  | T.oneOf _, T.func _ _ => isFalse (by intro; contradiction)
  | T.tuple _, T.func _ _ => isFalse (by intro; contradiction)
  | T.func _ _, T.oneOf _ => isFalse (by intro; contradiction)
  | T.func _ _, T.tuple _ => isFalse (by intro; contradiction)

def decTTuple (as bs : T × T) : Decidable (as = bs) :=
  match as, bs with
  | (a, b), (c, d) =>
    match decT a c with
    | isTrue h₁ =>
      match decT b d with
      | isTrue h₂  => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h₂; injection h₂; contradiction)
    | isFalse _ => isFalse (by intro h₁; injection h₁; contradiction)

def decTList (as bs : List T) : Decidable (as = bs) :=
  match as, bs with
  | [], [] => isTrue rfl
  | _::_, [] => isFalse (by intro; contradiction)
  | [], _::_ => isFalse (by intro; contradiction)
  | a::as, b::bs =>
    match decT a b with
    | isTrue h₁ => match decTList as bs with
      | isTrue h₂ => isTrue (by rw [h₁, h₂])
      | isFalse _ => isFalse (by intro h; injection h; contradiction)
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

end

instance : DecidableEq T :=
  decT

def T.combine : T → T → T
| T.oneOf xs, T.oneOf ys => T.oneOf (List.union xs ys)
| T.oneOf xs, y => T.oneOf (List.union [y] xs)
| x, T.oneOf ys => T.oneOf (List.union [x] ys)
| x, y => if x == y then x else T.oneOf [x, y]

def T.remove : T → T → T
| T.oneOf xs, T.oneOf ys => T.oneOf (List.diff xs ys)
| T.oneOf xs, y =>
  match List.diff xs [y] with
  | [] => T.oneOf []
  | [x] => x
  | xs => T.oneOf xs
| x, T.oneOf ys =>
  match List.diff ys [x] with
  | [] => T.oneOf []
  | [y] => y
  | ys => T.oneOf ys
| T.func args x, y => T.func args (x.remove y)
| x, _ => x

structure TypedBinOp where
  op : BinOp
  left : T
  right : T
  result : T
deriving Repr, BEq

def TypedBinOp.ofBinOp : BinOp → TypedBinOp
| BinOp.Add => { op := BinOp.Add, left := T.oneOf [T.int, T.string], right := T.oneOf [T.int, T.string], result := T.oneOf [T.int, T.string] }
| BinOp.Sub => { op := BinOp.Sub, left := T.int, right := T.int, result := T.int }
| BinOp.Mul => { op := BinOp.Mul, left := T.int, right := T.int, result := T.int }
| BinOp.Div => { op := BinOp.Div, left := T.int, right := T.int, result := T.int }
| BinOp.Rem => { op := BinOp.Rem, left := T.int, right := T.int, result := T.int }
| BinOp.Eq => { op := BinOp.Eq, left := T.var "β", right := T.var "β", result := T.bool }
| BinOp.Neq => { op := BinOp.Neq, left := T.var "β", right := T.var "β", result := T.bool }
| BinOp.Lt => { op := BinOp.Lt, left := T.int, right := T.int, result := T.bool }
| BinOp.Lte => { op := BinOp.Lte, left := T.int, right := T.int, result := T.bool }
| BinOp.Gt => { op := BinOp.Gt, left := T.int, right := T.int, result := T.bool }
| BinOp.Gte => { op := BinOp.Gte, left := T.int, right := T.int, result := T.bool }
| BinOp.And => { op := BinOp.And, left := T.bool, right := T.bool, result := T.bool }
| BinOp.Or => { op := BinOp.Or, left := T.bool, right := T.bool, result := T.bool }

partial def T.toString : T → String
| T.int => "int"
| T.bool => "bool"
| T.string => "string"
| T.func args ret => s!"({args.map toString} -> {toString ret})"
| T.var x => x
| T.tuple (a, b) => s!"({toString a}, {toString b})"
| T.oneOf ts => s!"({ts.map toString})"

instance : ToString T where
  toString := T.toString

inductive Scheme where
| scheme : List String → T → Scheme
deriving Repr, BEq

abbrev Subst := HashMap String T

class Types (α : Type) where
  ftv : α → List String
  apply : Subst → α → α

partial def T.ftv : T → List String
| T.var x => [x]
| T.bool => {}
| T.int => {}
| T.string => {}
| T.oneOf ts => ts.foldl (λ x y => List.union x (ftv y)) {}
| T.func args ret => (args.foldl (λ x y => List.union x (ftv y)) (ftv ret))
| T.tuple (x, y) => List.union x.ftv y.ftv

partial def T.apply : Subst → T → T
| s, T.var x => match s.find? x with
  | some t => t
  | none => T.var x
| s, (T.func args ret) => T.func (args.map (apply s)) (apply s ret)
| _, t => t

instance : Types T := ⟨T.ftv, T.apply⟩

def Scheme.ftv : Scheme → List String
| Scheme.scheme vars t => t.ftv.diff vars

def Scheme.apply : Subst → Scheme → Scheme
| s, Scheme.scheme vars t => Scheme.scheme vars (t.apply (vars.foldr (flip Std.HashMap.erase) s))

instance : Types Scheme := ⟨Scheme.ftv, Scheme.apply⟩

def List.ftv {α : Type} [Types α] : List α → List String :=
 List.foldr List.union {} ∘ List.map Types.ftv

def List.apply {α : Type} [Types α] (s : Subst) : List α → List α :=
  List.map (Types.apply s)

instance [Types α] : Types (List α) := ⟨List.ftv, List.apply⟩

def nullSubst : Subst := {}

def Subst.map (f : α → β) [BEq γ] [Hashable γ] : (x : Std.HashMap γ α) → Std.HashMap γ β :=
 Std.HashMap.ofList ∘ List.map (Prod.map id f) ∘ Std.HashMap.toList

def Subst.compose (s₁ s₂ : Subst) : Subst :=
  let s₃ := Subst.map (λ t => t.apply s₁) s₂
  Std.HashMap.fold (Std.HashMap.insert) s₃ s₁

def Subst.composeMany : List Subst → Subst := List.foldl Subst.compose nullSubst

instance : Repr Subst where
  reprPrec n := reprPrec n.toList

structure TypeEnv where
  vars : Std.HashMap String Scheme

def Std.HashMap.elems [BEq α] [Hashable α] : Std.HashMap α β → List β := Std.HashMap.fold (λ x _ z => z :: x) []

def TypeEnv.insert (x : String) (s : Scheme) (env : TypeEnv) : TypeEnv :=
  { env with vars := env.vars.insert x s }

def TypeEnv.ftv (env : TypeEnv) : List String :=
  List.ftv (Std.HashMap.elems env.vars)

def TypeEnv.apply (s : Subst) (env : TypeEnv) : TypeEnv :=
  { env with vars := Subst.map (Scheme.apply s) env.vars }

instance : Types TypeEnv := ⟨TypeEnv.ftv, TypeEnv.apply⟩

def generalize : TypeEnv → T → Scheme := λ env t =>
  let vars := env.ftv.diff t.ftv
  Scheme.scheme vars t

inductive TIEnv where
| tiEnv : TIEnv

structure TIState where
  tiSupply : Int
  recursingOn : List String

def TIState.init := TIState.mk 0 {}

structure TypeError where
  message : String
  location : Option Term.Location := Option.none
  deriving Repr

instance : ToString TypeError where
  toString := λ ⟨ message, location ⟩ =>
    match location with
    | some l => s!"{message} starting at {l.start}, ending at {l.end_}"
    | none => message

abbrev TI (α : Type) := ExceptT TypeError (ReaderT TIEnv (StateT TIState IO)) α

def runTI : TI α → IO (Except TypeError α × TIState) := λ t => do
  let (res, st) ← (t.run TIEnv.tiEnv).run TIState.init
  pure (res, st)

def newTyVar (prefix_ : String) : TI T := do
  let s ← get
  set { s with tiSupply := s.tiSupply + 1  }
  pure $ T.var (prefix_ ++ toString s.tiSupply)

def newRecursion (funcName : String) : TI String := do
  let s ← get
  if s.recursingOn.contains funcName
    then throw <| TypeError.mk "cannot shadow a recursive function" none
    else do
      set { s with recursingOn := s.recursingOn.insert funcName }
      pure funcName

def removeRecursion (funcName : String) : TI Unit := do
  let s ← get
  set { s with recursingOn := s.recursingOn.erase funcName }

def instantiate : Scheme → TI T
| Scheme.scheme vars t => do
  let nvars ← List.mapM (λ _ => newTyVar "α") vars
  let s := Std.HashMap.ofList (List.zip vars nvars)
  pure $ t.apply s

def varBind : String → T → TI Subst := λ u t => do
  if t == T.var u then pure {}
  else if u ∈ t.ftv then throw <| TypeError.mk (s!"occurs check fails {u} vs. {ToString.toString t}") none
  else pure $ Std.HashMap.ofList [(u, t)]

def IsFunction : T → Bool
| T.func _ _ => true
| _ => false

def ArgsLocationFor : (x : T) → Type
| T.func _ _ => List (Location)
| _ => Unit

def defaultFor : (x : T) → ArgsLocationFor x
| T.func params _ => params.map (λ _ => Location.mk 0 0)
| T.int => ()
| T.bool => ()
| T.string => ()
| T.var _ => ()
| T.tuple _ => ()
| T.oneOf _ => ()

def getArgsLocation : List Location → Location
| [] => Location.mk 0 0
| x :: xs => Location.mk (x.start) (List.getLastD xs x).end_


mutual
partial def mguList : List T → List (T × Location) → TI Subst
| [], [] => pure {}
| x :: xs, (y, l) :: ys => do
  let s₁ ← mgu l x y (defaultFor y)
  let s₂ ← mguList (xs.map (λ x => x.apply s₁)) (ys.map (λ (y, l) => (y.apply s₁, l)))
  pure $ s₁.compose s₂
| args₁, args₂ => throw <| ⟨ s!"Oh no! Wrong number of arguments: the function expected {args₁.length}, but got {args₂.length}", none ⟩

partial def mgu (l : Location) : T → (x : T) → ArgsLocationFor x → TI Subst
| T.func args₁ ret₁, T.func args₂ ret₂, args => do
  if args₁.length != args₂.length
    then throw <| ⟨ s!"Oh no! Wrong number of arguments: the function expected {args₁.length}, but got {args₂.length}", getArgsLocation args ⟩
  let s₁ ← mguList args₁ (args₂.zip args)
  let s₂ ← mgu l (ret₁.apply s₁) (ret₂.apply s₁) (defaultFor (ret₂.apply s₁))
  pure $ s₁.compose s₂
| T.var u, t, _ => varBind u t
| t, T.var u, _ => varBind u t
| T.oneOf ts, T.oneOf ts₁, _ =>
  -- We let any intersection here pass. If there's any error, that's gonna be caught by the runtime.
  if List.bagInter ts ts₁ == []
    then throw ⟨ s!"Oh no! I can't match these types: I was expecting {ts}, but found {ts₁}", l ⟩
    else pure {}
| T.oneOf ts, t, _ => if ts.contains t then pure {} else
  throw $ ⟨ s!"Oh no! I can't match these types: I was expecting one of {ts}, but found {t}", l ⟩
| t, T.oneOf ts, _ => if ts.contains t then pure {} else
  throw $ ⟨ s!"Oh no! I can't match these types: I was expecting {t}, but found one of {ts}", l ⟩
| T.int, T.int, _ => pure {}
| T.bool, T.bool, _ => pure {}
| T.string, T.string, _ => pure {}
| T.tuple (a, b), T.tuple (c, d), _ => do
  let s₁ ← mgu l a c (defaultFor c)
  let s₂ ← mgu l b d (defaultFor d)
  pure $ Subst.compose s₁ s₂
| t₁, t₂, _ => throw $ ⟨ s!"Oh no! I can't match these types: I was expecting {t₁}, but found {t₂}", l ⟩
end

def tiLit : Literal → TI (Subst × T)
| Literal.int _ => pure ({}, T.int)
| Literal.bool _ => pure ({}, T.bool)
| Literal.string _ => pure ({}, T.string)

partial def applyWhileDiff : List T → Subst → TI (List T) := λ ts s => do
  let ts₁ ← ts.mapM (λ x => pure $ x.apply s)
  if ts == ts₁
    then pure ts
    else applyWhileDiff ts₁ s

open Term in
mutual
partial def tiList : TypeEnv → List Term → TI (Subst × List T)
| _, [] => pure ({}, [])
| env, x :: xs => do
  let (s₁, t₁) ← ti env x
  let env₁ := env.apply s₁
  let (s₂, t₂) ← tiList env₁ xs
  pure (s₁.compose s₂, t₁ :: t₂)

partial def ti (env : TypeEnv) : Term → TI (Subst × T)
| Var l x => do
  match env.vars.find? x with
  | some s => do
    let t ← instantiate s
    pure ({}, t)
  | none => throw $ ⟨ s!"unbound variable: {x}", l ⟩
| Term.Int _ t => tiLit (Literal.int t)
| Str _ t => tiLit (Literal.string t)
| Boolean _ t => tiLit (Literal.bool t)
| Call _ f args => do
  match f with
  | Var _ x =>
    let { recursingOn, .. } ← get
    if x ∈ recursingOn
      then
        pure ({}, T.var (x ++ "call"))
      else
        let tv ← newTyVar "α"
        let (s₁, t₁) ← ti env f
        let env₁ := env.apply s₁
        let (s₂, t₂) ← tiList env₁ args
        let s₃ ← mgu f.location (t₁.apply s₂) (T.func t₂ tv) (args.map (·.location))
        pure (Subst.composeMany [s₃, s₂, s₁], tv.apply s₃)
  | _ =>
    let tv ← newTyVar "α"
    let (s₁, t₁) ← ti env f
    let env₁ := env.apply s₁
    let (s₂, t₂) ← tiList env₁ args
    let s₃ ← mgu f.location (t₁.apply s₂) (T.func t₂ tv) (args.map (·.location))
    pure (Subst.composeMany [s₃, s₂, s₁], tv.apply s₃)
| Function _ { parameters, value } => do
  let args := parameters.map (·.value)
  let env₁ := List.foldl (λ env x => Std.HashMap.erase env x) env.vars args
  let argsTyVars ← args.mapM (λ _ => newTyVar "α")
  let args₁ := List.zip args (List.map (Scheme.scheme []) argsTyVars)
  let env₂ := TypeEnv.mk <| Std.HashMap.mergeWith (λ _ x _ => x) env₁ (HashMap.ofList args₁)
  let (s₁, t₁) ← ti env₂ value
  let args₂ ← applyWhileDiff argsTyVars s₁
  pure (s₁, T.func args₂ t₁)
| If _ { condition, consequent, alternative } => do
  let (s₁, t₁) ← ti env condition
  let s₂ ← mgu condition.location t₁ T.bool ()
  let env₁ := env.apply s₂
  let (s₃, t₃) ← ti env₁ consequent
  let env₂ := env₁.apply s₃
  let (s₄, t₄) ← ti env₂ alternative
  let t := (t₃.combine t₄).apply s₄
  pure (Subst.composeMany [s₄, s₃, s₂, s₁], t)
| Tuple _ fst snd => do
  let (s₁, t₁) ← ti env fst
  let env₁ := env.apply s₁
  let (s₂, t₂) ← ti env₁ snd
  pure (s₂.compose s₁, T.tuple (t₁, t₂))
| First _ e => do
  let (s, t) ← ti env e
  let t₀ ← newTyVar "t"
  let t₁ ← newTyVar "t"
  let s₂ ← mgu e.location t (T.tuple (t₀, t₁)) ()
  pure (s₂.compose s, t₀)
| Second _ e => do
  let (s, t) ← ti env e
  let t₀ ← newTyVar "t"
  let t₁ ← newTyVar "t"
  let s₂ ← mgu e.location t (T.tuple (t₀, t₁)) ()
  pure (s₂.compose s, t₁)
| Print _ expr => do
  let (s, t) ← ti env expr
  pure (s, t)
| f@(Let l { name, value, next }) => do
  let name := name.value
  if Term.isRecursiveFunction f
    then do
      let recName ← newRecursion name
      let tv := T.var recName
      let env₁ := env.insert name (Scheme.scheme [] tv)
      let (s₁, t₁) ← ti env₁ value
      let s' ← mgu l (t₁.apply s₁) tv ()
      let env₂ := env₁.apply s'
      let scheme := generalize env₂ t₁
      let (s₂, t₂) ← ti (env₂.insert name scheme) next
      pure (s₁.compose s₂, t₂.remove (T.var (name ++ "call")))
    else do
      removeRecursion name
      let (s₁, t₁) ← ti env value
      let env₁ := env.apply s₁
      let scheme := generalize env₁ t₁
      let (s₂, t₂) ← ti (env₁.insert name scheme) next
      pure (s₁.compose s₂, t₂)
| Binary _ { lhs := leftExpr, rhs := rightExpr, op } =>
  match TypedBinOp.ofBinOp op with
  | { left, right, op := BinOp.Add, .. } => do
    let (sLeft, tLeft) ← ti env leftExpr
    let s₁ ← mgu leftExpr.location (tLeft.apply sLeft) left (defaultFor left)
    let right₁ := right.apply s₁
    let env₁ := env.apply s₁
    let (sRight, tRight) ← ti env₁ rightExpr
    let s₂ ← mgu rightExpr.location (tRight.apply sRight) right₁ (defaultFor right₁)
    let result :=
      match tLeft, tRight with
      | T.int, T.int => T.int
      | _, T.string => T.string
      | T.string, _ => T.string
      | _, _ => T.oneOf [T.int, T.string]
    pure (Subst.composeMany [s₂, sRight, s₁, sLeft], result)
  | { left, right, result, .. } => do
    let (sLeft, tLeft) ← ti env leftExpr
    let s₁ ← mgu leftExpr.location (tLeft.apply sLeft) left (defaultFor left)
    let right₁ := right.apply s₁
    let env₁ := env.apply s₁
    let (sRight, tRight) ← ti env₁ rightExpr
    let s₂ ← mgu rightExpr.location (tRight.apply sRight) right₁ (defaultFor right₁)
    pure (Subst.composeMany [s₂, sRight, s₁, sLeft], result)
end

def typeInference : Std.HashMap String Scheme → Term → TI T := λ env e => do
  let (s, t) ← ti (TypeEnv.mk env) e
  pure (Types.apply s t)

end Rinha.Type
