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

axiom tupleEq : ∀ {α β : Type} {a b : α} {c d : β}, (a, c) = (b, d) ↔ a = b ∧ c = d
axiom whatever : ∀ {α : Prop}, ¬α -- TODO: Replace with real proof

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
  | T.tuple (a, b), T.tuple (c, d) => match decT a c, decT b d with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ => isFalse whatever
    | _, isFalse _ => isFalse whatever
  | T.oneOf as, T.oneOf bs => match decTList as bs with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  | _, _ => isFalse whatever

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

instance DecidableEq : DecidableEq T := decT

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

inductive Expr where
| var : String → Expr
| lit : Literal → Expr
| app : Expr → List Expr → Expr
| func : List String → Expr → Expr
| let_ : String → Expr → Expr → Expr
| op : TypedBinOp → Expr → Expr → Expr
| if_ : Expr → Expr → Expr → Expr
| print : Expr → Expr
| tuple : (Expr × Expr) → Expr
| fst : Expr → Expr
| snd : Expr → Expr
deriving Repr, BEq, Inhabited

partial def Expr.ofTerm : Term → Expr
| Term.Int x => Expr.lit (Literal.int x)
| Term.Boolean x => Expr.lit (Literal.bool x)
| Term.Str x => Expr.lit (Literal.string x)
| Term.Var x => Expr.var x
| Term.Call f args => Expr.app (Expr.ofTerm f) (args.map Expr.ofTerm)
| Term.Print t => Expr.print (Expr.ofTerm t)
| Term.Tuple a b => Expr.tuple (Expr.ofTerm a, Expr.ofTerm b)
| Term.First t => Expr.fst (Expr.ofTerm t)
| Term.Second t => Expr.snd (Expr.ofTerm t)
| Term.Function { parameters, value } => Expr.func (parameters.map (·.value)) (Expr.ofTerm value)
| Term.Let { name, value, next } => Expr.let_ name.value (Expr.ofTerm value) (Expr.ofTerm next)
| Term.If { condition, consequent, alternative } => Expr.if_ (Expr.ofTerm condition) (Expr.ofTerm consequent) (Expr.ofTerm alternative)
| Term.Binary binop => Expr.op (TypedBinOp.ofBinOp binop.op) (Expr.ofTerm binop.lhs) (Expr.ofTerm binop.rhs)

partial def detectRecursion : String → Expr → Bool
| x, Expr.app p args => (p == Expr.var x) || args.any (detectRecursion x)
| x, Expr.let_ y e₁ e₂ =>
  if (y == x)
  then false
  else detectRecursion x e₁ || detectRecursion x e₂
| x, Expr.func _ body => detectRecursion x body
| x, Expr.op _ left right => detectRecursion x left || detectRecursion x right
| x, Expr.if_ cond then_ else_ => detectRecursion x cond || detectRecursion x then_ || detectRecursion x else_
| x, Expr.tuple (a, b) => detectRecursion x a || detectRecursion x b
| x, Expr.fst e => detectRecursion x e
| x, Expr.snd e => detectRecursion x e
| x, Expr.print e => detectRecursion x e
| _, Expr.var _ => false
| _, Expr.lit _ => false

partial def Expr.isRecursiveFunction : Expr → Bool
| Expr.let_ name (Expr.func _ body) _ => detectRecursion name body
| _ => false

instance : ToString T where
  toString := reprStr

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

abbrev TI (α : Type) := ExceptT String (ReaderT TIEnv (StateT TIState IO)) α

def runTI : TI α → IO (Except String α × TIState) := λ t => do
  let (res, st) ← (t.run TIEnv.tiEnv).run TIState.init
  pure (res, st)

def newTyVar (prefix_ : String) : TI T := do
  let s ← get
  set { s with tiSupply := s.tiSupply + 1  }
  pure $ T.var (prefix_ ++ toString s.tiSupply)

def newRecursion (funcName : String) : TI String := do
  let s ← get
  if s.recursingOn.contains funcName
    then throw "cannot shadow a recursive function"
    else do
      set { s with recursingOn := s.recursingOn.insert funcName }
      pure funcName

def instantiate : Scheme → TI T
| Scheme.scheme vars t => do
  let nvars ← List.mapM (λ _ => newTyVar "α") vars
  let s := Std.HashMap.ofList (List.zip vars nvars)
  pure $ t.apply s

def varBind : String → T → TI Subst := λ u t => do
  if t == T.var u then pure {}
  else if u ∈ t.ftv then throw "occurs check fails"
  else pure $ Std.HashMap.ofList [(u, t)]

mutual
partial def mguList : List T → List T → TI Subst
| [], [] => pure {}
| x :: xs, y :: ys => do
  let s₁ ← mgu x y
  let s₂ ← mguList (xs.map (λ x₁ => x₁.apply s₁)) (ys.map (λ y₁ => y₁.apply s₁))
  pure $ s₁.compose s₂
| args₁, args₂ => throw ("types do not unify: " ++ toString args₁ ++ " vs. " ++ toString args₂)


partial def mgu : T → T → TI Subst
| T.func args₁ ret₁, T.func args₂ ret₂ => do
  if args₁.length != args₂.length
    then throw ("types do not unify: " ++ toString args₁ ++ " vs. " ++ toString args₂)
  let s₁ ← mguList args₁ args₂
  let s₂ ← mgu (ret₁.apply s₁) (ret₂.apply s₁)
  pure $ s₁.compose s₂
| T.var u, t => varBind u t
| t, T.var u => varBind u t
| T.oneOf ts, T.oneOf ts₁ =>
  -- We let any intersection here pass. If there's any error, that's gonna be caught by the runtime.
  if List.bagInter ts ts₁ == []
    then throw $ "types do not unify: " ++ toString ts ++ " vs. " ++ toString ts₁
    else pure {}
| T.oneOf ts, t => if ts.contains t then pure {} else
  throw $ "types do not unify: " ++ toString t ++ " is not one of " ++ toString ts
| t, T.oneOf ts => if ts.contains t then pure {} else
  throw $ "types do not unify: " ++ toString t ++ " is not one of " ++ toString ts
| T.int, T.int => pure {}
| T.bool, T.bool => pure {}
| T.string, T.string => pure {}
| T.tuple (a, b), T.tuple (c, d) => do
  let s₁ ← mgu a c
  let s₂ ← mgu b d
  pure $ Subst.compose s₁ s₂
| t₁, t₂ => throw $ "types do not unify: " ++ toString t₁ ++ " vs. " ++ toString t₂
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

mutual
partial def tiList : TypeEnv → List Expr → TI (Subst × List T)
| _, [] => pure ({}, [])
| env, x :: xs => do
  let (s₁, t₁) ← ti env x
  let env₁ := env.apply s₁
  let (s₂, t₂) ← tiList env₁ xs
  pure (s₁.compose s₂, t₁ :: t₂)

partial def ti (env : TypeEnv) : Expr → TI (Subst × T)
| Expr.var x => do
  match env.vars.find? x with
  | some s => do
    let t ← instantiate s
    pure ({}, t)
  | none => throw $ "unbound variable: " ++ x
| Expr.lit l => tiLit l
| Expr.app f args => do
  match f with
  | Expr.var x =>
    let { recursingOn, .. } ← get
    if x ∈ recursingOn
      then
        pure ({}, T.var (x ++ "call"))
      else
        let tv ← newTyVar "α"
        let (s₁, t₁) ← ti env f
        let env₁ := env.apply s₁
        let (s₂, t₂) ← tiList env₁ args
        let s₃ ← mgu (t₁.apply s₂) (T.func t₂ tv)
        pure (Subst.composeMany [s₃, s₂, s₁], tv.apply s₃)
  | _ =>
    let tv ← newTyVar "α"
    let (s₁, t₁) ← ti env f
    let env₁ := env.apply s₁
    let (s₂, t₂) ← tiList env₁ args
    let s₃ ← mgu (t₁.apply s₂) (T.func t₂ tv)
    pure (Subst.composeMany [s₃, s₂, s₁], tv.apply s₃)
| Expr.func args body => do
  let env₁ := List.foldl (λ env x => Std.HashMap.erase env x) env.vars args
  let argsTyVars ← args.mapM (λ _ => newTyVar "α")
  let args₁ := List.zip args (List.map (Scheme.scheme []) argsTyVars)
  let env₂ := TypeEnv.mk <| Std.HashMap.mergeWith (λ _ x _ => x) env₁ (HashMap.ofList args₁)
  let (s₁, t₁) ← ti env₂ body
  let args₂ ← applyWhileDiff argsTyVars s₁
  pure (s₁, T.func args₂ t₁)
| Expr.op { left, right, op := BinOp.Add, .. } rightExpr leftExpr => do
  let (sLeft, tLeft) ← ti env leftExpr
  let s₁ ← mgu (tLeft.apply sLeft) left
  let right₁ := right.apply s₁
  let env₁ := env.apply s₁
  let (sRight, tRight) ← ti env₁ rightExpr
  let s₂ ← mgu (tRight.apply sRight) right₁
  let result :=
    match tLeft, tRight with
    | T.int, T.int => T.int
    | _, T.string => T.string
    | T.string, _ => T.string
    | _, _ => T.oneOf [T.int, T.string]
  pure (Subst.composeMany [s₂, sRight, s₁, sLeft], result)
| Expr.op { left, right, result, .. } leftExpr rightExpr => do
  let (sLeft, tLeft) ← ti env leftExpr
  let s₁ ← mgu (tLeft.apply sLeft) left
  let right₁ := right.apply s₁
  let env₁ := env.apply s₁
  let (sRight, tRight) ← ti env₁ rightExpr
  let s₂ ← mgu (tRight.apply sRight) right₁
  pure (Subst.composeMany [s₂, sRight, s₁, sLeft], result)
| Expr.if_ cond then_ else_ => do
  let (s₁, t₁) ← ti env cond
  let s₂ ← mgu t₁ T.bool
  let env₁ := env.apply s₂
  let (s₃, t₃) ← ti env₁ then_
  let env₂ := env₁.apply s₃
  let (s₄, t₄) ← ti env₂ else_
  let t := (t₃.combine t₄).apply s₄
  pure (Subst.composeMany [s₄, s₃, s₂, s₁], t)
| Expr.tuple (fst, snd) => do
  let (s₁, t₁) ← ti env fst
  let env₁ := env.apply s₁
  let (s₂, t₂) ← ti env₁ snd
  pure (s₂.compose s₁, T.tuple (t₁, t₂))
| Expr.fst e => do
  let (s, t) ← ti env e
  let s₂ ← mgu t (T.tuple (T.var "t₀", T.var "t₁"))
  pure (s₂.compose s, T.var "t₀")
| Expr.snd e => do
  let (s, t) ← ti env e
  let s₂ ← mgu t (T.tuple (T.var "t₀", T.var "t₁"))
  pure (s₂.compose s, T.var "t₁")
| Expr.print expr => do
  let (s, t) ← ti env expr
  pure (s, t)
| f@(Expr.let_ name e₁ e₂) => do
  if f.isRecursiveFunction
    then do
      let recName ← newRecursion name
      let tv := T.var recName
      let env₁ := env.insert name (Scheme.scheme [] tv)
      let (s₁, t₁) ← ti env₁ e₁
      let s' ← mgu (t₁.apply s₁) tv
      let env₂ := env₁.apply s'
      let scheme := generalize env₂ t₁
      let (s₂, t₂) ← ti (env₂.insert name scheme) e₂
      pure (s₁.compose s₂, t₂.remove (T.var (name ++ "call")))
    else do
      let (s₁, t₁) ← ti env e₁
      let env₁ := env.apply s₁
      let scheme := generalize env₁ t₁
      let (s₂, t₂) ← ti (env₁.insert name scheme) e₂
      pure (s₁.compose s₂, t₂)
end

def typeInference : Std.HashMap String Scheme → Expr → TI T := λ env e => do
  let (s, t) ← ti (TypeEnv.mk env) e
  pure (Types.apply s t)

end Rinha.Type
