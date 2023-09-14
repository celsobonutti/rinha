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

def T.combine : T → T → T
| T.oneOf xs, T.oneOf ys => T.oneOf (xs ++ ys)
| T.oneOf xs, y => T.oneOf (y :: xs)
| x, T.oneOf ys => T.oneOf (x :: ys)
| x, y => if x == y then x else T.oneOf [x, y]

structure TypedBinOp where
  op : BinOp
  left : T
  right : T
  result : T
deriving Repr, BEq

def TypedBinOp.fromBinOp : BinOp → TypedBinOp
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
deriving Repr, BEq

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

def TIState.init := TIState.mk 0

abbrev TI (α : Type) := ExceptT String (ReaderT TIEnv (StateT TIState IO)) α

def runTI : TI α → IO (Except String α × TIState) := λ t => do
  let (res, st) ← (t.run TIEnv.tiEnv).run TIState.init
  pure (res, st)

def newTyVar (prefix_ : String) : TI T := do
  let s ← get
  set { s with tiSupply := s.tiSupply + 1  }
  pure $ T.var (prefix_ ++ toString s.tiSupply)

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
def tiList : TypeEnv → List Expr → TI (Subst × List T)
| _, [] => pure ({}, [])
| env, x :: xs => do
  let (s₁, t₁) ← ti env x
  let env₁ := env.apply s₁
  let (s₂, t₂) ← tiList env₁ xs
  pure (s₁.compose s₂, t₁ :: t₂)

def ti : TypeEnv → Expr → TI (Subst × T)
| env, Expr.var x => match env.vars.find? x with
  | some s => do
    let t ← instantiate s
    pure ({}, t)
  | none => throw $ "unbound variable: " ++ x
| _, Expr.lit l => tiLit l
| env, Expr.app f args => do
  let tv ← newTyVar "α"
  let (s₁, t₁) ← ti env f
  let env₁ := env.apply s₁
  let (s₂, t₂) ← tiList env₁ args
  let s₃ ← mgu (t₁.apply s₂) (T.func t₂ tv)
  pure (Subst.composeMany [s₃, s₂, s₁], tv.apply s₃)
| env, Expr.func args body => do
  let env₁ := List.foldl (λ env x => Std.HashMap.erase env x) env.vars args
  let argsTyVars ← args.mapM (λ _ => newTyVar "α")
  let args₁ := List.zip args (List.map (Scheme.scheme []) argsTyVars)
  let env₂ := TypeEnv.mk <| Std.HashMap.mergeWith (λ _ x _ => x) env₁ (HashMap.ofList args₁)
  let (s₁, t₁) ← ti env₂ body
  let args₂ ← applyWhileDiff argsTyVars s₁
  pure (s₁, T.func args₂ t₁)
| env, Expr.op { left, right, op := BinOp.Add, .. } rightExpr leftExpr => do
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
| env, Expr.op { left, right, result, .. } leftExpr rightExpr => do
  let (sLeft, tLeft) ← ti env leftExpr
  let s₁ ← mgu (tLeft.apply sLeft) left
  let right₁ := right.apply s₁
  let env₁ := env.apply s₁
  let (sRight, tRight) ← ti env₁ rightExpr
  let s₂ ← mgu (tRight.apply sRight) right₁
  pure (Subst.composeMany [s₂, sRight, s₁, sLeft], result)
| env, Expr.if_ cond then_ else_ => do
  let (s₁, t₁) ← ti env cond
  let s₂ ← mgu t₁ T.bool
  let env₁ := env.apply s₂
  let (s₃, t₃) ← ti env₁ then_
  let env₂ := env₁.apply s₃
  let (s₄, t₄) ← ti env₂ else_
  let t := (t₃.combine t₄).apply s₄
  pure (Subst.composeMany [s₄, s₃, s₂, s₁], t)
| env, Expr.tuple (fst, snd) => do
  let (s₁, t₁) ← ti env fst
  let env₁ := env.apply s₁
  let (s₂, t₂) ← ti env₁ snd
  pure (s₂.compose s₁, T.tuple (t₁, t₂))
| env, Expr.fst e => do
  let (s, t) ← ti env e
  let s₂ ← mgu t (T.tuple (T.var "t₀", T.var "t₁"))
  pure (s₂.compose s, T.var "t₀")
| env, Expr.snd e => do
  let (s, t) ← ti env e
  let s₂ ← mgu t (T.tuple (T.var "t₀", T.var "t₁"))
  pure (s₂.compose s, T.var "t₁")
| env, Expr.print expr => do
  let (s, t) ← ti env expr
  pure (s, t)
| env, Expr.let_ x e₁ e₂ => do
  let (s₁, t₁) ← ti env e₁
  let env₁ := env.apply s₁
  let t₂ := generalize env₁ t₁
  let (s₃, t₃) ← ti (env₁.insert x t₂) e₂
  pure (s₁.compose s₃, t₃)

end

def typeInference : Std.HashMap String Scheme → Expr → TI T := λ env e => do
  let (s, t) ← ti (TypeEnv.mk env) e
  pure (Types.apply s t)

open Expr
open Literal
open BinOp

def toTyped : BinOp → TypedBinOp := TypedBinOp.fromBinOp

def e0 := let_ "id" (func ["x"] (var "x")) (var "id")
def e₀ := let_ "id" (func ["x"] (var "x")) (var "id")
def e₁ := let_ "id" (func ["x", "y"] (op (toTyped BinOp.Eq) (lit (int 2)) (var "x"))) (var "id")
def e₂ := let_ "id" (func ["x", "y"] (op (toTyped BinOp.Add) (lit (int 2)) (var "x"))) (var "id")
def e₃ := let_ "fn" (func ["x", "y"] (op (toTyped BinOp.Eq) (var "y") (var "x"))) (var "fn")
def e₄ := let_ "fn" (func ["x", "y"] (op (toTyped BinOp.Eq) (var "y") (var "x"))) (app (var "fn") [lit (int 1), lit (string "me")])
def e0applied := app (func ["x"] (var "x")) [lit (int 1)]
def e₅ := let_ "sum" (func ["x"] (op (toTyped Eq) (var "x") (lit (int 1)))) (var "sum")
def add := let_ "one" (lit (int 1)) <| app (let_ "add" (func ["y"] (var "one")) (var "add")) [lit (int 2)]
def one := lit (int 1)
def two := lit (int 2)
def str := lit (string "hello")
def sum := op { left := T.int, right := T.int, result := T.int, op := BinOp.Add }

def test : Expr → IO Unit := λ e => do
  let (res, _) ← runTI (typeInference {} e)
  match res with
  | Except.ok t => IO.println t
  | Except.error e => IO.println e

def oneOf := (if_ (lit (bool true)) one str)
def t := tuple (one, e0)

#eval test e₀
#eval test (app e₀ [one])
#eval test e₁
#eval test (app e₁ [one, two])
#eval test e₂
#eval test e₃
#eval test ((op (toTyped BinOp.Eq) (lit (int 2)) (lit (string "oof"))))
#eval test e₄
#eval test (app e₂ [one, two])
#eval test e0
#eval test e0applied
#eval test (app e0 [one])
#eval test e₁
#eval test (op (toTyped Add) one oneOf)
#eval test (op (toTyped Add) one two)
#eval test (op (toTyped Add) str two)
#eval test (op (toTyped Add) two str)
#eval test (op (toTyped Add) str str)
#eval test (oneOf)
#eval test (print oneOf)
#eval test (let_ "id" (lit (int 1)) (var "id"))
#eval test (tuple (one, e0))
#eval test (fst t)
#eval test (fst one)
#eval test (snd t)

end Rinha.Type
