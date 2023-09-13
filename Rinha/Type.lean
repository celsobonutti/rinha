import Mathlib.Init.Set
import Init.Data.List.Basic
import Init.Data.Repr
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
| func : T → T → T
| var : String → T
| tuple : (T × T) → T
-- | oneOf : List T → T
deriving Repr, BEq, Inhabited

structure TypedBinOp where
  op : BinOp
  left : T
  right : T
  result : T
deriving Repr, BEq

def TypedBinOp.fromBinOp : BinOp → TypedBinOp
| BinOp.Add => { op := BinOp.Add, left := T.int, right := T.int, result := T.int }
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
| app : Expr → Expr → Expr
| func : String → Expr → Expr
| let' : String → Expr → Expr → Expr
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
-- | T.oneOf ts => ts.foldl (λ x y => List.union x (ftv y)) {}
-- | T.func args ret => (args.foldl (λ x y => List.union x (ftv y)) (ftv ret))
| T.func arg ret => List.union arg.ftv ret.ftv
| T.tuple (x, y) => List.union x.ftv y.ftv

partial def T.apply : Subst → T → T
| s, T.var x => match s.find? x with
  | some t => t
  | none => T.var x
-- | s, (T.func args ret) => T.func (args.map (apply s)) (apply s ret)
| s, (T.func arg ret) => T.func (arg.apply s) (apply s ret)
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

def Subst.compose (s1 s2 : Subst) : Subst :=
  let s1' := Subst.map (λ t => t.apply s2) s1
  Std.HashMap.mergeWith (λ _ x _ => x) s1' s2

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

def newTyVar (prefix' : String) : TI T := do
  let s ← get
  set { s with tiSupply := s.tiSupply + 1 }
  pure $ T.var (prefix' ++ toString s.tiSupply)

def instantiate : Scheme → TI T
| Scheme.scheme vars t => do
  let nvars ← List.mapM (λ _ => newTyVar "α") vars
  let s := Std.HashMap.ofList (List.zip vars nvars)
  pure $ t.apply s

def varBind : String → T → TI Subst := λ u t => do
  if t == T.var u then pure {}
  else if u ∈ t.ftv then throw "occurs check fails"
  else pure $ Std.HashMap.ofList [(u, t)]

partial def mgu : T → T → TI Subst
-- | T.func args1 ret1, T.func args2 ret2 => do
--   let s1 ← List.zip args1 args2 |>.mapM (λ (x, y) => mgu x y)
--   let s2 ← mgu ret1 ret2
--   pure $ s1.foldl Subst.compose s2
| T.func arg₁ ret₁, T.func arg₂ ret₂ => do
  let s1 ← mgu arg₁ arg₂
  let s2 ← mgu ret₁ ret₂
  pure $ Subst.compose s1 s2
| T.var u, t => varBind u t
| t, T.var u => varBind u t
| T.int, T.int => pure {}
| T.bool, T.bool => pure {}
| T.string, T.string => pure {}
| T.tuple (a, b), T.tuple (c, d) => do
  let s1 ← mgu a c
  let s2 ← mgu b d
  pure $ Subst.compose s1 s2
| t1, t2 => throw $ "types do not unify: " ++ toString t1 ++ " vs. " ++ toString t2

def tiLit : Literal → TI (Subst × T)
| Literal.int _ => pure ({}, T.int)
| Literal.bool _ => pure ({}, T.bool)
| Literal.string _ => pure ({}, T.string)

def ti : TypeEnv → Expr → TI (Subst × T)
| env, Expr.var x => match env.vars.find? x with
  | some s => do
    let t ← instantiate s
    pure ({}, t)
  | none => throw $ "unbound variable: " ++ x
| _, Expr.lit l => tiLit l
| env, Expr.app e1 e2 => do
  let tv ← newTyVar "α"
  let (s1, t1) ← ti env e1
  let (s2, t2) ← ti (env.apply s1) e2
  let s3 ← mgu (t1.apply s2) (T.func t2 tv)
  pure (s3.compose (s2.compose s1), tv.apply s3)
| env, Expr.op { left, right, result, .. } rightExpr leftExpr => do
  let (sLeft, tLeft) ← ti env leftExpr
  let env' := env.apply sLeft
  let (sRight, tRight) ← ti env' rightExpr
  let s₃ ← mgu (tLeft.apply sRight) left
  let s₄ ← mgu (tRight.apply s₃) right
  let s₅ ← if left == right then mgu (tLeft.apply s₄) (tRight.apply s₄) else pure {}
  pure ((((sLeft.compose sRight).compose s₃).compose s₄).compose s₅, result)
| env, Expr.if_ cond then_ else_ => do
  let (s1, t1) ← ti env cond
  let s₂ ← mgu t1 T.bool
  let env' := env.apply s₂
  let (s3, t3) ← ti env' then_
  let env'' := env'.apply s3
  let (s4, t4) ← ti env'' else_
  let s5 ← mgu t3 t4
  pure ((((s1.compose s₂).compose s3).compose s4).compose s5, t3.apply s5)
| env, Expr.tuple (fst, snd) => do
  let (s1, t1) ← ti env fst
  let env' := env.apply s1
  let (s2, t2) ← ti env' snd
  pure (s1.compose s2, T.tuple (t1, t2))
| env, Expr.fst e => do
  let (s, t) ← ti env e
  let s₂ ← mgu t (T.tuple (T.var "t₀", T.var "t₁"))
  pure (s.compose s₂, T.var "t₀")
| env, Expr.snd e => do
  let (s, t) ← ti env e
  let s₂ ← mgu t (T.tuple (T.var "t₀", T.var "t₁"))
  pure (s.compose s₂, T.var "t₁")
| _, Expr.print _ => do
  pure ({}, T.int)
| env, Expr.let' x e1 e2 => do
  let (s1, t1) ← ti env e1
  let env' := env.apply s1
  let t' := generalize env' t1
  let (s2, t2) ← ti (env'.insert x t') e2
  pure (s1.compose s2, t2)
| env, Expr.func arg body => do
  let tv ← newTyVar "α"
  let env' := Std.HashMap.erase env.vars arg
  -- let argsMap := TypeEnv.mk <| args.foldl (λ env x => env.insert x (Scheme.scheme [] tv)) Std.HashMap.empty
  let env'' := TypeEnv.mk <| Std.HashMap.mergeWith (λ _ x _ => x) env' (HashMap.ofList [(arg, Scheme.scheme [] tv)])
  let (s1, t1) ← ti env'' body
  pure (s1, T.func (tv.apply s1) t1)

def typeInference : Std.HashMap String Scheme → Expr → TI T := λ env e => do
  let (s, t) ← ti (TypeEnv.mk env) e
  pure (Types.apply s t)

open Expr
open Literal
open BinOp

def e0 := let' "id" (func "x" (var "x")) (var "id")
def add := let' "one" (lit (int 1)) <| app (let' "add" (func "y" (var "one")) (var "add")) (lit (int 2))
def one := lit (int 1)
def two := lit (int 2)
def str := lit (string "hello")
def sum := op { left := T.int, right := T.int, result := T.int, op := BinOp.Add }

def test : Expr → IO Unit := λ e => do
  let (res, _) ← runTI (typeInference {} e)
  match res with
  | Except.ok t => IO.println t
  | Except.error e => IO.println e

def toTyped : BinOp → TypedBinOp := TypedBinOp.fromBinOp

#eval test add
#eval test (op (toTyped Eq) one str)
#eval test (if_ (lit (bool true)) one str)
#eval test (print str)
#eval test (let' "id" (lit (int 1)) (var "id"))
#eval test (tuple (one, e0))
def t := tuple (one, e0)
#eval test (fst t)
#eval test (fst one)
#eval test (snd t)

end Rinha.Type
