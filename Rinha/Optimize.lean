import Rinha.Term

namespace Rinha.Optimize
open Rinha.Term

open Term in
partial def optimize : Term → Term
| Term.Int n => Term.Int n
| Var x => Term.Var x
| Boolean b => Term.Boolean b
| Str s => Term.Str s
| First a =>
  match optimize a with
  | Term.Tuple a _ => a
  | a => Term.First a
| Second a =>
  match optimize a with
  | Term.Tuple _ b => b
  | a => Term.Second a
| Print a => Term.Print (optimize a)
| Tuple a b => Term.Tuple (optimize a) (optimize b)
| Call f args => Term.Call f (args.map optimize)
| Function { parameters, value } => Term.Function { parameters, value := (optimize value) }
| If { condition, consequent, alternative } =>
  let condition := optimize condition
  match condition with
  | Boolean true => optimize consequent
  | Boolean false => optimize alternative
  | _ => Term.If { condition
                 , consequent := (optimize consequent)
                 , alternative := (optimize alternative)
                 }
| Let { name, value, next } =>
  Term.Let { name, value := optimize value, next := (optimize next) }
| Binary { lhs, rhs, op } =>
  open BinOp in
  match op with
  | BinOp.Add =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Int (a + b)
    | (Str a, Str b) => Str (a ++ b)
    | (Term.Int a, Str b) => Str (s! "{a}{b}")
    | (Str a, Term.Int b) => Str (s! "{a}{b}")
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Sub =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Int (a - b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Mul =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Int (a * b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Div =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Int (a / b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Rem =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Int (a % b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Eq =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Boolean (a == b)
    | (Term.Boolean a, Term.Boolean b) => Boolean (a == b)
    | (Term.Str a, Term.Str b) => Boolean (a == b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Neq =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Boolean (a != b)
    | (Term.Boolean a, Term.Boolean b) => Boolean (a != b)
    | (Term.Str a, Term.Str b) => Boolean (a != b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Lt =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Boolean (a < b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Lte =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Boolean (a <= b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Gt =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Boolean (a > b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Gte =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int a, Term.Int b) => Boolean (a >= b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.And =>
    match (optimize lhs, optimize rhs) with
    | (Term.Boolean a, Term.Boolean b) => Boolean (a && b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }
  | BinOp.Or =>
    match (optimize lhs, optimize rhs) with
    | (Term.Boolean a, Term.Boolean b) => Boolean (a || b)
    | (a, b) => Term.Binary { lhs := a, rhs := b, op }

end Rinha.Optimize

def Rinha.Term.Program.optimize : Program → Program
| p => { p with expression := Rinha.Optimize.optimize p.expression }
