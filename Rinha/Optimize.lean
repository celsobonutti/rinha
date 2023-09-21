import Rinha.Term

namespace Rinha.Optimize
open Rinha.Term

open Term in
partial def optimize : Term → Term
| Term.Int l n => Term.Int l n
| Var l x => Term.Var l x
| Boolean l b => Term.Boolean l b
| Str l s => Term.Str l s
| First l a =>
  match optimize a with
  | Term.Tuple location a _ => a.withLocation location
  | a => Term.First l a
| Second l a =>
  match optimize a with
  | Term.Tuple l _ b => b.withLocation l
  | a => Term.Second l a
| Print l a => Term.Print l (optimize a)
| Tuple l a b => Term.Tuple l (optimize a) (optimize b)
| Call l f args => Term.Call l f (args.map optimize)
| Function l { parameters, value } => Term.Function l { parameters, value := (optimize value) }
| If l { condition, consequent, alternative } =>
  let condition := optimize condition
  match condition with
  | Boolean _ true => (optimize consequent).withLocation l
  | Boolean _ false => (optimize alternative).withLocation l
  | _ => Term.If l { condition
                   , consequent := (optimize consequent)
                   , alternative := (optimize alternative)
                  }
| Let l { name, value, next } =>
  Term.Let l { name, value := optimize value, next := (optimize next) }
| Binary l { lhs, rhs, op } =>
  open BinOp in
  match op with
  | BinOp.Add =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Int l (a + b)
    | (Str _ a, Str _ b) => Str l (a ++ b)
    | (Term.Int _ a, Str _ b) => Str l (s! "{a}{b}")
    | (Str _ a, Term.Int _ b) => Str l (s! "{a}{b}")
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Sub =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Int l (a - b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Mul =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Int l (a * b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Div =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Int l (a / b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Rem =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Int l (a % b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Eq =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Boolean l (a == b)
    | (Term.Boolean _ a, Term.Boolean _ b) => Boolean l (a == b)
    | (Term.Str _ a, Term.Str _ b) => Boolean l (a == b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Neq =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Boolean l (a != b)
    | (Term.Boolean _ a, Term.Boolean _ b) => Boolean l (a != b)
    | (Term.Str _ a, Term.Str _ b) => Boolean l (a != b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Lt =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Boolean l (a < b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Lte =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Boolean l (a <= b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Gt =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Boolean l (a > b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Gte =>
    match (optimize lhs, optimize rhs) with
    | (Term.Int _ a, Term.Int _ b) => Boolean l (a >= b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.And =>
    match (optimize lhs, optimize rhs) with
    | (Term.Boolean _ a, Term.Boolean _ b) => Boolean l (a && b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }
  | BinOp.Or =>
    match (optimize lhs, optimize rhs) with
    | (Term.Boolean _ a, Term.Boolean _ b) => Boolean l (a || b)
    | (a, b) => Term.Binary l { lhs := a, rhs := b, op }

end Rinha.Optimize

def Rinha.Term.Program.optimize : Program → Program
| p => { p with expression := Rinha.Optimize.optimize p.expression }
