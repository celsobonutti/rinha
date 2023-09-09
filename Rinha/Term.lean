import JSON

namespace Rinha.Term

inductive BinOp
| Add | Sub | Mul | Div | Rem | Eq | Neq | Lt | Gt | Lte | Gte | And | Or
deriving Repr, BEq, DecidableEq

structure WithLocation (α : Type) where
  value : α
deriving Repr, BEq, DecidableEq

structure Binary (α : Type) where
  lhs : α
  rhs : α
  op : BinOp
deriving Repr, BEq, DecidableEq

def Parameter := WithLocation String
deriving Repr, BEq, DecidableEq

structure Function (α : Type) where
  parameters : List Parameter
  value : α
deriving Repr, BEq, DecidableEq

structure Let (α : Type) where
  name : Parameter
  value : α
  next : α
deriving Repr, BEq, DecidableEq

structure If (α : Type) where
  condition : α
  then' : α
  otherwise : α
deriving Repr, BEq, DecidableEq

inductive Term
| Int : Int → Term
| Str : String → Term
| Boolean : Bool → Term
| Call : Term → List Term → Term
| Function : Function Term → Term
| Binary : Binary Term → Term
| Let : Let Term → Term
| If : If Term → Term
| Print : Term → Term
| First : Term → Term
| Second : Term → Term
| Tuple : Term → Term → Term
| Var : String → Term
deriving Repr, BEq

def may_be_bool : Term → Prop
| Term.Boolean _ => true
| Term.If {then', otherwise, ..} => may_be_bool then' ∨ may_be_bool otherwise
| Term.Function {value, ..} => may_be_bool value
| Term.First (Term.Tuple lhs _) => may_be_bool lhs
| Term.Second (Term.Tuple _ rhs) => may_be_bool rhs
| _ => false

def may_be_int : Term → Prop
| Term.Int _ => true
| Term.If {then', otherwise, ..} => may_be_bool then' ∨ may_be_bool otherwise
| Term.Function {value, ..} => may_be_bool value
| Term.First (Term.Tuple lhs _) => may_be_bool lhs
| Term.Second (Term.Tuple _ rhs) => may_be_bool rhs
| _ => false

instance : Coe α (Except String α) where
  coe x := Except.ok x

def BinOp.from_string : String → Except String BinOp
| "Add" => BinOp.Add
| "Sub" => BinOp.Sub
| "Mul" => BinOp.Mul
| "Div" => BinOp.Div
| "Rem" => BinOp.Rem
| "Eq" => BinOp.Eq
| "Neq" => BinOp.Neq
| "Lt" => BinOp.Lt
| "Gt" => BinOp.Gt
| "Lte" => BinOp.Lte
| "Gte" => BinOp.Gte
| "And" => BinOp.And
| "Or" => BinOp.Or
| _ => Except.error "invalid binary operation"

def Parameter.from_JSON : JSON → Except String Parameter
| JSON.obj fields =>
  match fields["text"]? with
  | JSON.str text => pure {value := text}
  | _ => Except.error "expected a parameter"
| _ => Except.error "expected a parameter"

partial def Term.from_JSON : JSON → Except String Term
| JSON.obj fields =>
  match fields["kind"]? with
  | "Int" =>
    match fields["value"]? with
    | JSON.num n => Term.Int n
    | _ => Except.error "expected a number"
  | "Str" =>
    match fields["value"]? with
    | JSON.str s => Term.Str s
    | _ => Except.error "expected a string"
  | "Boolean" =>
    match fields["value"]? with
    | JSON.bool b => Term.Boolean b
    | _ => Except.error "expected a boolean"
  | "Tuple" =>
    match fields["first"]?, fields["second"]? with
    | Option.some fst, Option.some snd => do
      let fst ← from_JSON fst
      let snd ← from_JSON snd
      Term.Tuple fst snd
    | _, _ => Except.error "expected a tuple"
  | "Binary" =>
    match fields["lhs"]?, fields["rhs"]?, fields["op"]? with
    | Option.some lhs, Option.some rhs, Option.some (JSON.str op) => do
      let lhs ← from_JSON lhs
      let rhs ← from_JSON rhs
      let op ← BinOp.from_string op
      Term.Binary {lhs, rhs, op}
    | _, _, _ => Except.error "expected a binary operation"
  | "Call" =>
    match fields["callee"]?, fields["arguments"]? with
    | Option.some callee, Option.some (JSON.arr args) => do
      let callee ← from_JSON callee
      let args ← args.mapM from_JSON
      Term.Call callee args
    | _, _ => Except.error "expected a function call"
  | "Function" =>
    match fields["parameters"]?, fields["value"]? with
    | Option.some (JSON.arr params), Option.some value => do
      let parameters ← params.mapM Parameter.from_JSON
      let value ← from_JSON value
      Term.Function {parameters, value}
    | _, _ => Except.error "expected a function"
  | "First" =>
    match fields["value"]? with
    | Option.some value => do
      let value ← from_JSON value
      Term.First value
    | _ => Except.error "expected a first projection"
  | "Second" =>
    match fields["value"]? with
    | Option.some value => do
      let value ← from_JSON value
      Term.Second value
    | _ => Except.error "expected a second projection"
  | "Let" =>
    match fields["name"]?, fields["value"]?, fields["next"]? with
    | Option.some name, Option.some value, Option.some next => do
      let name ← Parameter.from_JSON name
      let value ← from_JSON value
      let next ← from_JSON next
      Term.Let {name, value, next}
    | _, _, _ => Except.error "expected a let binding"
  | "If" =>
    match fields["condition"]?, fields["then"]?, fields["otherwise"]? with
    | Option.some condition, Option.some then', Option.some otherwise => do
      let condition ← from_JSON condition
      let then' ← from_JSON then'
      let otherwise ← from_JSON otherwise
      Term.If {condition, then', otherwise}
    | Option.none, _, _ => Except.error "expected a condition"
    | _, Option.none, _ => Except.error "expected a then branch"
    | _, _, Option.none => Except.error "expected an otherwise branch"
  | "Print" =>
    match fields["value"]? with
    | Option.some value => do
      let value ← from_JSON value
      Term.Print value
    | _ => Except.error "expected a print expression"
  | "Var" =>
    match fields["text"]? with
    | Option.some (JSON.str name) => Term.Var name
    | _ => Except.error "expected a variable"
  | _ => Except.error "invalid Term kind"
| _ => Except.error "invalid JSON"

structure Program where
  name : String
  expression : Term
deriving Repr

def Program.from_JSON : JSON → Except String Program
| JSON.obj fields =>
  match fields["name"]?, fields["expression"]? with
  | Option.some (JSON.str name), Option.some expression => do
    let expression ← Term.from_JSON expression
    pure {name, expression}
  | _, _ => Except.error "expected a program"
| _ => Except.error "expected a program"

end Rinha.Term
