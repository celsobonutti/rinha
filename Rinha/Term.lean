import Lean.Data.Json.Basic
import Lean.Data.RBMap

namespace Rinha.Term

inductive BinOp
| Add | Sub | Mul | Div | Rem | Eq | Neq | Lt | Gt | Lte | Gte | And | Or
deriving Repr, BEq, DecidableEq

structure Location where
  start : Nat
  end_ : Nat
deriving Repr, BEq, DecidableEq

def Location.join (l₁ l₂ : Location) : Location :=
  {start := l₁.start, end_ := l₂.end_}

structure WithLocation (α : Type) where
  value : α
  location : Location
deriving Repr, BEq, DecidableEq

structure Binary' (α : Type) where
  lhs : α
  rhs : α
  op : BinOp
deriving Repr, BEq, DecidableEq

def Parameter := WithLocation String
deriving Repr, BEq, DecidableEq

structure Function' (α : Type) where
  parameters : List Parameter
  value : α
deriving Repr, BEq, DecidableEq

structure Let' (α : Type) where
  name : Parameter
  value : α
  next : α
deriving Repr, BEq, DecidableEq

structure If' (α : Type) where
  condition : α
  consequent : α
  alternative : α
deriving Repr, BEq, DecidableEq

inductive Term
| Int : Location → Int → Term
| Str : Location → String → Term
| Boolean : Location → Bool → Term
| Call : Location → Term → List Term → Term
| Function : Location → Function' Term → Term
| Binary : Location → Binary' Term → Term
| Let : Location → Let' Term → Term
| If : Location → If' Term → Term
| Print : Location → Term → Term
| First : Location → Term → Term
| Second : Location → Term → Term
| Tuple : Location → Term → Term → Term
| Var : Location → String → Term
deriving Repr, BEq

def Term.withLocation (l : Location) : Term → Term
| Term.Int _ n => Term.Int l n
| Term.Str _ s => Term.Str l s
| Term.Boolean _ b => Term.Boolean l b
| Term.Call _ callee args => Term.Call l callee args
| Term.Function _ f => Term.Function l f
| Term.Binary _ b => Term.Binary l b
| Term.Let _ l' => Term.Let l l'
| Term.If _ i => Term.If l i
| Term.Print _ p => Term.Print l p
| Term.First _ f => Term.First l f
| Term.Second _ s => Term.Second l s
| Term.Tuple _ fst snd => Term.Tuple l fst snd
| Term.Var _ name => Term.Var l name



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

abbrev JSON := Lean.Json

instance : GetElem (Lean.RBNode String fun _ => Lean.Json) String (Option Lean.Json) (λ _ _ => True) where
  getElem node elem _ := Lean.RBNode.find compare node elem

def Location.from_JSON : JSON → Except String Location
| Lean.Json.obj fields =>
  match fields["location"]? with
  | Option.some (Lean.Json.obj fields) =>
    match fields["start"], fields["end"] with
    | Option.some s@(Lean.Json.num _), Option.some e@(Lean.Json.num _) => do
      Location.mk
        <$> s.getNat?
        <*> e.getNat?
    | _, _ => Except.error "expected a location field"
  | _ => Except.error s!"expected a location object"
| _ => Except.error "expected a location"

def Parameter.from_JSON : JSON → Except String Parameter
| Lean.Json.obj fields => do
  let location ← Location.from_JSON (Lean.Json.obj fields)
  match fields["text"] with
  | Lean.Json.str value => pure {value, location}
  | _ => Except.error "expected a parameter"
| _ => Except.error "expected a parameter"

partial def Term.from_JSON : JSON → Except String Term
| Lean.Json.obj fields => do
  let location ← Location.from_JSON (Lean.Json.obj fields)
  match fields["kind"] with
  | "Int" =>
    match fields["value"] with
    | Option.some n@(Lean.Json.num _) => do
      Term.Int location <$> n.getInt?
    | _ => Except.error "expected a number"
  | "Str" =>
    match fields["value"] with
    | Lean.Json.str s => Term.Str location s
    | _ => Except.error "expected a string"
  | "Bool" =>
    match fields["value"] with
    | Lean.Json.bool b => Term.Boolean location b
    | _ => Except.error "expected a boolean"
  | "Tuple" =>
    match fields["first"], fields["second"] with
    | Option.some fst, Option.some snd => do
      let fst ← from_JSON fst
      let snd ← from_JSON snd
      Term.Tuple location fst snd
    | _, _ => Except.error "expected a tuple"
  | "Binary" =>
    match fields["lhs"], fields["rhs"], fields["op"] with
    | Option.some lhs, Option.some rhs, Option.some (Lean.Json.str op) => do
      let lhs ← from_JSON lhs
      let rhs ← from_JSON rhs
      let op ← BinOp.from_string op
      Term.Binary location {lhs, rhs, op}
    | _, _, _ => Except.error "expected a binary operation"
  | "Call" =>
    match fields["callee"], fields["arguments"] with
    | Option.some callee, Option.some (Lean.Json.arr args) => do
      let callee ← from_JSON callee
      let args ← (·.toList) <$> args.mapM from_JSON
      Term.Call location callee args
    | _, _ => Except.error "expected a function call"
  | "Function" =>
    match fields["parameters"], fields["value"] with
    | Option.some (Lean.Json.arr params), Option.some value => do
      let parameters ← (·.toList) <$> params.mapM Parameter.from_JSON
      let value ← from_JSON value
      Term.Function location {parameters, value}
    | _, _ => Except.error "expected a function"
  | "First" =>
    match fields["value"] with
    | Option.some value => do
      let value ← from_JSON value
      Term.First location value
    | _ => Except.error "expected a first projection"
  | "Second" =>
    match fields["value"] with
    | Option.some value => do
      let value ← from_JSON value
      Term.Second location value
    | _ => Except.error "expected a second projection"
  | "Let" =>
    match fields["name"], fields["value"], fields["next"] with
    | Option.some name, Option.some value, Option.some next => do
      let name ← Parameter.from_JSON name
      let value ← from_JSON value
      let next ← from_JSON next
      Term.Let location {name, value, next}
    | _, _, _ => Except.error "expected a let binding"
  | "If" =>
    match fields["condition"], fields["then"], fields["otherwise"] with
    | Option.some condition, Option.some consequent, Option.some otherwise => do
      let condition ← from_JSON condition
      let consequent ← from_JSON consequent
      let alternative ← from_JSON otherwise
      Term.If location {condition, consequent, alternative}
    | Option.none, _, _ => Except.error "expected a condition"
    | _, Option.none, _ => Except.error "expected a then branch"
    | _, _, Option.none => Except.error "expected an otherwise branch"
  | "Print" =>
    match fields["value"] with
    | Option.some value => do
      let value ← from_JSON value
      Term.Print location value
    | _ => Except.error "expected a print expression"
  | "Var" =>
    match fields["text"] with
    | Option.some (Lean.Json.str name) => Term.Var location name
    | _ => Except.error "expected a variable"
  | Lean.Json.str k => Except.error ("invalid Term kind: " ++ k)
  | _ => Except.error "invalid Term"
| _ => Except.error "invalid JSON"

structure Program where
  name : String
  expression : Term
deriving Repr

def Program.from_JSON : JSON → Except String Program
| Lean.Json.obj fields =>
  match fields["name"], fields["expression"] with
  | Option.some (Lean.Json.str name), Option.some expression => do
    let expression ← Term.from_JSON expression
    pure {name, expression}
  | _, _ => Except.error "expected a program"
| _ => Except.error "expected a program"

partial def Term.detectRecursion : String → Term → Bool
| x, Term.Call _ p args =>
  match p with
  | Term.Var _ y => x == y || args.any (detectRecursion x)
  | _ => args.any (detectRecursion x)
| x, Term.Let _ { name, value, next } =>
  if (name.value == x)
  then false
  else detectRecursion x value || detectRecursion x next
| x, Term.Function _ { value, .. } => detectRecursion x value
| x, Term.Binary _ { lhs, rhs, .. } => detectRecursion x lhs || detectRecursion x rhs
| x, Term.If _ { condition, consequent, alternative } => List.foldl (· || detectRecursion x ·) false [condition, consequent, alternative]
| x, Term.Tuple _ a b => detectRecursion x a || detectRecursion x b
| x, Term.First _ e => detectRecursion x e
| x, Term.Second _ e => detectRecursion x e
| x, Term.Print _ e => detectRecursion x e
| _, Term.Var _ _ => false
| _, Term.Int _ _ => false
| _, Term.Str _ _ => false
| _, Term.Boolean _ _ => false

partial def Term.isRecursiveFunction : Term → Bool
| Term.Let _ { name, value := Term.Function _ { value, .. }, .. } =>
  detectRecursion name.value value
| _ => false

def Term.location : Term → Location
| Term.Int l _ => l
| Term.Str l _ => l
| Term.Boolean l _ => l
| Term.Call l _ _ => l
| Term.Function l _ => l
| Term.Binary l _ => l
| Term.Let l _ => l
| Term.If l _ => l
| Term.Print l _ => l
| Term.First l _ => l
| Term.Second l _ => l
| Term.Tuple l _ _ => l
| Term.Var l _ => l

partial def isParameterBeingCalled : List String → Term → Bool
| name, Term.Call _ (Term.Var _ callee) values => name.any (· == callee) || values.any (isParameterBeingCalled name ·)
| name, Term.Call _ _ values => values.any (isParameterBeingCalled name ·)
| name, Term.Let _ { name := { value, .. } , value := body, next } =>
  let name := if List.contains name value then List.erase name value else name
  isParameterBeingCalled name body || isParameterBeingCalled name next
| name, Term.Function _ { value, .. } => isParameterBeingCalled name value
| name, Term.Binary _ { lhs, rhs, .. } => isParameterBeingCalled name lhs || isParameterBeingCalled name rhs
| name, Term.If _ { condition, consequent, alternative } => List.foldl (· || isParameterBeingCalled name ·) false [condition, consequent, alternative]
| name, Term.Tuple _ a b => isParameterBeingCalled name a || isParameterBeingCalled name b
| name, Term.First _ e => isParameterBeingCalled name e
| name, Term.Second _ e => isParameterBeingCalled name e
| name, Term.Print _ e => isParameterBeingCalled name e
| _, Term.Var _ _ => false
| _, Term.Int _ _ => false
| _, Term.Str _ _ => false
| _, Term.Boolean _ _ => false

end Rinha.Term
