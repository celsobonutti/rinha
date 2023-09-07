namespace Rinha.Term

inductive BinOp
| Add | Sub | Mul | Div | Rem | Eq | Neq | Lt | Gt | Lte | Gte | And | Or
deriving Repr

structure WithLocation (α : Type) where
  value : α
deriving Repr

structure Binary (α : Type) where
  lhs : α
  rhs : α
  op : BinOp
deriving Repr

def Parameter := WithLocation String
deriving Repr

structure Function (α : Type) where
  parameters : List Parameter
  value : α
deriving Repr

structure Let (α : Type) where
  name : Parameter
  value : α
  next : α
deriving Repr

structure If (α : Type) where
  condition : α
  then' : α
  otherwise : α
deriving Repr

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
deriving Repr


end Rinha.Term
