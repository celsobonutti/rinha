import Init.Data.Int.Basic

inductive BinaryTree (α : Type) where
  | null : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α
deriving Repr

open BinaryTree in
def BinaryTree.size : BinaryTree α → Nat
  | null => 0
  | node left _ right => 1 + left.size + right.size

def BinaryTree.depth : BinaryTree α → Nat
  | null => 0
  | node left _ right => 1 + max left.size right.size

def BinaryTree.leaves : BinaryTree α → List α
  | BinaryTree.null => []
  | BinaryTree.node BinaryTree.null x BinaryTree.null => [x]
  | BinaryTree.node left _ right => left.leaves ++ right.leaves

def BinaryTree.map : (α → β) → BinaryTree α → BinaryTree β
  | _, BinaryTree.null => BinaryTree.null
  | f, BinaryTree.node left x right =>
    BinaryTree.node (map f left) (f x) (map f right)

instance : Functor BinaryTree where
  map := BinaryTree.map

def BinaryTree.elem : Int → BinaryTree Int → Bool
  | _, BinaryTree.null => False
  | x, BinaryTree.node left x' right =>
    x == x' || left.elem x || right.elem x

def BinaryTree.maximum : BinaryTree Int → Int
  | BinaryTree.null => 0
  | BinaryTree.node left x right => max (max left.maximum x) right.maximum

def BinaryTree.minimum : BinaryTree Int → Int
  | BinaryTree.null => 0
  | BinaryTree.node left x right => min (min left.minimum x) right.minimum

def BinaryTree.flatten : BinaryTree α → List α
  | BinaryTree.null => []
  | BinaryTree.node left x right => left.flatten ++ [x] ++ right.flatten

inductive Direction where
  | right
  | left

inductive Rotation where
  | none : Rotation
  | single : Direction → Rotation
  | double: Direction → Rotation

def necessaryRotation : BinaryTree α → BinaryTree α → Rotation
  | x, y =>
    let sizeDifference := (x.depth : Int) - (y.depth : Int)
    if [-1, 0, 1].elem sizeDifference then
      Rotation.none
    else
      Rotation.none

-- Needs implementation
def BinaryTree.balance : BinaryTree α → BinaryTree α
  | BinaryTree.null => BinaryTree.null
  | BinaryTree.node left x right =>
    match necessaryRotation left right with
      | Rotation.none => BinaryTree.node left x right
      | Rotation.single Direction.right => BinaryTree.node left x right
      | Rotation.single Direction.left => BinaryTree.node left x right
      | Rotation.double Direction.right => BinaryTree.node left x right
      | Rotation.double Direction.left => BinaryTree.node left x right

abbrev Map (α β : Type) [Hashable α] [Ord α] : Type := BinaryTree (UInt64 × β)

def Map.Empty [Ord α] [Hashable α]: Map α β := BinaryTree.null

def Map.getOption {α β : Type} [Ord α] [Hashable α] : α → Map α β → Option β
| _, BinaryTree.null => Option.none
| x, BinaryTree.node left (y, value) right =>
  match Ord.compare (Hashable.hash x) y with
  | Ordering.eq => Option.some value
  | Ordering.lt => Map.getOption x left
  | Ordering.gt => Map.getOption x right

def Map.insert {α β : Type} [Ord α] [Hashable α] : α → β → Map α β → Map α β
| x, y, BinaryTree.null => BinaryTree.node BinaryTree.null (Hashable.hash x, y) BinaryTree.null
| x, y, BinaryTree.node left (key, value) right =>
  let
    hashed := Hashable.hash x
  match Ord.compare hashed key with
  | Ordering.eq => BinaryTree.node left (hashed, y) right
  | Ordering.lt => BinaryTree.node (Map.insert x y left) (key, value) right
  | Ordering.gt => BinaryTree.node left (key, value) (Map.insert x y right)

def Map.Mem [Ord α] [Hashable α] (x : α) : Map α β → Prop
  | .null => False
  | .node left (y, _) right => (Hashable.hash x = y) ∨ (Mem x left) ∨ (Mem x right)

instance [Ord α] [Hashable α] : Membership α (Map α β) where
  mem := Map.Mem

instance Mem.decidableMap [DecidableEq α] [Ord α] [Hashable α] (x : α) : ∀ xs : Map α β, Decidable (x ∈ xs)
  | BinaryTree.null => by
    apply Decidable.isFalse
    simp [Membership.mem, Map.Mem]
  | BinaryTree.node left (y, v) right =>
    let hashed := Hashable.hash x
    if h : hashed = y then
      isTrue <| by
        constructor
        exact h
    else by
      have := Mem.decidableMap x left
      have := Mem.decidableMap x right
      have : (x ∈ left ∨ x ∈ right) ↔ (x ∈ BinaryTree.node left (y, v) right) := by
        simp [(· ∈ ·), Map.Mem, h]
      exact decidable_of_decidable_of_iff this

theorem Or.elimLeft (xs : α ∨ β) (x: ¬α) : β :=
  match xs with
  | Or.inl y => absurd y x
  | Or.inr b => b

def Map.get {α β : Type} [DecidableEq α] [Ord α] [Hashable α] : (x : α) → { xs : Map α β // x ∈ xs } → β
  | x, ⟨BinaryTree.node left (y, v) right, ok⟩ =>
    let hashed := Hashable.hash x
    if here : hashed = y then
      v
    else
      if l : x ∈ left then
        Map.get x ⟨ left, l ⟩
      else
        Map.get x ⟨ right, (ok.elimLeft here).elimLeft l ⟩

def Map.ofList [Hashable α] [Ord α] : List (α × β) → Map α β
| [] => Map.Empty
| (x, y) :: rest =>
  Map.insert x y (Map.ofList rest)

instance [Hashable α] [Ord α] : Coe (List (α × β)) (Map α β) where
  coe := Map.ofList
