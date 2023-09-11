import Init.Data.Int.Basic

inductive Map (α β : Type) [Hashable α] where
  | empty : Map α β
  | node : Map α β → (UInt64 × β) → Map α β → Map α β
  deriving Repr

namespace Map

def getOption {α β : Type} [Hashable α] : α → Map α β → Option β
| _, empty => Option.none
| x, node left (y, value) right =>
  match Ord.compare (Hashable.hash x) y with
  | Ordering.eq => Option.some value
  | Ordering.lt => getOption x left
  | Ordering.gt => getOption x right

def insert {α β : Type} [Hashable α] : Map α β → α → β → Map α β
| empty, x, y => node empty (Hashable.hash x, y) empty
| node left (key, value) right, x, y =>
  let
    hashed := Hashable.hash x
  match Ord.compare hashed key with
  | Ordering.eq => node left (hashed, y) right
  | Ordering.lt => node (left.insert x y) (key, value) right
  | Ordering.gt => node left (key, value) (right.insert x y)

def Mem [Hashable α] (x : α) : Map α β → Prop
  | .empty => False
  | .node left (y, _) right => (Hashable.hash x = y) ∨ (Mem x left) ∨ (Mem x right)

instance [Hashable α] : Membership α (Map α β) where
  mem := Mem

instance Mem.decidableMap [DecidableEq α] [Hashable α] (x : α) : ∀ xs : Map α β, Decidable (x ∈ xs)
  | empty => by
    apply Decidable.isFalse
    simp [Membership.mem, Mem]
  | node left (y, v) right =>
    let hashed := Hashable.hash x
    if h : hashed = y then
      isTrue <| by
        constructor
        exact h
    else by
      have := Mem.decidableMap x left
      have := Mem.decidableMap x right
      have : (x ∈ left ∨ x ∈ right) ↔ (x ∈ node left (y, v) right) := by
        simp [(· ∈ ·), Mem, h]
      exact decidable_of_decidable_of_iff this

theorem Or.elimLeft (xs : α ∨ β) (x: ¬α) : β :=
  match xs with
  | Or.inl y => absurd y x
  | Or.inr b => b

def get {α β : Type} [DecidableEq α] [Hashable α] : (x : α) → { xs : Map α β // x ∈ xs } → β
  | x, ⟨node left (y, v) right, ok⟩ =>
    let hashed := Hashable.hash x
    if here : hashed = y then
      v
    else
      if l : x ∈ left then
        get x ⟨ left, l ⟩
      else
        get x ⟨ right, Map.Or.elimLeft (Map.Or.elimLeft ok here) l ⟩

def ofList [Hashable α] : List (α × β) → Map α β
| [] => empty
| (x, y) :: rest =>
  (ofList rest).insert x y

instance [Hashable α] : Coe (List (α × β)) (Map α β) where
  coe := ofList

theorem belongIff [Hashable α] {x : α} {xs : Map α β} : x ∈ xs ↔ Mem x xs := by
  simp [(·∈·)];

theorem belongs {α β : Type} [Hashable α] {y : β} {left right : Map α β} : ∀ {x : α}, x ∈ node left (hash x, y) right := by
  intro x;
  simp [(·∈·), Mem];

theorem belongsL {α β : Type} [Hashable α] { n : UInt64 × β } {left right : Map α β} : ∀ {x : α}, x ∈ left → x ∈ node left n right := by
  intro x
  intro belong
  simp [(·∈·), Mem, Iff.mp belongIff belong]

theorem belongsR {α β : Type} [Hashable α] { n : UInt64 × β } {left right : Map α β} : ∀ {x : α}, x ∈ right → x ∈ node left n right := by
  intro x
  intro belong
  simp [(·∈·), Mem, Iff.mp belongIff belong]

def insertP {α β : Type} [Hashable α] : (x : α) → β → Map α β → { xs : Map α β // x ∈ xs }
| x, y, empty => ⟨ node empty (Hashable.hash x, y) empty, belongs ⟩
| x, y, node left (key, value) right =>
  let
    hashed := Hashable.hash x
  match Ord.compare hashed key with
  | Ordering.eq =>
    ⟨ node left (hashed, y) right, belongs ⟩
  | Ordering.lt =>
    let ins := insertP x y left
    match ins with
    | ⟨ l, p ⟩ =>
      ⟨ node l (key, value) right, belongsL p ⟩
  | Ordering.gt =>
  let ins := insertP x y right
  match ins with
    | ⟨ r, p ⟩ =>
      ⟨ node left (key, value) r, belongsR p ⟩

instance [Hashable α] [DecidableEq α] : GetElem (Map α β) α β (λ map elem => elem ∈ map) where
  getElem map elem proof := get elem ⟨ map, proof ⟩

end Map
