import Soda.Grape
import Soda.Grape.Text
import Std.Data.HashMap.Basic

open Std (HashMap)
open Grape
open Function

/--
The most important part of this was copied from [Ash](https://github.com/meoowers/ash/blob/main/Ash/JSON.lean).
I haven't used the lib directly because of a mismatch on lake-manifest versions, but
credits go to Sofia and Gabi.
-/

inductive JSON where
  | num : Int → JSON
  | bool : Bool → JSON
  | null : JSON
  | str : String → JSON
  | arr : List JSON → JSON
  | obj : List (String × JSON) → JSON
  deriving Inhabited, Repr

def JSON.token : Grape α → Grape α := Text.trailing

def JSON.pString : Grape String :=
  string "\"" *> Text.takeToStr (· != 34) <* string "\""

def JSON.number : Grape Nat :=
  Text.number

def JSON.space : Grape Unit := list (oneOf " \n\r\t") *> Grape.pure ()

partial def JSON.expr : Grape JSON := token $
        (str <$> label "string" pString)
    <|> (num <$> label "number" number)
    <|> ((λ_ => JSON.null)       <$> label "null" (string "null"))
    <|> ((λ_ => JSON.bool true)  <$> label "true" (string "true"))
    <|> ((λ_ => JSON.bool false) <$> label "false" (string "false"))
    <|> (arr <$> (string "[" *> space *> sepBy expr (space *> (token $ string ",") <* space) <* space <* (token $ string "]")))
    <|> (obj <$> (string "{" *> space *> sepBy pair (space *> (token $ string ",") <* space) <* space <* (token $ string "}")))
  where
    pair := Prod.mk <$> (JSON.pString <* (space *> (token $ string ":") <* space)) <*> expr

instance : Coe String JSON where
  coe s := JSON.str s

instance : Coe Nat JSON where
  coe n := JSON.num n

instance : Coe (List JSON) JSON where
  coe l := JSON.arr l

instance [Coe α JSON] : Coe (Option α) JSON where
  coe
    | none => JSON.null
    | some a => a

def JSON.parse (s: String) : Option JSON :=
  match Grape.run JSON.expr (s.toSlice) with
  | Result.done res _ => some res
  | _                 => none

def find [DecidableEq α] : List (α × β) → α → Option β
| [], _ => none
| (k, v) :: xs, k' => if k = k' then some v else find xs k'

abbrev AssocList (α : Type) (β : Type) := List (α × β)

def AssocList.Mem (x : α) : AssocList α β → Prop
  | [] => False
  | (y, _) :: ys => (x = y) ∨ (Mem x ys)

instance : Membership α (AssocList α β) where
  mem := AssocList.Mem

instance Mem.decidableAssocList [DecidableEq α] (x : α) : ∀ xs : List (α × β), Decidable (x ∈ xs)
| [] => by
  apply Decidable.isFalse
  simp [Membership.mem, AssocList.Mem]
| (y, v) :: ys =>
  if h : x = y then
    isTrue (Or.inl h)
  else by
    have := Mem.decidableAssocList x ys
    have : (x ∈ ys) ↔ (x ∈ (y, v) :: ys) := by
      simp [(· ∈ ·), AssocList.Mem, h]
    exact decidable_of_decidable_of_iff this

theorem Or.elimLeft (xs : α ∨ β) (x: ¬α) : β :=
  match xs with
  | Or.inl y => absurd y x
  | Or.inr b => b

def AssocList.find [DecidableEq α] : (x : α) → { xs : AssocList α β // x ∈ xs } → β
| x, ⟨ (y, v) :: ys, ok ⟩ =>
  if here : x = y then
    v
  else
    AssocList.find x ⟨ ys, Or.elimLeft ok here ⟩

instance [DecidableEq α] : GetElem (List (α × β)) α β (λ assoc elem => elem ∈ assoc) where
  getElem assoc elem proof := AssocList.find elem ⟨ assoc, proof ⟩
