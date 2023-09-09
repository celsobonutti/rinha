import Soda.Grape
import Soda.Grape.Text
import Map

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
  | obj : Map String JSON → JSON
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
