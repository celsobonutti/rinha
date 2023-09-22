import Rinha.Term
import Std.Data.HashMap.Basic
import Init.Data.Format.Basic

namespace Rinha.Printer

open Rinha.Term
open Std.Format

def dquotes' : String → String := ("\"" ++ · ++ "\"")
def dquotes : Std.Format → Std.Format := (bracket "\"" · "\"")
def parens : String → String := ("(" ++ · ++ ")")
def hcat : List String → String := String.intercalate " "
def vcat' : List String → String := String.intercalate "\n"
def vcat : List Std.Format → Std.Format := (Std.Format.joinSep · Std.Format.line)

inductive Output
| int : Int → Output
| bool : Bool → Output
| string : String → Output
| list : List Output → Output
| symbol : String → Output
deriving Inhabited, Repr

partial def Output.format : Output → Std.Format
| Output.int i => Std.Format.text <| toString i
| Output.bool b => Std.Format.text <| if b then "#t" else "#f"
| Output.string s => dquotes s
| Output.symbol s => Std.Format.text s
| Output.list l => Std.Format.group (Std.Format.paren <| Std.Format.joinSep (l.map Output.format) " ")

instance : ToString Output := ⟨pretty ∘ Output.format⟩

instance : Std.ToFormat Output := ⟨Output.format⟩

instance : Coe Bool Output := ⟨Output.bool⟩
instance : Coe Int Output := ⟨Output.int⟩
instance : Coe String Output := ⟨Output.symbol⟩
instance [Coe α Output] : Coe (List α) Output := ⟨Output.list ∘ List.map Coe.coe⟩
instance : Coe (List Output) Output := ⟨Output.list⟩
instance : Coe Nat Output := ⟨Output.int ∘ Int.ofNat⟩
instance : OfNat Output n := ⟨Output.int <| Int.ofNat <| n⟩

syntax (priority := high) "{" term,+ "}" : term

/- Declares two expansions/syntax transformers -/
macro_rules
  | `({$x}) => `([($x : Output)])
  | `({$x, $xs:term,*}) => `(($x : Output) :: {$xs,*})

def BinOp.toSchemeOp : BinOp → String
| BinOp.Add => "__builtin__sum"
| BinOp.Sub => "-"
| BinOp.Mul => "*"
| BinOp.Div => "/"
| BinOp.Rem => "%"
| BinOp.Eq => "__builtin__eq?"
| BinOp.Neq => "__builtin__neq?"
| BinOp.Lt => "<"
| BinOp.Lte => "<="
| BinOp.Gt => ">"
| BinOp.Gte => ">="
| BinOp.And => "__builtin__and"
| BinOp.Or => "__builtin__or"

partial def isPure (hash : Std.HashMap String Bool) : Term → Bool
| Term.Int _ _ => true
| Term.Boolean _ _ => true
| Term.Str _ _ => true
| Term.Call _ f args => isPure hash f && args.all (isPure hash)
| Term.Function _ ⟨ parameters, body ⟩ =>
  if Rinha.Term.isParameterBeingCalled (parameters.map (·.value)) body -- We can't memoize functions that call other functions because I'm lazy
    then
      false
    else
      let hash := List.foldl (λ hash p => hash.insert p.value true) hash parameters
      isPure hash body
| Term.If _ ⟨ cond, thenBranch, elseBranch ⟩ => isPure hash cond && isPure hash thenBranch && isPure hash elseBranch
| Term.Let _ ⟨ _, value, _ ⟩ => isPure hash value
| Term.Var _ name => match hash.find? name with
  | some isPure => isPure
  | none => panic! s!"Variable {name} not found, {reprStr hash.toList}"
| Term.Tuple _ fst snd => isPure hash fst && isPure hash snd
| Term.First _ t => isPure hash t
| Term.Second _ t => isPure hash t
| Term.Print _ _ => false
| Term.Binary _ ⟨lhs, rhs, _⟩ => isPure hash lhs && isPure hash rhs


partial def Output.ofTerm (hash : Std.HashMap String Bool) : Term → Output
| Term.Int _ i => i
| Term.Boolean _ b => b
| Term.Str _ s => Output.string s
| Term.Call _ f args =>
  let x : List Output := Output.ofTerm hash f :: args.map (Output.ofTerm hash)
  Output.list x
| l@(Term.Function _ ⟨ parameters, body ⟩) =>
  let isPure := isPure hash l
  let hash := List.foldl (λ hash x => hash.insert x.value true) hash parameters
  if isPure
  then {"__builtin__memoize", {"lambda", (parameters.map (·.value)), Output.ofTerm hash body}}
  else {"lambda", (parameters.map (·.value)), Output.ofTerm hash body}
| Term.If _ ⟨ cond, thenBranch, elseBranch ⟩ =>
  {"if", { "fail-if-not-bool", Output.ofTerm hash cond}, Output.ofTerm hash thenBranch, Output.ofTerm hash elseBranch}
| x@(Term.Let _ ⟨ name, f@(Term.Function _ ⟨ parameters, _ ⟩), next ⟩) =>
  let isRecursive := x.isRecursiveFunction
  let hash := if isRecursive then hash.insert name.value true else hash
  let hash := List.foldl (λ hash p => hash.insert p.value true) hash parameters
  let isPure := isPure hash x
  let hash := hash.insert name.value isPure
  let kindOfLet := if isRecursive then "letrec" else "let"
  {kindOfLet, {{name.value, Output.ofTerm hash f}}, Output.ofTerm hash next}
| x@(Term.Let _ ⟨ name, value, next ⟩) =>
  let isRecursive := x.isRecursiveFunction
  let hash := if isRecursive then hash.insert name.value true else hash
  let isPure := isPure hash x
  let hash := hash.insert name.value isPure
  let kindOfLet := if isRecursive then "letrec" else "let"
  {kindOfLet, {{name.value, Output.ofTerm hash value}}, Output.ofTerm hash next}
| Term.Var _ name => name
| Term.Tuple _ fst snd => {"cons", Output.ofTerm hash fst, Output.ofTerm hash snd}
| Term.First _ t => {"__builtin__car", Output.ofTerm hash t}
| Term.Second _ t => {"__builtin__cdr", Output.ofTerm hash t}
| Term.Print _ x => {"__builtin__println", Output.ofTerm hash x}
| Term.Binary _ ⟨lhs, rhs, op⟩ => {BinOp.toSchemeOp op, Output.ofTerm hash lhs, Output.ofTerm hash rhs}

def discardTopLevel : Output → Output := λ x =>
  { "discard", x }

end Rinha.Printer
