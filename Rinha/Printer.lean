import Rinha.Term
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

partial def Output.toString : Output → String
| Output.int i => ToString.toString i
| Output.bool b => if b then "#t" else "#f"
| Output.string s => dquotes' s
| Output.symbol s => s
| Output.list l => parens ∘ hcat <| Output.toString <$> l

instance : ToString Output := ⟨Output.toString⟩

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
| BinOp.Add => "sum"
| BinOp.Sub => "-"
| BinOp.Mul => "*"
| BinOp.Div => "/"
| BinOp.Rem => "%"
| BinOp.Eq => "safe-eq?"
| BinOp.Neq => "neq?"
| BinOp.Lt => "<"
| BinOp.Lte => "<="
| BinOp.Gt => ">"
| BinOp.Gte => ">="
| BinOp.And => "safe-and"
| BinOp.Or => "safe-or"


partial def Output.ofTerm : Term → Output
| Term.Int i => i
| Term.Boolean b => b
| Term.Str s => Output.string s
| Term.Call f args =>
  let x : List Output := Output.ofTerm f :: args.map Output.ofTerm
  Output.list x
| Term.Function ⟨ parameters, body ⟩ =>
  {"lambda", (parameters.map (·.value)), Output.ofTerm body}
| Term.If ⟨ cond, thenBranch, elseBranch ⟩ =>
  {"if", Output.ofTerm cond, Output.ofTerm thenBranch, Output.ofTerm elseBranch}
| Term.Let ⟨ name, value, body ⟩ =>
  {"letrec", {{name.value, Output.ofTerm value}}, Output.ofTerm body}
| Term.Var name => name
| Term.Tuple fst snd => {"cons", Output.ofTerm fst, Output.ofTerm snd}
| Term.First t => {"safe-car", Output.ofTerm t}
| Term.Second t => {"safe-cdr", Output.ofTerm t}
| Term.Print x => {"println", Output.ofTerm x}
| Term.Binary ⟨lhs, rhs, op⟩ => {BinOp.toSchemeOp op, Output.ofTerm lhs, Output.ofTerm rhs}

def discardTopLevel : Output → Output := λ x =>
  { "discard", x }

end Rinha.Printer
