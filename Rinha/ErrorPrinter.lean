import Rinha.Term
import Rinha.Type
import Mathlib.Data.String.Defs
import Lean.Data.Lsp.Utf16
import Init.Data.Format.Basic

namespace Rinha.ErrorPrinter

abbrev Location := Rinha.Term.Location
abbrev TypeError := Rinha.Type.TypeError

def getStartLine (l : Location) (s : String) : Nat :=
  ((String.take s l.start).splitOn "\n").length

def getEndLine (l : Location) (s : String) : Nat :=
  ((String.take s l.end_).splitOn "\n").length

def charsBeforeLine (l : Location) (s : String) : Nat :=
  let startLine := getStartLine l s
  let lines := String.splitOn s "\n"
  let lines := lines.take (startLine - 1)
  lines.foldl (fun acc line => acc + line.length + 1) 0

def errorArea (l : Location) (s : String) : String :=
  (String.drop s l.start).take (l.end_ - l.start)

def start (l : Location) (s : String) : String :=
  String.take s l.start

def end_ (l : Location) (s : String) : String :=
  String.drop s l.end_

def highlightError (s : String) : String := Std.Format.pretty <| Std.Format.bracket "\x1b[1;31m" s "\x1b[0m"

def highlighted (l : Location) (s : String) : String :=
  let start := start l s
  let end_ := end_ l s
  let errorArea := errorArea l s
  start ++ (highlightError errorArea) ++ end_


def insertBeforeLast (s : String) (ls : List String) : List String :=
  match ls with
  | [] => [s]
  | [x] => [s, x]
  | x :: xs => x :: (insertBeforeLast s xs)

def getMessage (t : TypeError) (s : String) : IO (List String) :=
  match t.location with
  | some l => do
    let startLine := getStartLine l s
    let endLine := getEndLine l s
    let s := highlighted l s
    let lines := String.splitOn s "\n"
    let isErrorAtEnd := lines.length == endLine
    let numberOfLines := (ToString.toString lines.length).length
    let errorMessage := highlightError <| s!"{String.replicate (numberOfLines + 1) ' '}| {t.message}"
    let lines := String.splitOn s "\n" |> List.mapIdx (fun i line => s!"{(toString (i + 1)).leftpad numberOfLines '0'} | {line}")
    let lines := lines.drop (startLine - 2)
    let lines := lines.take ((endLine - startLine) + 3)
    pure $ if isErrorAtEnd then
      (lines ++ [errorMessage])
    else
      lines |> insertBeforeLast errorMessage
  | none => pure [t.message]

end Rinha.ErrorPrinter
