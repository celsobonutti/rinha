import Rinha
import Init.Data.Repr

def parseWithIOError (value : String) : IO JSON := do
  match JSON.parse value with
  | Option.some json => pure json
  | Option.none => throw (IO.userError "Invalid JSON value")

def convertWithIOError (value : JSON) : IO Rinha.Term.Program := do
  match Rinha.Term.Program.from_JSON value with
  | Except.ok term => pure term
  | Except.error error => throw (IO.userError error)

def parseAndConvert (fileName : String) : IO Rinha.Term.Program := do
  let read ← IO.FS.readFile fileName
  let json ← parseWithIOError read
  convertWithIOError json

def printRepr [Repr α] : α → IO Unit := IO.println ∘ repr

def main : IO Unit := do
  let rinha ← parseAndConvert "rinha.json"
  printRepr rinha
  let fib ← parseAndConvert "fib.json"
  printRepr fib
  let sum ← parseAndConvert "sum.json"
  printRepr sum
