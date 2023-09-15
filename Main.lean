import Rinha
import Init.Data.Repr
import Init.System.FilePath

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

def typeCheck (program : Rinha.Term.Program) : IO Unit := do
  let e := program.expression
  let expr := Rinha.Type.Expr.ofTerm e
  let (res, _) ← Rinha.Type.runTI (Rinha.Type.typeInference {} expr)
  match res with
  | Except.ok _ => pure ()
  | Except.error e => IO.println e

def codegen (program : Rinha.Term.Program) : IO Unit := do
  let baseCode ← IO.FS.readFile "base.scm"
  let fileName := (System.FilePath.mk program.name).withExtension "scm"
  let file ← IO.FS.Handle.mk fileName IO.FS.Mode.write
  let e := program.expression
  let output :=
    Rinha.Printer.vcat
      [ baseCode
      , Rinha.Printer.Output.ofTerm e |> ToString.toString
      ]
  file.putStr output

inductive KindOfFile where
| json
| rinha

def System.FilePath.kindOfFile (path : System.FilePath) : KindOfFile :=
  match path.extension with
  | Option.some "json" => KindOfFile.json
  | _ => KindOfFile.rinha -- We'll try to compile anything else as a Rinha file

def compile (path : System.FilePath) : IO Unit := do
  let rawJSON ← match path.kindOfFile with
    | KindOfFile.json => IO.FS.readFile path
    | KindOfFile.rinha => IO.Process.run { cmd := "rinha", args := #[path.toString] }
  let json ← parseWithIOError rawJSON
  let program ← convertWithIOError json
  typeCheck program
  codegen program

def printRepr [Repr α] : α → IO Unit := IO.println ∘ repr

def files : List System.FilePath := ["files/fib.rinha", "files/sum.json", "files/combination.json", "files/type-fail.rinha"]

def main : IO Unit := files.mapM compile *> pure ()
