import Init.Data.Format.Basic
import Std.Data.HashMap.Basic
import Rinha
import Init.Data.Repr
import Init.System.FilePath

open Rinha.Printer
open Rinha.Optimize
open Rinha.ErrorPrinter

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
  let (res, _) ← Rinha.Type.runTI (Rinha.Type.typeInference {} e)
  match res with
  | Except.ok _ => pure ()
  | Except.error e => do
    match e.location with
    | Option.some _ => do
      let file <- IO.FS.readFile program.name
      let err ← Rinha.ErrorPrinter.getMessage e file
      throw (IO.userError ("Type error" ++ "\n" ++ (String.intercalate "\n" err)))

    | Option.none =>
      e
      |> toString
      |> IO.userError
      |> throw


def codegen (program : Rinha.Term.Program) : IO System.FilePath := do
  let baseCode ← IO.FS.readFile "base.rkt"
  let fileName := (System.FilePath.mk program.name).withExtension "rkt"
  let file ← IO.FS.Handle.mk fileName IO.FS.Mode.write

  let e := program.expression
  let output :=
    Rinha.Printer.vcat
      [ Std.Format.text baseCode
      , Rinha.Printer.Output.format <| Rinha.Printer.discardTopLevel (Rinha.Printer.Output.ofTerm {} e)
      ]
      |> Std.Format.pretty
  file.putStr output
  pure fileName

inductive KindOfFile where
| json
| rinha

def System.FilePath.kindOfFile (path : System.FilePath) : KindOfFile :=
  match path.extension with
  | Option.some "json" => KindOfFile.json
  | _ => KindOfFile.rinha -- We'll try to compile anything else as a Rinha file

def compile (path : System.FilePath) : IO System.FilePath := do
  let rawJSON ← match path.kindOfFile with
    | KindOfFile.json => IO.FS.readFile path
    | KindOfFile.rinha => IO.Process.run { cmd := "rinha", args := #[path.toString] }
  let json ← parseWithIOError rawJSON
  let program ← convertWithIOError json
  let optimizedProgram := program.optimize
  typeCheck optimizedProgram
  codegen optimizedProgram

def main : List String → IO Unit
| [] => IO.eprintln "No file given"
| [fileName] => do
  let outputFileName ← compile fileName
  let io ← IO.Process.output { cmd := "raco", args := #["exe", outputFileName.toString] }
  if io.exitCode == 0 then
    IO.println s!"Compiled to {outputFileName.withExtension System.FilePath.exeExtension}"
  else
    IO.eprintln s!"Compilation failed with exit code {io.exitCode}"
    IO.eprintln io.stderr
  IO.FS.removeFile outputFileName
  pure ()
| ["--to-racket", fileName] => do
  let outputFileName ← compile fileName
  IO.println s!"Compiled racket output to {outputFileName}"
  pure ()
| ["--run", fileName] => do
  let outputFileName ← compile fileName
  let io ← IO.Process.output { cmd := "racket", args := #[outputFileName.toString] }
  if io.exitCode == 0 then
    IO.println io.stdout
  else
    IO.eprintln s!"Compilation failed with exit code {io.exitCode}"
    IO.eprintln io.stderr
  IO.FS.removeFile outputFileName
| _ => IO.eprintln "Too many arguments"
