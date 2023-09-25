import Lean.Data.Json.Basic
import Init.Data.Format.Basic
import Std.Data.HashMap.Basic
import Rinha
import Init.Data.Repr
import Init.System.FilePath

open Rinha.Printer
open Rinha.Optimize
open Rinha.ErrorPrinter

def parseWithIOError (value : String) : IO Lean.Json := do
  match Lean.Json.parse value with
  | Except.ok json => pure json
  | Except.error error => throw (IO.userError s!"Invalid JSON value: {error}")

def convertWithIOError (value : Lean.Json) : IO Rinha.Term.Program := do
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


def codegen (program : Rinha.Term.Program) (output : Option System.FilePath): IO System.FilePath := do
  let baseCode ← IO.FS.readFile "base.rkt"
  let name := output.getD program.name
  let fileName := name.withExtension "rkt"
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

def compile (path : System.FilePath) (output : Option System.FilePath) : IO System.FilePath := do
  let rawJSON ← match path.kindOfFile with
    | KindOfFile.json => IO.FS.readFile path
    | KindOfFile.rinha => do
      let process ← IO.Process.output { cmd := "rinha", args := #[path.toString] }
      if process.exitCode == 0 then
        pure process.stdout
      else
        IO.eprintln process.stderr
        throw (IO.userError s!"Compilation failed with exit code {process.exitCode}")
  let json ← parseWithIOError rawJSON
  let program ← convertWithIOError json
  let optimizedProgram := program.optimize
  typeCheck optimizedProgram
  codegen optimizedProgram output

inductive Arg where
| toRacket : Arg
| run : Arg
| file : String → Arg
| output : String → Arg
deriving Inhabited, DecidableEq

structure Command where
  toRacket : Bool
  run : if toRacket then Unit else Bool
  file : String
  output : Option String

def parseArgs : List String → List Arg
| [] => []
| "--to-racket" :: xs => Arg.toRacket :: parseArgs xs
| "--run" :: xs => Arg.run :: parseArgs xs
| "-o" :: output :: xs => Arg.output output :: parseArgs xs
| fileName :: xs => Arg.file fileName :: parseArgs xs

def getFile (arg : Arg) : Option String :=
  match arg with
  | Arg.file name => name
  | _ => none

def getOutput (arg : Arg) : Option String :=
  match arg with
  | Arg.output name => name
  | _ => none

def parseCommand (args : List Arg) : IO Command :=
match args.findSome? getFile with
| none => throw (IO.userError "No file given")
| some fileName =>
    let output := List.findSome? getOutput args
    let toRacket := List.elem Arg.toRacket args
    let run := List.elem Arg.run args
    match (toRacket, run) with
    | (true, _) => pure { toRacket := true, run := (), file := fileName, output := output }
    | (false, true) => pure { toRacket := false, run := true, file := fileName, output := output }
    | (false, false) => pure { toRacket := false, run := false, file := fileName, output := output }

def main (args : List String) : IO Unit := do
let command ← args |> parseArgs |> parseCommand
match command with
| { toRacket := true, file, output .. } =>
  let outputFileName ← compile file output
  IO.println s!"Compiled racket output to {outputFileName}"
  pure ()
| { toRacket := false, run := true, file, output } =>
  let outputFileName ← compile file output
  let io ← IO.Process.output { cmd := "racket", args := #[outputFileName.toString] }
  if io.exitCode == 0 then
    IO.println io.stdout
  else
    IO.eprintln s!"Compilation failed with exit code {io.exitCode}"
    IO.eprintln io.stderr
  IO.FS.removeFile outputFileName
| { toRacket := false, run := false, file, output } =>
  let outputFileName ← compile file output
  let io ← IO.Process.output { cmd := "raco", args := #["exe", outputFileName.toString] }
  if io.exitCode == 0 then
    IO.println s!"Compiled to {outputFileName.withExtension System.FilePath.exeExtension}"
  else
    IO.eprintln s!"Compilation failed with exit code {io.exitCode}"
    IO.eprintln io.stderr
  IO.FS.removeFile outputFileName
  pure ()
