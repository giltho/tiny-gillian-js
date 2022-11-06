open Gillian
open Instantiation

module Lifter (Verification : Gillian.Abstraction.Verifier.S) =
  Gillian.Debugger.Lifter.GilLifter.Make (Verification) (Symbolic.Dummy_memory)
    (ParserAndCompiler.Dummy)

module CLI =
  Gillian.CommandLine.Make (General.Init_data.Dummy) (Cmemory) (Symbolic.Dummy_memory) (General.External.Dummy)
    (ParserAndCompiler.Dummy)
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()
