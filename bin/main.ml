open Gillian
open Tinygjs

module SMemory = Gillian.Monadic.MonadicSMemory.Lift(Smemory)

module Lifter (Verification : Gillian.Abstraction.Verifier.S) =
  Gillian.Debugger.Lifter.GilLifter.Make (Verification) (SMemory)
    (ParserAndCompiler.Dummy)

module CLI =
  Gillian.CommandLine.Make (General.Init_data.Dummy) (Cmemory)
    (SMemory)
    (General.External.Dummy)
    (ParserAndCompiler.Dummy)
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()
