import Lean
open Lean Macro

def Array.dotted (idents : Array Ident) : MacroM (Array Term) :=
  idents.mapM fun ident => `(.$ident)

def Array.enumerate (as : Array α) : Array (Nat × α) := Id.run do
  let mut result := #[]
  for idx in [:as.size], a in as do
    result := result.push (idx, a)
  return result