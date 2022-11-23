import Lean
open Lean Macro

def Array.dotted (idents : Array Ident) : MacroM (Array Term) :=
  idents.mapM fun ident => `(.$ident)

def Array.enumerate (as : Array α) : Array (Nat × α) := Id.run do
  let mut result := #[]
  for idx in [:as.size], a in as do
    result := result.push (idx, a)
  return result

def Array.uniqueMapM [Monad m] (as : Array α) (same : α → α → Bool) (f : α → m β) : m (Array β) := do
  let mut processed : Array α := #[]
  let mut result : Array β := #[]
  for a in as do
    unless processed.any (same a ·) do
      processed := processed.push a
      result := result.push (← f a)
  return result
