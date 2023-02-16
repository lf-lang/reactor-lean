import Runtime.Utilities.Std

open Lean Meta Elab Term Command in
elab (name := runCmd) "run_cmd " elems:doSeq : command => do
  ← liftTermElabM <|
    unsafe evalTerm (CommandElabM Unit)
      (mkApp (mkConst ``CommandElabM) (mkConst ``Unit))
      (← `(discard do $elems))
