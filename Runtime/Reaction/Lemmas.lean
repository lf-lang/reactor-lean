import Runtime.Reaction.Monad

namespace ReactionT

open Lean in
scoped macro "mk_get_lemmas" op:ident field:ident param:"_"? : command => do
  let var := if param.isSome then #[mkIdent `var] else #[]
  let input := mkIdent `input
  let opApp ← `($op $[ $var ]* $input (m := Id)
    (σPS := $(mkIdent `σPS)) (σPE := $(mkIdent `σPE))
    (σAS := $(mkIdent `σAS)) (σAE := $(mkIdent `σAE))
    (σS  := $(mkIdent  `σS)) (σP  := $(mkIdent  `σP))
  )
  let lemmas := #[
    ("value",        ← `(($opApp).snd = $input.$field $[ $var ]*)),
    ("state",        ← `(($opApp).fst.state = $(input).state)),
    ("ports",        ← `(($opApp).fst.ports.isEmpty)),
    ("events",       ← `(($opApp).fst.events.isEmpty)),
    ("writtenPorts", ← `(($opApp).fst.writtenPorts.isEmpty))
  ]
  let commands ← lemmas.mapM fun ⟨suffix, property⟩ => `(
    @[simp] theorem $(mkIdentFrom op s!"{op.getId}_{suffix}") {$[ $var ]*} : $property := rfl
  )
  return ⟨mkNullNode commands⟩

mk_get_lemmas getInput       ports   _
mk_get_lemmas getState       state   _
mk_get_lemmas getAction      actions _
mk_get_lemmas getParam       params  _
mk_get_lemmas getTag         tag
mk_get_lemmas getLogicalTime time

-- TODO: Lemmas for `setOutput`, `setState`, `schedule` and `requestStop`.

@[simp] theorem setOutput_same_port : (setOutput (m := Id) (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) var val input).fst.ports var = val := by
  simp [setOutput]

@[simp] theorem setOutput_other_port {var var' val} : (var' ≠ var) → (setOutput (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) var val input).fst.ports var' = none :=
  (by simp [setOutput, ·])

@[simp] theorem setState_same_state : (setState (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) stv v input).fst.state stv = v := by
  simp [setState]

@[simp] theorem setState_other_state {stv stv' v} : (stv' ≠ stv) → (setState (σPS := σPS) (σPE := σPE) (σAS := σAS) (σAE := σAE) (σS := σS) (σP := σP) (m := Id) stv v input).fst.state stv' = input.state stv' := by
  intro h
  simp [setState, h]

end ReactionT
