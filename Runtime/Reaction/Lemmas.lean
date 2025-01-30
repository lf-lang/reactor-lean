import Runtime.Reaction.Monad

/-
This file contains a variety of trivial lemmas about the monadic operations defined for `ReactionT`.
-/

namespace ReactionT

/--
This macro should be used by LF-users to prove theorems about reactions. It makes it possible to
write `input -[ReactorName.ReactionN]→ output` to express that running reaction number N of reactor
(class) `ReactorName` on a given `input` produces `output`.
-/
macro input:term:max " -[" rcn:ident "]→ " output:term:max : term => `(
  ($(Lean.mkIdentFrom rcn <| `LF ++ rcn.getId ++ `body) $input).fst = $output
)

-- TODO: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Conditional.20Syntax/near/311857316
open Lean in
macro "mk_get_lemmas" op:ident field:ident var:"_"? : command => do
  let var := if var.isSome then #[mkIdent `var] else #[]
  let input := mkIdent `input
  let opApp ← `($op $[ $var ]* $input (m := Id)
    (σPS := $(mkIdent `σPS)) (σPE := $(mkIdent `σPE))
    (σAS := $(mkIdent `σAS)) (σAE := $(mkIdent `σAE))
    (σS  := $(mkIdent  `σS)) (σP  := $(mkIdent  `σP))
  )
  let lemmas := #[
    ("value",         ← `(($opApp).snd = $input.$field $[ $var ]*)),
    ("state",         ← `(($opApp).fst.state = $(input).state)),
    ("ports",         ← `(($opApp).fst.ports.isEmpty)),
    ("events",        ← `(($opApp).fst.events.isEmpty)),
    ("stopRequested", ← `(($opApp).fst.stopRequested = false)),
    ("writtenPorts",  ← `(($opApp).fst.writtenPorts.isEmpty))
  ]
  let commands ← lemmas.mapM fun ⟨suffix, property⟩ => `(
    @[simp] theorem $(mkIdentFrom op (.mkSimple s!"{op.getId}_{suffix}")) {$[ $var ]*} : $property := rfl
  )
  return ⟨mkNullNode commands⟩

open Lean in
macro "mk_set_lemma" op:ident suffix:ident " : " prop:term : command => `(
  @[simp] theorem $(mkIdentFrom op (.mkSimple s!"{op.getId}_{suffix.getId}")) : $prop := by
    simp [$op:ident]; first | done | rfl | intro h; simp [h]
)

mk_get_lemmas getInput       ports   _
mk_get_lemmas getState       state   _
mk_get_lemmas getAction      actions _
mk_get_lemmas getParam       params  _
mk_get_lemmas getTag         tag
mk_get_lemmas getLogicalTime time

mk_set_lemma setOutput state : (setOutput (m := Id) (σAE := σAE) var val input).fst.state = input.state
mk_set_lemma setOutput same_port : (setOutput (m := Id) (σAE := σAE) var val input).fst.ports var = some val

@[simp] theorem setOutput_other_port {var' var val} : (var' ≠ var) →
  (setOutput (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.ports var' = none :=
  by simp [setOutput]; first | done | rfl | intro h; simp [h]

mk_set_lemma setOutput events : (setOutput (m := Id) (σAE := σAE) var val input).fst.events.isEmpty
mk_set_lemma setOutput stopRequested : (setOutput (m := Id) (σAE := σAE) var val input).fst.stopRequested = false
mk_set_lemma setOutput writtenPorts : (setOutput (m := Id) (σAE := σAE) var val input).fst.writtenPorts = #[var]

mk_set_lemma setState same_state : (setState (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.state var = val

@[simp] theorem setState_other_state {var' var val} : (var' ≠ var) →
  (setState (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.state var' = input.state var' :=
  by simp [setState]; first | done | rfl | intro h; simp [h]

mk_set_lemma setState ports : (setState (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.ports.isEmpty
mk_set_lemma setState events : (setState (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.events.isEmpty
mk_set_lemma setState stopRequested : (setState (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.stopRequested = false
mk_set_lemma setState writtenPorts : (setState (m := Id) (σPE := σPE) (σAE := σAE) var val input).fst.writtenPorts.isEmpty

-- TODO: Lemmas for `schedule` and `requestStop`.

end ReactionT
