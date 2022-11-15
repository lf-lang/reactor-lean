import Runtime
 
lf {
  reactor Main
    parameters  [p : (Nat × Nat) := (1, 2)]
    inputs      [i : Int]
    outputs     [o : Bool]
    actions     [a : String]
    state       [s : Nat := 0]
    timers      [
      {
        name t
        offset 0
        period 0
      }  
    ]
    nested      [
      n₁ : Nest := [pn : String := "first"], 
      n₂ : Nest := [pn : String := "second"]
    ]
    connections [n₁.o : n₂.i]
    reactions   [
      {
        portSources   [i, n₂.o]
        portEffects   [o, n₁.i]
        actionSources [a]
        actionEffects [a]
        triggers {
          ports   [i]
          actions [a]
          timers  [t]
          meta    [startup, shutdown]
        }
        body {
          let w ← getState  s
          let x ← getInput  i
          let y ← getInput  n₂.o
          let z ← getAction ActionSource.a
          let p ← getParam  p
          let t ← getTag
          let l ← getLogicalTime
          let q ← getPhysicalTime
          setOutput o    true
          setOutput n₁.i (-1)
          setState  s    w
          schedule  a    (.of 10 .s) "hello"
        }
      }
    ]

  reactor Nest
    parameters  [pn : String := ""]
    inputs      [i : Int]
    outputs     [o : Bool]
    actions     []
    state       []
    timers      []
    nested      []
    connections []
    reactions   []
} 

open Lean in
macro input:term " -[" rcn:term "]→ " prop:term : term =>
  `(ReactionM.Sat $input $(rcn).body (fun out => $prop out.fst))

-- TODO: 1. Turn this into an elab that reads p from the goal state.
--       2. Find a way to "output" a goal over ReactionSatisfiesM instead of SatisfiesM.
--       3. Remove the explicit goal tag, since there's only a single goal.
open Lean in
macro "resolve_bind" p:term:max proof:term : tactic => 
  `(tactic| (
      apply SatisfiesM.bind_pre
      simp [ReactionM.Input.noop]
      refine SatisfiesM.imp ?next (p := $p) (by
        intro output h
        apply SatisfiesM.pure
        revert h
        exact $proof
      )
    )
  )

open Lean Elab
elab "rcn_step" proof:term : tactic =>
  Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    match goalDecl.type.getAppArgs[9]? with
    | some prop => 
      withFreshMacroScope do
        let mvar ← Tactic.elabTerm (←`(?prop)) (expectedType? := none)
        mvar.mvarId!.assign prop
        Tactic.evalTactic (← `(tactic| resolve_bind ?prop $proof))
    | none => Meta.throwTacticEx `rcn_step goal "Couldn't apply tactic to goal"

open LF ReactionM
example : input -[Main.Reaction0]→ (·.state .s = input.state .s) := by
  simp [Main.Reaction0]

  refine ReactionM.Sat.bind 
    (prop₁ := fun out => out.fst.state Main.State.s = input.state .s ∧ out.snd = input.state .s)
    (prop₂ := fun out => out.fst.state Main.State.s = input.state .s)
    ?head ?tail ?merge
  case head => exact ReactionM.Sat.and getState_state getState_value
  case merge => intros; rw [Output.merge_state]; assumption
  case tail =>

    intro out₁ val₁ ⟨ho₁, hv₁⟩
    simp at ho₁ hv₁
    
    refine ReactionM.Sat.bind 
      (prop₁ := fun out => out.fst.state Main.State.s = input.state .s)
      (prop₂ := fun out => out.fst.state Main.State.s = input.state .s)
      ?head ?tail ?merge
    case head => rw [←ho₁]; exact ReactionM.getInput_state (input := { input with «state» := out₁.state }) 
    case merge => intros; rw [Output.merge_state]; assumption
    case tail => 
      sorry
