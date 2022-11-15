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

-- TODO: Factor out the proof component into a theorem on `ReactionM.Sat`.
open Lean Elab
elab "irrelevant" merge:term : tactic =>
  Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    match goalDecl.type.getAppArgs[9]? with
    | some prop => 
      withFreshMacroScope do
        let mvar ← Tactic.elabTerm (←`(?prop)) (expectedType? := none)
        mvar.mvarId!.assign prop
        Tactic.evalTactic (← `(tactic| (
          refine ReactionM.Sat.bind (prop₁ := fun _ => True) (prop₂ := ?prop) SatisfiesM.trivial ?_ $merge;
          intro out x₁ x₂; clear x₁ x₂; simp
        )))
    | none => Meta.throwTacticEx `rcn_step goal "Couldn't apply tactic to goal"


open LF ReactionM
example : input -[Main.Reaction0]→ (·.state .s = input.state .s) := by
  simp [Main.Reaction0]

  refine ReactionM.Sat.bind 
    (prop₁ := fun out => out.snd = input.state .s)
    (prop₂ := fun out => out.fst.state Main.State.s = input.state .s)
    ?head ?_ ?merge
  case head => exact getState_value
  case merge => intros; rw [Output.merge_state]; assumption
  
  intro out val h
  subst h
  
  iterate 9 irrelevant by intros; rw [Output.merge_state]; assumption
  sorry
  

