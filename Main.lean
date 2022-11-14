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
macro input:term " -[" rcn:ident "]→ " prop:term : term =>
  `($(mkIdent `ReactionSatisfiesM) $input $(mkIdentFrom rcn <| `LF ++ rcn.getId ++ `body) $prop)

-- TODO: 0. Generalize this to use `SatisfiesM.bind`.
--       1. Turn this into an elab that reads p from the goal state.
--       2. Find a way to "output" a goal over ReactionSatisfiesM instead of SatisfiesM.
--       3. Remove the explicit goal tag, since there's only a single goal.
open Lean in
macro "resolve_bind" p:term:max proof:term : tactic => 
  `(tactic| (
      apply SatisfiesM.bind_pre
      simp [$(mkIdent `Input.noop):ident]
      refine SatisfiesM.imp ?next (p := $p) (by
        intro output h
        apply SatisfiesM.pure
        revert h
        exact $proof
      )
    )
  )

open LF ReactionM
example : input -[Main.Reaction0]→ (·.fst.state .s = input.state .s) := by
  simp [Main.Reaction0]
  iterate 7 resolve_bind (·.fst.state .s = input.state .s) (by rw [Output.merge_state, ·])
  apply SatisfiesM.bind (p := (·.fst.state .s = input.state .s))
  · resolve_bind (fun _ => True) (by simp)
    exact SatisfiesM.trivial
  · simp [Input.noop]
    intro output h
    iterate 4 resolve_bind (·.fst.state .s = input.state .s) (by rw [Output.merge_state, ·])
    apply SatisfiesM.pure
    simp [h]
