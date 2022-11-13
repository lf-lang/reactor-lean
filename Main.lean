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
          let w ← getState s
          let x ← getInput i
          let y ← getInput n₂.o
          let z ← getAction ActionSource.a
          let p ← getParam p
          let t ← getTag
          let l ← getLogicalTime
          let q ← getPhysicalTime
          setState s w
          setOutput o true
          setOutput n₁.i (-1)
          schedule a (.of 10 .s) "hello"
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

macro val:term " -[" i:term "]→ " p:term : term => `(ReactionM.ReactionSatisfiesM $val $i $p)

-- TODO: Have the reactions array contain the bodies, not the reaction.
open LF ReactionM
example : Main.reactions[0].val.body -[input]→ 
  (·.fst.state .s = ReactionM.Input.state input Main.State.s) := by
  let output := do
    setOutput .o true
    setOutput .n₁.i (-1 : Int)
    schedule  .a (.of 10 .s) sorry
  let x := output input
  exists (return ⟨x, by sorry⟩)
  sorry

