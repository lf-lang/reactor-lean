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
          -- let q ← getPhysicalTime
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

open LF

-- TODO: Turn this into an elab that checks it the reaction is pure.
macro input:term " -[" rcn:ident "]→ " p:term : term => `($p ($(rcn).body $input).fst)

example : input -[Main.Reaction0]→ (·.state .s = input.state .s) := rfl

example : (Main.Reaction0.body input).fst.state .s = input.state .s := rfl