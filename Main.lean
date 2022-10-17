import Runtime

lf {
  reactor Main
    parameters  []
    inputs      []
    outputs     [out : Nat]
    actions     []
    state       [count : Nat := 1]
    timers      [
      {
        name   t
        offset 0
        period some (.of 1 .s)
      }
    ]
    nested      [a₁ : A, a₂ : A]
    connections []
    reactions   [
      {
        portSources   []
        portEffects   [out]
        actionSources []
        actionEffects []
        triggers {
          ports   []
          actions []
          timers  [t]
          meta    []
        }
        body {
          let c ← getState count
          setOutput out c
          setState count (c + 1)
          monadLift <| IO.println s!"{c}"
        }
      }
    ]

  reactor A 
    parameters  [p : Nat := 10]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [c : C]
    connections []
    reactions   []

  reactor C 
    parameters  [c₁ : Bool := true, c₂ : Nat := 10]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [d : D]
    connections []
    reactions   []
  
  reactor D
  parameters  [d₁ : String := ""]
  inputs      []
  outputs     []
  actions     []
  state       []
  timers      []
  nested      []
  connections []
  reactions   []
}

def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
 