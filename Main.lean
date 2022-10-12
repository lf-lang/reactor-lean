import Runtime

lf {
  reactor Main
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
    nested      []
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
}

def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
