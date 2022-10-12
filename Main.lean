import Runtime

lf {
  reactor Main
    inputs      []
    outputs     []
    actions     [next : Unit]
    state       [count : Nat := 0]
    timers      [
      {
        name   t1
        offset 0
        period none
      }
    ]
    nested      []
    connections []
    reactions   [
      {
        portSources   []
        portEffects   []
        actionSources [next]
        actionEffects [next]
        triggers {
          ports   []
          actions [next]
          timers  []
          meta    [startup]
        }
        body {
          let c ← getState count
          monadLift <| IO.println s!"count: {c}"
          monadLift <| IO.println s!"logical time: {← getLogicalTime}"
          monadLift <| IO.println s!"physical time: {← getPhysicalTime}"
          setState count (c + 1)
          schedule next (.of 1 .s) ()
        }
      }
    ]
}

def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
