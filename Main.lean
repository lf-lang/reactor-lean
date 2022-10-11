import Runtime

lf {
  reactor Main
    inputs      []
    outputs     []
    actions     [next : Unit]
    state       [count : Nat := 0]
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
          meta    [startup]
        }
        body {
          let c ← getState count
          monadLift <| IO.println s!"count: {c}"
          monadLift <| IO.println s!"logical time: {← getLogicalTime}"
          monadLift <| IO.println s!"physical time: {← getPhysicalTime}"
          setState count <| (c.getD 0) + 1
          schedule next (.s 1) ()
        }
      }
    ]
}

def main : IO Unit := do
  let exec := LF.executable <| .ns (← IO.monoNanosNow)
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
