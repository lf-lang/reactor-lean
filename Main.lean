import Runtime

lf {
  reactor Main
    inputs      []
    outputs     []
    actions     [next : Unit]
    state       [count : Nat]
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
          monadLift <| IO.println s!"{c}"
          setState count <| (c.getD 0) + 1
          schedule next (.s 1) ()
        }
      }
    ]
}

def main : IO Unit := do
  let exec : Network.Executable LF.network := { }
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
