import Runtime

-- set_option trace.Elab.command true

lf {
  reactor Main
    parameters  []
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [c : Child := [xyz : Nat := 23]]
    connections []
    reactions   []

  reactor Child
    parameters  [xyz : Nat := 1]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [g : Grandchild := []]
    connections []
    reactions   [
      {
        portSources   []
        portEffects   []
        actionSources []
        actionEffects []
        triggers {
          ports   []
          actions []
          timers  []
          meta    [startup]
        }
        body {
          monadLift <| IO.println s!"{← getParam xyz}"
        }
      }
    ]

  reactor Grandchild
    parameters  [a : Nat := 2]
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
  let topo : Array (Network.ReactionID LF.network) := #[⟨.cons .c <| .nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
 