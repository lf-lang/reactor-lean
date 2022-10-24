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
    nested      [c : Child := [xyz : Nat := 5]]
    connections []
    reactions   []

  reactor Child
    parameters  [xyz : Nat := 1]
    inputs      []
    outputs     []
    actions     []
    state       [s : Nat := 0]
    timers      []
    nested      [g : Grandchild := [a : Nat := xyz]]
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
          monadLift <| IO.println s!"c: {← getParam xyz}"
        }
      }
    ]

  reactor Grandchild
    parameters  [a : Nat := 1]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      [ 
      { 
        name t 
        offset (.of 5 .s) 
        period some (.of a .s) 
      } 
    ]
    nested      []
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
          timers  [t]
          meta    [startup]
        }
        body {
          return
          -- monadLift <| IO.println s!"g: {← getParam a}"
        }
      }
    ]
}

def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionID LF.network) := #[
    ⟨.cons .c <| .nil,             ⟨0, by simp⟩⟩, 
    ⟨.cons .c <| .cons .g <| .nil, ⟨0, by simp⟩⟩
  ]
  exec.run topo 0
 