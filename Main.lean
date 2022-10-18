import Runtime

set_option trace.Elab.command true

lf {
  reactor Main
    parameters  [one_p : Nat := 11, two_p : Nat := 11]
    inputs      []
    outputs     []
    actions     []
    state       [one : Nat := one_p + 2, two : Nat := two_p / 2]
    timers      [
      {
        name   t
        offset 0
        period some (.of 1 .s)
      }
    ]
    nested      [c : Child := []]
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
          let o ← getState one
          let t ← getState two
          monadLift <| IO.println s!"{o}"
          monadLift <| IO.println s!"{t}"
        }
      }
    ]

  reactor Child
    parameters  [p : Nat := 1]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [g : Grandchild := []]
    connections []
    reactions   []

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
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
 