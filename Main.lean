import Runtime

lf {
  reactor Main
    parameters  []
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [
      c : Client := [],
      s : Server := []
    ]
    connections [
        c.out : s.in := .of 1 .ns,
        s.out : c.in
      ]
    reactions   []

  reactor Server
    parameters  []
    inputs      [«in» : Int]
    outputs     [out : Int]
    actions     [err : Unit]
    state       [error : Int]
    timers      []
    nested      []
    connections []
    reactions   [
      {
        kind          pure
        portSources   [«in»]
        portEffects   [out]
        actionSources []
        actionEffects [err]
        triggers {
          ports   [«in»]
          actions []
          timers  []
          meta    []
        }
        body {
          match ← getInput «in» with
          | none   => schedule err 0 ()
          | some i => setOutput out i
        }
      },
      {
        kind          pure
        portSources   []
        portEffects   []
        actionSources [err]
        actionEffects []
        triggers {
          ports   []
          actions [err]
          timers  []
          meta    []
        }
        body {
          setState error (1 : Int)
        }
      }
    ]

  reactor Client
    parameters  []
    inputs      [«in» : Int]
    outputs     [out : Int]
    actions     []
    state       [req : Int := 0]
    timers      []
    nested      []
    connections []
    reactions   [
      {
        kind          pure
        portSources   []
        portEffects   [out]
        actionSources []
        actionEffects []
        triggers {
          ports   []
          actions []
          timers  []
          meta    [startup]
        }
        body {
          setState req (0 : Int)
          setOutput out (← getState req)
        }
      },
      {
        kind          pure
        portSources   [«in»]
        portEffects   []
        actionSources []
        actionEffects []
        triggers {
          ports   [«in»]
          actions []
          timers  []
          meta    []
        }
        body {
          setState req (0 : Int)
        }
      }
    ]
}

def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionId LF.network) := #[
    ⟨.cons ⟨.c⟩ <| .nil, ⟨0, by simp⟩⟩,
    ⟨.cons ⟨.s⟩ <| .nil, ⟨0, by simp⟩⟩,
    ⟨.cons ⟨.s⟩ <| .nil, ⟨1, by simp⟩⟩,
    ⟨.cons ⟨.c⟩ <| .nil, ⟨1, by simp⟩⟩
  ]
  exec.run topo 0
