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
          IO.println s!"{c}"
        }
      }
    ]
}

def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0








#synth MonadLift IO (
  ReactionM (Interface.Scheme.restrict (Network.Graph.reactionInputScheme LF.graph .Main) LF.Main.Reaction0.PortSource)
    (Interface.Scheme.restrict (Network.Graph.reactionOutputScheme LF.graph .Main) LF.Main.Reaction0.PortEffect)
    (Interface.Scheme.restrict (Network.Graph.interface LF.graph .Main Reactor.InterfaceKind.actions) LF.Main.Reaction0.ActionSource)
    (Interface.Scheme.restrict (Network.Graph.interface LF.graph .Main Reactor.InterfaceKind.actions) LF.Main.Reaction0.ActionEffect)
    (Network.Graph.interface LF.graph .Main Reactor.InterfaceKind.state)
)



structure In : Type
structure Out : Type

def ThingM (n₁ n₂ : Nat) (α : Type) := In → IO (α × Out)

instance : Monad (ThingM n₁ n₂) := sorry
instance : MonadLift IO (ThingM n₁ n₂) := sorry

example : ThingM 1 2 Nat := do
  IO.println ""
  return 2