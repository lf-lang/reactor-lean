import Runtime.Reaction

inductive PortKind
  | input
  | output

def PortKind.opposite : PortKind → PortKind 
  | .input => .output
  | .output => .input

namespace Reactor

structure Scheme where
  inputs    : Interface.Scheme
  outputs   : Interface.Scheme
  actions   : Interface.Scheme
  state     : Interface.Scheme

abbrev Scheme.ports (σ : Reactor.Scheme) : PortKind → Interface.Scheme
  | .input => σ.inputs
  | .output => σ.outputs

structure _root_.Reactor (σ : Reactor.Scheme) where
  inputs  : Interface σ.inputs
  outputs : Interface σ.outputs
  actions : Interface σ.actions
  state   : Interface σ.state

-- TODO: Does this ExecInput/-Output correspond to `Network.Tree.reactionType`?
structure ExecInput {Nested : Type} (nested : Nested → Reactor.Scheme) where
  tag : Tag
  scheme : Reactor.Scheme
  reactor : Reactor σ
  nestedOutputs : (n : Nested) → (Interface $ (nested n).outputs)
  
structure ExecOutput {Nested : Type} (nested : Nested → Reactor.Scheme) (σ : Reactor.Scheme) (time : Time) where
  reactor : Reactor σ
  events : SortedArray (Event σ.actions time)
  nestedInputs : (n : Nested) → (Interface $ (nested n).inputs)

end Reactor