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

abbrev Scheme.reactionType (σ : Reactor.Scheme) := Reaction σ.inputs σ.outputs σ.actions σ.state

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

def triggers (rtr : Reactor σ) (rcn : σ.reactionType) : Bool :=
  rcn.triggers.any fun trigger => 
    match trigger with
    | .source source => rtr.inputs.isPresent source
    | .action action => rtr.actions.isPresent action

-- When this function is called, the reactor should have its actions set to reflect the events
-- of the given tag.
/-def run {Nested : Type} (nested : Nested → Reactor.Scheme) (input : ExecInput nested) : IO (ExecOutput nested input.scheme input.tag.time) := do
  let mut rtr := input.reactor
  let mut events := #[]#
  for rcn in input.scheme.reactions do
    unless rtr.triggers rcn do continue
    let ⟨⟨effects, state, newEvents⟩, _⟩ ← rcn.run rtr.inputs rtr.actions rtr.state input.tag
    rtr := { rtr with 
      outputs := rtr.outputs.merge' effects
      state := rtr.state.merge state 
    }
    events := events.merge newEvents
  return { reactor := rtr, events := events }
-/
-- TODO: Given a reactor R with nested reactors R.Nested identifying the nested reactors,
--       for each reaction C in R we need injective coercions :
--       * C.Source to (Sum (R.inputs.vars) (Σ n : R.Nested, (R.Nested.schemes n).outputs)) 
--       * C.Effect to (Sum (R.outputs.vars) (Σ n : R.Nested, (R.Nested.schemes n).inputs)) 

end Reactor