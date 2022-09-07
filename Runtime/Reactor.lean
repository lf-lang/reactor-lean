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
  reactions : Array (Reaction inputs outputs actions state)

abbrev Scheme.reactionType (σ : Reactor.Scheme) := Reaction σ.inputs σ.outputs σ.actions σ.state

abbrev Scheme.ports (σ : Reactor.Scheme) : PortKind → Interface.Scheme
  | .input => σ.inputs
  | .output => σ.outputs

structure _root_.Reactor (σ : Reactor.Scheme) where
  inputs  : Interface σ.inputs
  outputs : Interface σ.outputs
  actions : Interface σ.actions
  state   : Interface σ.state

structure ExecOutput (σ : Reactor.Scheme) (time : Time) where
  reactor : Reactor σ
  events : SortedArray (Event σ.actions time)

def triggers (rtr : Reactor σ) (rcn : σ.reactionType) : Bool :=
  rcn.triggers.any fun trigger => 
    match trigger with
    | .source source => rtr.inputs.isPresent source
    | .action action => rtr.actions.isPresent action

-- When this function is called, the reactor should have its actions set to reflect the events
-- of the given tag.
def run {σ : Reactor.Scheme} (rtr : Reactor σ) (tag : Tag) : IO (ExecOutput σ tag.time) := 
  go 0 rtr tag
where 
  go (rcnIdx : Nat) {σ : Reactor.Scheme} (rtr : Reactor σ) (tag : Tag) : IO (ExecOutput σ tag.time) := do
  match h : σ.reactions.get? rcnIdx with
  | none => return { reactor := rtr, events := #[] }
  | some rcn => 
    have : rcnIdx < σ.reactions.size := by unfold Array.get? at h; split at h <;> simp [*]
    if rtr.triggers rcn then
      let ⟨⟨effects, state, events⟩, _⟩ ← rcn.run rtr.inputs rtr.actions rtr.state tag
      let rtr' := { rtr with 
        outputs := rtr.outputs.merge' effects
        state := rtr.state.merge state 
      }
      go (rcnIdx + 1) rtr' tag
    else 
      go (rcnIdx + 1) rtr tag
  termination_by _ => σ.reactions.size - rcnIdx

end Reactor