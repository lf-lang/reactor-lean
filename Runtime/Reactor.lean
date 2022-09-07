import Runtime.Reaction

structure Reactor.Schemes where
  inputs  : Scheme
  outputs : Scheme
  actions : Scheme
  state   : Scheme
  reactions : Array (Reaction inputs outputs actions state)

def Reactor.Schemes.reactionType (σ : Reactor.Schemes) := Reaction σ.inputs σ.outputs σ.actions σ.state

structure Reactor (σ : Reactor.Schemes) where
  inputs  : Interface σ.inputs
  outputs : Interface σ.outputs
  actions : Interface σ.actions
  state   : Interface σ.state

structure Reactor.ExecOutput (σ : Schemes) (time : Time) where
  reactor : Reactor σ
  events : SortedArray (Event σ.actions time)

def Reactor.triggers (rtr : Reactor σ) (rcn : σ.reactionType) : Bool :=
  sorry

-- When this function is called, the reactor should have its actions set to reflect the events
-- of the given tag.
def Reactor.run {σ : Schemes} (rtr : Reactor σ) (tag : Tag) : IO (ExecOutput σ tag.time) := 
  go 0 rtr tag
where 
  go (rcnIdx : Nat) {σ : Schemes} (rtr : Reactor σ) (tag : Tag) : IO (ExecOutput σ tag.time) := do
  match h : σ.reactions.get? rcnIdx with
  | none => return { reactor := rtr, events := #[] }
  | some rcn => 
    have : rcnIdx < σ.reactions.size := by unfold Array.get? at h; split at h <;> simp [*]
    if rtr.triggers rcn then
      let ⟨⟨effects, state, events⟩, _⟩ ← rcn.run rtr.inputs rtr.actions rtr.state tag
      let rtr' := { rtr with 
        outputs := rtr.outputs.merge' effects, 
        state := rtr.state.merge state 
      }
      go (rcnIdx + 1) rtr' tag
    else 
      go (rcnIdx + 1) rtr tag
  termination_by _ => σ.reactions.size - rcnIdx
