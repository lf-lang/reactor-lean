import Runtime.Reaction

structure Reactor.Schemes where
  inputs  : Scheme
  outputs : Scheme
  actions : Scheme
  state   : Scheme
  reactions : Array (Reaction inputs outputs actions state)

structure Reactor (σ : Reactor.Schemes) where
  inputs  : Interface σ.inputs
  outputs : Interface σ.outputs
  actions : Interface σ.actions
  state   : Interface σ.state

structure Reactor.ExecInput (σAction : Scheme) where
  time : Time
  events : SortedArray (Event σAction time)

structure Reactor.ExecOutput (σ : Schemes) (time : Time) where
  reactor : Reactor σ
  events : SortedArray (Event σ.actions time)

-- TODO: Figure out the coercion of an array of events of reaction-actions to an array of events of reactor-actions.
instance {Sub : Type} [DecidableEq Sub] [InjectiveCoe Sub σAction.vars] : Coe (Event σAction time) (Event (σAction.restrict Sub) time) where
  coe e := sorry

instance [Coe α β] : Coe (Array α) (Array β) where
  coe as := as.map fun a => Coe.coe a

def Reactor.run {σ : Schemes} (rtr : Reactor σ) (input : ExecInput σ.actions) : IO (ExecOutput σ input.time) := 
  go 0 rtr input
where 
  go (rcnIdx : Nat) {σ : Schemes} (rtr : Reactor σ) (input : ExecInput σ.actions) : IO (ExecOutput σ input.time) := do
  match h : σ.reactions.get? rcnIdx with
  | none => return { reactor := rtr, events := input.events }
  | some rcn => 

    let ⟨⟨effects, state, events⟩, _⟩ ← ReactionM.run rtr.inputs rtr.actions rtr.state rcn input.time
    let outputs' := rtr.outputs.merge' effects
    let state' := rtr.state.merge state
    let events' := input.events -- ++ (events : Array $ Event σ.actions ctx.time)
    let rtr' := { rtr with outputs := outputs', state := state' }
    let input' := { input with events := events' }
    have : rcnIdx < σ.reactions.size := by unfold Array.get? at h; split at h <;> simp [*]
    let result ← go (rcnIdx + 1) rtr' input'
    have hi : input'.time = input.time := rfl
    return hi ▸ result
  termination_by _ => σ.reactions.size - rcnIdx
