import Runtime.Time
import Runtime.Interface
import Runtime.SortedArray

structure Event (σAction : Scheme) (min : Time) where 
  action : σAction.vars
  time   : Time.After min
  value  : σAction.type action

instance : LE (Event σAction time) where
  le e₁ e₂ := e₁.time ≤ e₂.time

structure ReactionM.Input (σSource σAction σState : Scheme) where
  sources : Interface σSource
  actions : Interface σAction
  state   : Interface σState
  time    : Time

structure ReactionM.Output (σEffect σAction σState : Scheme) (now : Time) where
  effects : Interface σEffect := fun _ => none
  state   : Interface σState
  events  : SortedArray (Event σAction now) := #[]

open ReactionM in
abbrev ReactionT (σSource σEffect σAction σState : Scheme) (m : Type → Type) (α : Type) := 
  (input : Input σSource σAction σState) → m (Output σEffect σAction σState input.time × α)

abbrev ReactionM (σSource σEffect σAction σState : Scheme) := ReactionT σSource σEffect σAction σState IO

variable {σInput σOutput σSource σEffect σAction σState : Scheme} 

namespace ReactionM

def Output.merge (o₁ o₂ : ReactionM.Output σEffect σAction σState time) : Output σEffect σAction σState time := {
  effects := o₁.effects.merge o₂.effects,
  state   := o₁.state.merge   o₂.state,
  events  := o₁.events.merge  o₂.events
}

def Input.noop (input : ReactionM.Input σSource σAction σState) : Output σEffect σAction σState input.time := 
  { state := input.state }

instance : Monad (ReactionM σSource σEffect σAction σState) where
  pure a input := do
    let output := input.noop
    return (output, a)
  map f ma input := do
    let (output, a) ← ma input
    return (output, f a)
  seq mf ma input₁ := do
    let (output₁, a) ← ma () input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, f) ← mf input₂
    return (output₂, f a)
  bind ma f input₁ := do
    let (output₁, a) ← ma input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, b) ← f a input₂
    let output := output₁.merge output₂
    return (output, b)

instance : Coe (IO α) (ReactionM σSource σEffect σAction σState α) where
  coe io input world :=
    match io world with 
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'

def getInput (source : σSource.vars) : ReactionM σSource σEffect σAction σState (Option $ σSource.type source) :=
  fun input => return (input.noop, input.sources source)

def getState (stv : σState.vars) : ReactionM σSource σEffect σAction σState (Option $ σState.type stv) :=
  fun input => return (input.noop, input.state stv)

def getAction (action : σAction.vars) : ReactionM σSource σEffect σAction σState (Option $ σAction.type action) :=
  fun input => return (input.noop, input.actions action)

def logicalTime : ReactionM σSource σEffect σAction σState Time := 
  fun input => return (input.noop, input.time)

def setOutput (effect : σEffect.vars) (v : σEffect.type effect) : ReactionM σSource σEffect σAction σState Unit :=
  fun input => 
    let effects := fun e => if h : e = effect then some (h ▸ v) else none
    let output := { effects := effects, state := input.state }
    return (output, ())

def setState (stv : σState.vars) (v : σState.type var) : ReactionM σSource σEffect σAction σState Unit :=
  fun input =>
    let state := fun s => if h : s = var then some (h ▸ v) else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σAction.vars) (delay : Nat) (h : delay > 0 := by simp_arith) (v : σAction.type action) : ReactionM σSource σEffect σAction σState Unit := 
  fun input => 
    let time := input.time.advance ⟨delay, h⟩
    let event : Event σAction input.time := { action := action, time := time, value := v }
    let output := { state := input.state, events := #[event] }
    return (output, ())

end ReactionM

structure Reaction (σInput σOutput σAction σState : Scheme) where
  sources : Type
  effects : Type
  actions : Type
  triggers : sources → Bool
  [sourcesDecEq : DecidableEq sources]
  [effectsDecEq : DecidableEq effects]
  [actionsDecEq : DecidableEq actions]
  [sourcesInjCoe : InjectiveCoe sources σInput.vars]
  [effectsInjCoe : InjectiveCoe effects σOutput.vars]
  [actionsInjCoe : InjectiveCoe actions σAction.vars]
  body : ReactionM (σInput.restrict sources) (σOutput.restrict effects) (σAction.restrict actions) σState Unit

attribute [instance] Reaction.sourcesDecEq Reaction.effectsDecEq Reaction.actionsDecEq
attribute [instance] Reaction.sourcesInjCoe Reaction.effectsInjCoe Reaction.actionsInjCoe

abbrev Reaction.outputType (rcn : Reaction σInput σOutput σAction σState) :=
  ReactionM.Output (σOutput.restrict rcn.effects) (σAction.restrict rcn.actions) σState 

def ReactionM.run 
  (inputs : Interface σInput) (actions : Interface σAction) (state : Interface σState) 
  (rcn : Reaction σInput σOutput σAction σState) (time : Time) : 
  IO (rcn.outputType time × Unit) := 
  rcn.body {
    sources := fun s => inputs s,
    actions := fun a => actions a,
    state := state,
    time := time
  }
