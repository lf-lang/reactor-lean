import Runtime.Time
import Runtime.Interface

structure Event (σAction : Scheme) (min : Time) where 
  action : σAction.vars
  time   : Time.After min
  value  : σAction.type action

structure BodyM.Input (σSource σAction σState : Scheme) where
  sources : Interface σSource
  actions : Interface σAction
  state   : Interface σState
  time    : Time

structure BodyM.Output (σEffect σAction σState : Scheme) (now : Time) where
  effects : Interface σEffect := fun _ => none
  state   : Interface σState
  events  : Array (Event σAction now) := #[]

open BodyM in
def BodyM (σSource σEffect σAction σState : Scheme) (α : Type) := 
  (input : Input σSource σAction σState) → (Output σEffect σAction σState input.time) × α

variable {σInput σOutput σSource σEffect σAction σState : Scheme} 

namespace BodyM

def Output.merge (o₁ o₂ : BodyM.Output σEffect σAction σState time) : Output σEffect σAction σState time := {
  effects := o₁.effects.merge o₂.effects,
  state := o₁.state.merge o₂.state,
  events := o₁.events ++ o₂.events
}

def Input.noop (input : BodyM.Input σSource σAction σState) : Output σEffect σAction σState input.time := 
  { state := input.state }

instance : Monad (BodyM σSource σEffect σAction σState) where
  pure a input := 
    let output := input.noop
    (output, a)
  map f ma input :=
    let (output, a) := ma input
    (output, f a)
  seq mf ma input₁ :=
    let (output₁, a) := ma () input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, f) := mf input₂
    (output₂, f a)
  bind ma f input₁ :=
    let (output₁, a) := ma input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, b) := f a input₂
    let output := output₁.merge output₂
    (output, b)

def getInput (source : σSource.vars) : BodyM σSource σEffect σAction σState (Option $ σSource.type source) :=
  fun input => (input.noop, input.sources source)

def getState (stv : σState.vars) : BodyM σSource σEffect σAction σState (Option $ σState.type stv) :=
  fun input => (input.noop, input.state stv)

def getAction (action : σAction.vars) : BodyM σSource σEffect σAction σState (Option $ σAction.type action) :=
  fun input => (input.noop, input.actions action)

def logicalTime : BodyM σSource σEffect σAction σState Time := 
  fun input => (input.noop, input.time)

def setOutput (effect : σEffect.vars) (v : σEffect.type effect) : BodyM σSource σEffect σAction σState Unit :=
  fun input =>
    let effects := fun e => if h : e = effect then some (h ▸ v) else none
    let output := { effects := effects, state := input.state }
    (output, ())

def setState (stv : σState.vars) (v : σState.type var) : BodyM σSource σEffect σAction σState Unit :=
  fun input =>
    let state := fun s => if h : s = var then some (h ▸ v) else input.state s
    let output := { state := state }
    (output, ())

def schedule (action : σAction.vars) (delay : Nat) (h : delay > 0 := by simp_arith) (v : σAction.type action) : BodyM σSource σEffect σAction σState Unit := 
  fun input => 
    let time := input.time.advance ⟨delay, h⟩
    let event : Event σAction input.time := { action := action, time := time, value := v }
    let output := { state := input.state, events := #[event] }
    (output, ())

end BodyM

def ReactionM (σSource σEffect σAction σState : Scheme) := 
  ExceptT IO.Error $ StateT IO.RealWorld $ BodyM σSource σEffect σAction σState

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
  BodyM.Output (σOutput.restrict rcn.effects) (σAction.restrict rcn.actions) σState 

def Reaction.input (rcn : Reaction σInput σOutput σAction σState) 
  (inputs : Interface σInput) (actions : Interface σAction) (state : Interface σState) (time : Time) :
  BodyM.Input (σInput.restrict rcn.sources) (σAction.restrict rcn.actions) σState := {
  sources := fun s => inputs s,
  actions := fun a => actions a,
  state := state,
  time := time
}

def ReactionM.run 
  (inputs : Interface σInput) (actions : Interface σAction) (state : Interface σState) 
  (rcn : Reaction σInput σOutput σAction σState) (time : Time) : 
  IO (rcn.outputType time × Unit) := fun io =>
  let ⟨output, error, io'⟩ := rcn.body io (rcn.input inputs actions state time)
  match error with
  | .error e => .error e ()
  | .ok _ => .ok (output, ()) io'