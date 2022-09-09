import Runtime.Time
import Runtime.Interface
import Runtime.SortedArray

structure Event (σAction : Interface.Scheme) (min : Time) where 
  action : σAction.vars
  time   : Time.After min
  value  : σAction.type action

instance : Ord (Event σAction time) where
  compare e₁ e₂ := compare e₁.time e₂.time

namespace ReactionM

structure Input (σSource σAction σState : Interface.Scheme) where
  sources : Interface σSource
  actions : Interface σAction
  state   : Interface σState
  tag     : Tag

structure Output (σEffect σAction σState : Interface.Scheme) (now : Time) where
  effects : Interface σEffect := fun _ => none
  state   : Interface σState
  events  : SortedArray (Event σAction now) := #[]

abbrev _root_.ReactionT (σSource σEffect σAction σState : Interface.Scheme) (m : Type → Type) (α : Type) := 
  (input : Input σSource σAction σState) → m (Output σEffect σAction σState input.tag.time × α)

abbrev _root_.ReactionM (σSource σEffect σAction σState : Interface.Scheme) := ReactionT σSource σEffect σAction σState IO

variable {σInput σOutput σSource σEffect σAction σState : Interface.Scheme} 

def Output.merge (o₁ o₂ : ReactionM.Output σEffect σAction σState time) : Output σEffect σAction σState time := {
  effects := o₁.effects.merge o₂.effects,
  state   := o₁.state.merge   o₂.state,
  events  := o₁.events.merge  o₂.events
}

def Input.noop (input : ReactionM.Input σSource σAction σState) : Output σEffect σAction σState input.tag.time := 
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

instance : MonadLift IO (ReactionM σSource σEffect σAction σState) where
  monadLift io input world := 
    match io world with 
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'

def getInput (source : σSource.vars) : ReactionM σSource σEffect σAction σState (Option $ σSource.type source) :=
  fun input => return (input.noop, input.sources source)

def getState (stv : σState.vars) : ReactionM σSource σEffect σAction σState (Option $ σState.type stv) :=
  fun input => return (input.noop, input.state stv)

def getAction (action : σAction.vars) : ReactionM σSource σEffect σAction σState (Option $ σAction.type action) :=
  fun input => return (input.noop, input.actions action)

def logicalTime : ReactionM σSource σEffect σAction σState Tag := 
  fun input => return (input.noop, input.tag)

def physicalTime : ReactionM σSource σEffect σAction σState Time :=
  fun input => return (input.noop, ← IO.monoNanosNow)

def setOutput (effect : σEffect.vars) (v : σEffect.type effect) : ReactionM σSource σEffect σAction σState Unit :=
  fun input => 
    let effects := fun e => if h : e = effect then some (h ▸ v) else none
    let output := { effects := effects, state := input.state }
    return (output, ())

def setState (stv : σState.vars) (v : σState.type stv) : ReactionM σSource σEffect σAction σState Unit :=
  fun input =>
    let state := fun s => if h : s = stv then some (h ▸ v) else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σAction.vars) (delay : Nat) (h : delay > 0 := by simp_arith) (v : σAction.type action) : ReactionM σSource σEffect σAction σState Unit := 
  fun input => 
    let time := input.tag.time.advance ⟨delay, h⟩
    let event : Event σAction input.tag.time := { action := action, time := time, value := v }
    let output := { state := input.state, events := #[event] }
    return (output, ())

end ReactionM

namespace Reaction

inductive Trigger (Source Action : Type)
  | source (_ : Source)
  | action (_ : Action)

open Reaction in
structure _root_.Reaction (σInput σOutput σAction σState : Interface.Scheme) where
  sources : Type
  effects : Type
  triggers : Array (Trigger sources σAction.vars)
  [sourcesDecEq : DecidableEq sources]
  [effectsDecEq : DecidableEq effects]
  [sourcesInjCoe : InjectiveCoe sources σInput.vars]
  [effectsInjCoe : InjectiveCoe effects σOutput.vars]
  body : ReactionM (σInput.restrict sources) (σOutput.restrict effects) σAction σState Unit

attribute [instance] Reaction.sourcesDecEq Reaction.effectsDecEq
attribute [instance] Reaction.sourcesInjCoe Reaction.effectsInjCoe

abbrev outputType (rcn : Reaction σInput σOutput σAction σState) :=
  ReactionM.Output (σOutput.restrict rcn.effects) σAction σState 

def run 
  (inputs : Interface σInput) (actions : Interface σAction) (state : Interface σState) 
  (rcn : Reaction σInput σOutput σAction σState) (tag : Tag) : 
  IO (rcn.outputType tag.time × Unit) := 
  rcn.body { sources := fun s => inputs s, actions := actions, state := state, tag := tag }

end Reaction