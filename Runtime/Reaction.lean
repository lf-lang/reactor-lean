import Runtime.Time
import Runtime.Interface
import Runtime.SortedArray

structure Event (σAction : Interface.Scheme) (min : Time) where 
  action : σAction.vars
  time   : Time.From min
  value  : σAction.type action

instance {later : Time.From earlier} : Coe (Event σAction later) (Event σAction earlier) where
  coe event := { event with time := event.time }

instance : Ord (Event σAction time) where
  compare e₁ e₂ := compare e₁.time e₂.time

namespace ReactionM

structure Input (σPortSource σActionSource σState : Interface.Scheme) where
  ports   : Interface σPortSource
  actions : Interface σActionSource
  state   : Interface σState
  tag     : Tag

structure Output (σPortEffect σActionEffect σState : Interface.Scheme) (now : Time) where
  ports : Interface σPortEffect := fun _ => none
  state   : Interface σState
  events  : SortedArray (Event σActionEffect now) := #[]#

abbrev _root_.ReactionT (σPortSource σPortEffect σActionSource σActionEffect σState : Interface.Scheme) (m : Type → Type) (α : Type) := 
  (input : Input σPortSource σActionSource σState) → m (Output σPortEffect σActionEffect σState input.tag.time × α)

abbrev _root_.ReactionM (σPortSource σPortEffect σActionSource σActionEffect σState : Interface.Scheme) := ReactionT σPortSource σPortEffect σActionSource σActionEffect σState IO

variable {σInput σOutput σAction σPortSource σPortEffect σActionSource σActionEffect σState : Interface.Scheme} 

def Output.merge (o₁ o₂ : ReactionM.Output σPortEffect σActionEffect σState time) : Output σPortEffect σActionEffect σState time := {
  ports  := o₁.ports.merge o₂.ports,
  state  := o₁.state.merge  o₂.state,
  events := o₁.events.merge o₂.events
}

def Input.noop (input : ReactionM.Input σPortSource σActionSource σState) : Output σPortEffect σActionEffect σState input.tag.time := 
  { state := input.state }

instance : Monad (ReactionM σPortSource σPortEffect σActionSource σActionEffect σState) where
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

instance : MonadLift IO (ReactionM σPortSource σPortEffect σActionSource σActionEffect σState) where
  monadLift io input world := 
    match io world with 
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'

def getInput (port : σPortSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState (Option $ σPortSource.type port) :=
  fun input => return (input.noop, input.ports port)

def getState (stv : σState.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState (Option $ σState.type stv) :=
  fun input => return (input.noop, input.state stv)

def getAction (action : σActionSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState (Option $ σActionSource.type action) :=
  fun input => return (input.noop, input.actions action)

-- TODO: Should this return the tag or just a time?
def logicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState Tag := 
  fun input => return (input.noop, input.tag)

def physicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState Time :=
  fun input => return (input.noop, ← IO.monoNanosNow)

def setOutput (port : σPortEffect.vars) (v : σPortEffect.type port) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState Unit :=
  fun input => 
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, state := input.state }
    return (output, ())

def setState (stv : σState.vars) (v : σState.type stv) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState Unit :=
  fun input =>
    let state := fun s => if h : s = stv then some (h ▸ v) else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σActionEffect.vars) (delay : Duration) (v : σActionEffect.type action) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState Unit := 
  fun input => 
    let time := input.tag.time.advance delay
    let event : Event σActionEffect input.tag.time := { action := action, time := time, value := v }
    let output := { state := input.state, events := #[event]# }
    return (output, ())

end ReactionM

namespace Reaction

inductive Trigger (Port Action : Type)
  | port (_ : Port)
  | action (_ : Action)

open Reaction in
structure _root_.Reaction (σInput σOutput σAction σState : Interface.Scheme) where
  portSources : Type
  portEffects : Type 
  actionSources : Type
  actionEffects : Type
  triggers : Array (Trigger portSources actionSources)
  [portSourcesDecEq : DecidableEq portSources]
  [portEffectsDecEq : DecidableEq portEffects]
  [actionSourcesDecEq : DecidableEq actionSources]
  [actionEffectsDecEq : DecidableEq actionEffects]
  [portSourcesInjCoe : InjectiveCoe portSources σInput.vars]
  [portEffectsInjCoe : InjectiveCoe portEffects σOutput.vars]
  [actionSourcesInjCoe : InjectiveCoe actionSources σAction.vars]
  [actionEffectsInjCoe : InjectiveCoe actionEffects σAction.vars]
  body : ReactionM (σInput.restrict portSources) (σOutput.restrict portEffects) (σAction.restrict actionSources) (σAction.restrict actionEffects) σState Unit

attribute [instance] Reaction.portSourcesDecEq Reaction.portEffectsDecEq Reaction.actionSourcesDecEq Reaction.actionEffectsDecEq
attribute [instance] Reaction.portSourcesInjCoe Reaction.portEffectsInjCoe Reaction.actionSourcesInjCoe Reaction.actionEffectsInjCoe

abbrev outputType (rcn : Reaction σInput σOutput σAction σState) :=
  ReactionM.Output (σOutput.restrict rcn.portEffects) (σAction.restrict rcn.actionEffects) σState 

def run 
  (inputs : Interface σInput) (actions : Interface σAction) (state : Interface σState) 
  (rcn : Reaction σInput σOutput σAction σState) (tag : Tag) : 
  IO (rcn.outputType tag.time × Unit) := 
  rcn.body { 
    ports   := fun s => inputs s
    actions := fun a => actions a
    state   := state
    tag     := tag 
  }

end Reaction