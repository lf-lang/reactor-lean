import Runtime.Time
import Runtime.Interface
import Runtime.Utilities

-- NOTE: This approach doesn't work unfortunately: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Type.20Inference.20Problem

namespace ReactionM

structure Event (σAction : Interface.Scheme) (min : Time) where 
  action : σAction.vars
  value  : σAction.type action
  time   : Time.From min

instance : LE (Event σAction time) where
  le e₁ e₂ := e₁.time ≤ e₂.time

instance : Decidable ((e₁ : Event σAction time) ≤ e₂) := by
  simp [LE.le]; infer_instance

structure Input.Schemes where
  portSource   : Interface.Scheme
  actionSource : Interface.Scheme
  state        : Interface.Scheme
  param        : Interface.Scheme

open Input.Schemes in attribute [reducible] portSource actionSource state param

structure Input (σs : Input.Schemes) where
  ports          : Interface? σs.portSource
  actions        : Interface? σs.actionSource
  state          : Interface σs.state
  params         : Interface σs.param
  tag            : Tag
  physicalOffset : Duration

structure Output.Schemes where
  portEffect   : Interface.Scheme
  actionEffect : Interface.Scheme
  state        : Interface.Scheme

open Output.Schemes in attribute [reducible] portEffect actionEffect state

structure Output (σs : Output.Schemes) (min : Time) where
  ports  : Interface? σs.portEffect := Interface?.empty
  state  : Interface σs.state
  events : SortedArray (Event σs.actionEffect min) := #[]#

structure Schemes where
  portSource   : Interface.Scheme
  portEffect   : Interface.Scheme
  actionSource : Interface.Scheme
  actionEffect : Interface.Scheme
  state        : Interface.Scheme
  param        : Interface.Scheme

open Schemes in attribute [reducible] portSource portEffect actionSource actionEffect state param

abbrev Schemes.inputSchemes (σs : Schemes) : Input.Schemes where
  portSource   := σs.portSource
  actionSource := σs.actionSource
  state        := σs.state
  param        := σs.param

abbrev Schemes.outputSchemes (σs : Schemes) : Output.Schemes where
  portEffect   := σs.portEffect
  actionEffect := σs.actionEffect
  state        := σs.state

abbrev _root_.ReactionM (σs : Schemes) (α : Type) := 
  (input : Input σs.inputSchemes) → IO (Output σs.outputSchemes input.tag.time × α)

def Output.merge (o₁ o₂ : ReactionM.Output σs time) : Output σs time where
  ports  := o₁.ports.merge o₂.ports
  state  := o₂.state
  events := o₁.events.merge o₂.events

@[simp]
theorem Output.merge_ports : (Output.merge o₁ o₂).ports = o₁.ports.merge o₂.ports := rfl

@[simp]
theorem Output.merge_state : (Output.merge o₁ o₂).state = o₂.state := rfl

@[simp]
theorem Output.merge_events : (Output.merge o₁ o₂).events = o₁.events.merge o₂.events := rfl

def Input.noop (input : Input σsᵢ) : Output ⟨σPortEffect, σActionEffect, σsᵢ.state⟩ input.tag.time where 
  state := input.state 

@[simp]
theorem Input.noop_ports_isEmpty (input : Input σs) : 
  input.noop (σPortEffect := σPortEffect) (σActionEffect := σActionEffect) |>.ports.isEmpty := 
  rfl

instance : Monad (ReactionM σs) where
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

instance : LawfulMonad (ReactionM σs) :=
  sorry -- https://github.com/leanprover/std4/blob/23f8577169c049e6eb472a0354c11b9b934b4282/Std/Classes/LawfulMonad.lean#L12

instance : MonadLift IO (ReactionM σs) where
  monadLift io input world := 
    match io world with 
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'

variable {σs : Schemes} 

def getInput (port : σs.portSource.vars) : ReactionM σs (Option <| σs.portSource.type port) := fun input => 
  return (input.noop, input.ports port)

/-
-- https://github.com/leanprover/std4/blob/23f8577169c049e6eb472a0354c11b9b934b4282/Std/Classes/LawfulMonad.lean#L69
theorem getInput_def (input : Input σPortSource σActionSource σState σParam) (port) : 
  SatisfiesM (· = input.ports port) 
  (getInput port (σPortEffect := σPortEffect) (σActionSource := σActionSource) (σActionEffect := σActionEffect) (σState := σState) (σParam := σParam)) 
  := sorry
-/

def getState (stv : σs.state.vars) : ReactionM σs (σs.state.type stv) := fun input => 
  return (input.noop, input.state stv)

def getAction (action : σs.actionSource.vars) : ReactionM σs (Option <| σs.actionSource.type action) := fun input => 
  return (input.noop, input.actions action)

def getParam (param : σs.param.vars) : ReactionM σs (σs.param.type param) := fun input => 
  return (input.noop, input.params param)

def getTag : ReactionM σs Tag := fun input => 
  return (input.noop, input.tag)

def getLogicalTime : ReactionM σs Time := fun input => 
  return (input.noop, input.tag.time)

def getPhysicalTime : ReactionM σs Time := fun input => 
  return (input.noop, (← Time.now) - input.physicalOffset)

def setOutput (port : σs.portEffect.vars) (v : σs.portEffect.type port) : ReactionM σs Unit :=
  fun input => 
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, state := input.state }
    return (output, ())

def setState (stv : σs.state.vars) (v : σs.state.type stv) : ReactionM σs Unit := fun input =>
  let state := fun s => if h : s = stv then h ▸ v else input.state s
  let output := { state := state }
  return (output, ())

def schedule (action : σs.actionEffect.vars) (delay : Duration) (v : σs.actionEffect.type action) : ReactionM σs Unit := fun input => 
  let time := input.tag.time.advance delay
  let event := { action := action, time := time, value := v }
  let output := { state := input.state, events := #[event]# }
  return (output, ())

end ReactionM

inductive Reaction.Trigger (Port Action Timer : Type)
  | startup
  | shutdown
  | port (p : Port)
  | action (a : Action)
  | timer (t : Timer)

structure Reaction (σInput σOutput σAction σState σParam : Interface.Scheme) (TimerNames : Type) where
  portSources : Type
  portEffects : Type 
  actionSources : Type
  actionEffects : Type
  triggers : Array (Reaction.Trigger portSources actionSources TimerNames)
  [portSourcesDecEq : DecidableEq portSources]
  [portEffectsDecEq : DecidableEq portEffects]
  [actionSourcesDecEq : DecidableEq actionSources]
  [actionEffectsDecEq : DecidableEq actionEffects]
  [portSourcesInjCoe : InjectiveCoe portSources σInput.vars]
  [portEffectsInjCoe : InjectiveCoe portEffects σOutput.vars]
  [actionSourcesInjCoe : InjectiveCoe actionSources σAction.vars]
  [actionEffectsInjCoe : InjectiveCoe actionEffects σAction.vars]
  body : ReactionM ⟨σInput.restrict portSources, σOutput.restrict portEffects, σAction.restrict actionSources, σAction.restrict actionEffects, σState, σParam⟩ Unit

namespace Reaction

attribute [instance] portSourcesDecEq portEffectsDecEq actionSourcesDecEq actionEffectsDecEq portSourcesInjCoe portEffectsInjCoe actionSourcesInjCoe actionEffectsInjCoe

abbrev outputType (rcn : Reaction σInput σOutput σAction σState σParam TimerNames) :=
  ReactionM.Output ⟨σOutput.restrict rcn.portEffects, σAction.restrict rcn.actionEffects, σState⟩

def run 
  (rcn : Reaction σInput σOutput σAction σState σParam TimerNames) 
  (inputs : Interface? σInput) (actions : Interface? σAction) 
  (state : Interface σState) (params : Interface σParam) 
  (tag : Tag) (physicalOffset : Duration) : 
  IO (rcn.outputType tag.time) := do
  let ⟨output, _⟩ ← rcn.body { 
    ports := (inputs ·), actions := (actions ·), 
    state := state, params := params, 
    tag := tag, physicalOffset := physicalOffset 
  }
  return output

end Reaction