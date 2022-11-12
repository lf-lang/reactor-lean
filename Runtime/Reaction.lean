import Runtime.Time
import Runtime.Interface
import Runtime.Utilities
import Std

namespace ReactionM

structure Event (σAction : Interface.Scheme) (min : Time) where 
  action : σAction.vars
  value  : σAction.type action
  time   : Time.From min

instance : LE (Event σAction time) where
  le e₁ e₂ := e₁.time ≤ e₂.time

instance : Decidable ((e₁ : Event σAction time) ≤ e₂) := by
  simp [LE.le]; infer_instance

structure Input (σPortSource σActionSource σState σParam : Interface.Scheme) where
  ports          : Interface? σPortSource
  actions        : Interface? σActionSource
  state          : Interface σState
  params         : Interface σParam
  tag            : Tag
  physicalOffset : Duration

structure Output (σPortEffect σActionEffect σState : Interface.Scheme) (min : Time) where
  ports  : Interface? σPortEffect := Interface?.empty
  state  : Interface σState
  events : SortedArray (Event σActionEffect min) := #[]#

def _root_.ReactionM (σPortSource σPortEffect σActionSource σActionEffect σState σParam : Interface.Scheme) (α : Type) := 
  (input : Input σPortSource σActionSource σState σParam) → IO (Output σPortEffect σActionEffect σState input.tag.time × α)

def Output.merge (o₁ o₂ : ReactionM.Output σPortEffect σActionEffect σState time) : Output σPortEffect σActionEffect σState time where
  ports  := o₁.ports.merge o₂.ports
  state  := o₂.state
  events := o₁.events.merge o₂.events

@[simp]
theorem Output.merge_ports : (Output.merge o₁ o₂).ports = o₁.ports.merge o₂.ports := rfl

@[simp]
theorem Output.merge_state : (Output.merge o₁ o₂).state = o₂.state := rfl

@[simp]
theorem Output.merge_events : (Output.merge o₁ o₂).events = o₁.events.merge o₂.events := rfl

def Input.noop (input : Input σPortSource σActionSource σState σParam) : Output σPortEffect σActionEffect σState input.tag.time where 
  state := input.state 

@[simp]
theorem Input.noop_ports_isEmpty (input : Input σPortSource σActionSource σState σParam) {σPortEffect σActionEffect} : 
  input.noop (σPortEffect := σPortEffect) (σActionEffect := σActionEffect) |>.ports.isEmpty := rfl

instance : Monad (ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam) where
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

instance : MonadLift IO (ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam) where
  monadLift io input world := 
    match io world with 
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'


def getInput (port : σPortSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σPortSource.type port) :=
  fun input => return (input.noop, input.ports port)

def ReactionSatisfiesM
  (val : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam α) 
  (input : Input σPortSource σActionSource σState σParam)
  (p : (Output σPortEffect σActionEffect σState input.tag.time × α) → Prop) :=
  SatisfiesM (α := (Output σPortEffect σActionEffect σState input.tag.time) × _) p (val input)

set_option hygiene false
local macro val:term " -[" i:term "]→ " p:term : term => `(
  ReactionSatisfiesM 
    (σPortSource := σPortSource) 
    (σPortEffect := σPortEffect)
    (σActionSource := σActionSource)
    (σActionEffect := σActionEffect)
    (σState := σState)
    (σParam := σParam)
    $val $i $p
)

macro "rcn_rfl" : tactic => `(tactic| exists return ⟨(input.noop, _), by first | rfl | simp⟩)

theorem getInput_def : (getInput port) -[input]→ (·.snd = input.ports port) := by rcn_rfl
  
def getState (stv : σState.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σState.type stv) :=
  fun input => return (input.noop, input.state stv)

theorem getState_def : (getState stv) -[input]→ (·.snd = input.state stv) := by rcn_rfl

def getAction (action : σActionSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σActionSource.type action) :=
  fun input => return (input.noop, input.actions action)

theorem getAction_def : (getAction action) -[input]→ (·.snd = input.actions action) := by rcn_rfl

def getParam (param : σParam.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σParam.type param) :=
  fun input => return (input.noop, input.params param)

theorem getParam_def : (getParam param) -[input]→ (·.snd = input.params param) := by rcn_rfl

def getTag : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Tag := 
  fun input => return (input.noop, input.tag)

theorem getTag_def : getTag -[input]→ (·.snd = input.tag) := by rcn_rfl

def getLogicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time := do
  return (← getTag).time

theorem getLogicalTime_def : getLogicalTime -[input]→ (·.snd = input.tag.time) := by rcn_rfl
  
-- TODO: Figure out how composition of `SatisfiesM`s works.
theorem getLogicalTime_def' : 
  (getTag         -[input]→ (·.snd = tag)) → 
  (getLogicalTime -[input]→ (·.snd = tag.time)) := by
  intro h
  exists do
    let t ← getTag (σPortEffect := σPortEffect) (σActionEffect := σActionEffect) input
    return {
      val := (input.noop, t.snd.time)
      property := by
        simp [ReactionSatisfiesM] at h ⊢
        -- PROBLEM: We Lean has no clue of the definition of t.
        sorry
    }

def getPhysicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time :=
  fun input => return (input.noop, (← Time.now) - input.physicalOffset)

def setOutput (port : σPortEffect.vars) (v : σPortEffect.type port) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input => 
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, state := input.state }
    return (output, ())

theorem setOutput_def : (setOutput port v) -[input]→ (·.fst.ports port = some v) := by
  exists do
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    return ⟨({ ports, state := input.state }, ()), by simp⟩

def setState (stv : σState.vars) (v : σState.type stv) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

theorem setState_eq_new_val : (setState stv v) -[input]→ (·.fst.state stv = some v) := by
  exists do
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    return ⟨({ state }, ()), by simp⟩

theorem setState_eq_old_val : (setState stv v) -[input]→ (fun out => ∀ stv', (stv' ≠ stv) → out.fst.state stv' = input.state stv') := by
  exists do
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    return ⟨({ state }, ()), by simp_all⟩

def schedule (action : σActionEffect.vars) (delay : Duration) (v : σActionEffect.type action) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit := 
  fun input => 
    let time := input.tag.time.advance delay
    let event := { action, time, value := v }
    let output := { state := input.state, events := #[event]# }
    return (output, ())

theorem schedule_def : (schedule action delay v) -[input]→ (·.fst.events = #[⟨action, v, input.tag.time.advance delay⟩]#) := by
  exists do
    let time := input.tag.time.advance delay
    return ⟨({ state := input.state, events := #[{ action, time, value := v }]# }, ()), by simp⟩

end ReactionM

inductive Reaction.Trigger (Port Action Timer : Type)
  | startup
  | shutdown
  | port (p : Port)
  | action (a : Action)
  | timer (t : Timer)

structure _root_.Reaction (σInput σOutput σAction σState σParam : Interface.Scheme) (TimerNames : Type) where
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
  body : ReactionM (σInput.restrict portSources) (σOutput.restrict portEffects) (σAction.restrict actionSources) (σAction.restrict actionEffects) σState σParam Unit

namespace Reaction

attribute [instance] portSourcesDecEq portEffectsDecEq actionSourcesDecEq actionEffectsDecEq portSourcesInjCoe portEffectsInjCoe actionSourcesInjCoe actionEffectsInjCoe

def outputType (rcn : Reaction σInput σOutput σAction σState σParam TimerNames) :=
  ReactionM.Output (σOutput.restrict rcn.portEffects) (σAction.restrict rcn.actionEffects) σState 

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