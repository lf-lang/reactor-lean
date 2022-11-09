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

def ReactionSatisfiesM 
  (σPortSource σPortEffect σActionSource σActionEffect σState σParam) 
  (val : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam α) 
  (p : α → (Input σPortSource σActionSource σState σParam) → Prop) :=
  ∀ input, SatisfiesM (p · input) (Prod.snd <$> val input)

-- TODO: Add a delab for this.
set_option hygiene false
macro val:term " ⊢ " p:term : term => `(ReactionSatisfiesM σPortSource σPortEffect σActionSource σActionEffect σState σParam $val $p)

def getInput (port : σPortSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σPortSource.type port) :=
  fun input => return (input.noop, input.ports port)

theorem getInput_def {σPortSource : Interface.Scheme} (port : σPortSource.vars) : (getInput port) ⊢ (· = ·.ports port) := 
  fun input => by exists (return ⟨input.ports port, rfl⟩)

def getState (stv : σState.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σState.type stv) :=
  fun input => return (input.noop, input.state stv)

theorem getState_def {σState : Interface.Scheme} (stv : σState.vars) : (getState stv) ⊢ (· = ·.state stv) := 
  fun input => by exists (return ⟨input.state stv, rfl⟩)

def getAction (action : σActionSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σActionSource.type action) :=
  fun input => return (input.noop, input.actions action)

theorem getAction_def {σActionSource : Interface.Scheme} (action : σActionSource.vars) : (getAction action) ⊢ (· = ·.actions action) := 
  fun input => by exists (return ⟨input.actions action, rfl⟩)

def getParam (param : σParam.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σParam.type param) :=
  fun input => return (input.noop, input.params param)

theorem getParam_def {σParam : Interface.Scheme} (param : σParam.vars) : (getParam param) ⊢ (· = ·.params param) := 
  fun input => by exists (return ⟨input.params param, rfl⟩)

def getTag : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Tag := 
  fun input => return (input.noop, input.tag)

theorem getTag_def : getTag ⊢ (· = ·.tag) := fun input => by exists (return ⟨input.tag, rfl⟩)

def getLogicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time := do
  return (← getTag).time

-- TODO: Is this a problem?
instance : LawfulFunctor IO := sorry

theorem getLogicalTime_def : getLogicalTime ⊢ (· = ·.tag.time) := by
  intro input
  apply SatisfiesM.map_pre
  unfold getLogicalTime
  exists return ⟨⟨input.noop, input.tag.time⟩, rfl⟩
  
notation a " ≐ " b => a ⊢ (fun x _ => x = b)

-- PROBLEM: We're quantifying over different inputs here.
--          Once in `getTag ≐ tag` and once in `getLogicalTime ≐ tag.time`.
theorem getLogicalTime_def' : (getTag ≐ tag) → (getLogicalTime ≐ tag.time) := by
  sorry
  /-intro h input
  apply SatisfiesM.map_pre
  -- let a := @getTag σPortSource σPortEffect σActionSource σActionEffect σState σParam
  let b : ReactionM (α := { y : Time // y = tag.time }) .. := do 
    let x ← @getTag σPortSource σPortEffect σActionSource σActionEffect σState σParam 
    return ⟨
      x.time, -- PROBLEM: Lean doesn't remember how x was defined.
      by
        have ⟨A, B⟩ := h input
        simp at A
        sorry
    ⟩
  exists do let ⟨o, v⟩ ← b input; return ⟨(o, v.val), by simp [v.property]⟩
  -/

def getPhysicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time :=
  fun input => return (input.noop, (← Time.now) - input.physicalOffset)

-- For monad-output related theorems.
def ReactionSatisfiesM' 
  (σPortSource σPortEffect σActionSource σActionEffect σState σParam) 
  (val : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam α) 
  (p : (input : Input σPortSource σActionSource σState σParam) → (Output σPortEffect σActionEffect σState input.tag.time) → Prop) :=
  ∀ input, SatisfiesM (p input ·) (Prod.fst <$> val input)

set_option hygiene false
macro val:term " ⊢' " p:term : term => `(ReactionSatisfiesM' σPortSource σPortEffect σActionSource σActionEffect σState σParam $val $p)

def setOutput (port : σPortEffect.vars) (v : σPortEffect.type port) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input => 
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, state := input.state }
    return (output, ())

theorem setOutput_def : (setOutput port v) ⊢' (fun _ out => out.ports port = some v) := by
  intro input
  apply SatisfiesM.map_pre
  unfold setOutput
  exists do
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    return ⟨({ ports, state := input.state }, ()), by simp⟩

def setState (stv : σState.vars) (v : σState.type stv) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σActionEffect.vars) (delay : Duration) (v : σActionEffect.type action) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit := 
  fun input => 
    let time := input.tag.time.advance delay
    let event : Event σActionEffect input.tag.time := { action := action, time := time, value := v }
    let output := { state := input.state, events := #[event]# }
    return (output, ())

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