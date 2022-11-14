import Runtime.Time
import Runtime.Interface
import Runtime.Utilities

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

abbrev Input.time (input : Input σPortSource σActionSource σState σParam) := input.tag.time

@[ext]
structure Output (σPortEffect σActionEffect σState : Interface.Scheme) (min : Time) where
  ports  : Interface? σPortEffect := Interface?.empty
  state  : Interface σState
  events : SortedArray (Event σActionEffect min) := #[]#

def _root_.ReactionM (σPortSource σPortEffect σActionSource σActionEffect σState σParam : Interface.Scheme) (α : Type) := 
  (input : Input σPortSource σActionSource σState σParam) → IO (Output σPortEffect σActionEffect σState input.time × α)

def Output.merge (o₁ o₂ : ReactionM.Output σPortEffect σActionEffect σState time) : Output σPortEffect σActionEffect σState time where
  ports  := o₁.ports.merge o₂.ports
  state  := o₂.state
  events := o₁.events.merge o₂.events

@[simp]
theorem Output.merge_idem {o : Output σPortEffect σActionEffect σState time} : (o.events = #[]#) → o.merge o = o := by
  intro h
  simp [Output.merge, Interface?.merge_idem, h, SortedArray.merge_empty]
  ext <;> simp [*]

@[simp]
theorem Output.merge_ports : (Output.merge o₁ o₂).ports = o₁.ports.merge o₂.ports := rfl

@[simp]
theorem Output.merge_state : (Output.merge o₁ o₂).state = o₂.state := rfl

@[simp]
theorem Output.merge_events : (Output.merge o₁ o₂).events = o₁.events.merge o₂.events := rfl

def Input.noop (input : Input σPortSource σActionSource σState σParam) : Output σPortEffect σActionEffect σState input.time where 
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

instance : LawfulMonad IO := sorry

def getInput (port : σPortSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σPortSource.type port) :=
  fun input => return (input.noop, input.ports port)

def ReactionSatisfiesM
  (input : Input σPortSource σActionSource σState σParam)
  (comp : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam α) 
  (p : (Output σPortEffect σActionEffect σState input.time × α) → Prop) :=
  SatisfiesM (α := (Output σPortEffect σActionEffect σState input.time) × _) p (comp input)

set_option hygiene false
local macro input:term " -[" comp:term "]→ " prop:term : term => `(
  ReactionSatisfiesM  
    (σPortSource := σPortSource) 
    (σPortEffect := σPortEffect) 
    (σActionSource := σActionSource) 
    (σActionEffect := σActionEffect) 
    (σState := σState) 
    (σParam := σParam)
    $input $comp $prop
)

local macro "rcn_rfl" : tactic => `(tactic| exists return ⟨(input.noop, _), by first | rfl | simp⟩)

theorem getInput_def : input -[getInput port]→ (·.snd = input.ports port) := by rcn_rfl
  
def getState (stv : σState.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σState.type stv) :=
  fun input => return (input.noop, input.state stv)

theorem getState_def : input -[getState stv]→ (·.snd = input.state stv) := by rcn_rfl

def getAction (action : σActionSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σActionSource.type action) :=
  fun input => return (input.noop, input.actions action)

theorem getAction_def : input -[getAction action]→ (·.snd = input.actions action) := by rcn_rfl

def getParam (param : σParam.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σParam.type param) :=
  fun input => return (input.noop, input.params param)

theorem getParam_def : input -[getParam param]→ (·.snd = input.params param) := by rcn_rfl

def getTag : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Tag := 
  fun input => return (input.noop, input.tag)

theorem getTag_def : input -[getTag]→ (·.snd = input.tag) := by rcn_rfl

def getLogicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time := do
  return (← getTag).time

theorem getLogicalTime_def : input -[getLogicalTime]→ (·.snd = input.time) := by rcn_rfl

-- TODO:
theorem getLogicalTime_def' : 
  (input -[getTag]→         (·.snd = tag)) → 
  (input -[getLogicalTime]→ (·.snd = tag.time)) := by
  intro h
  simp [ReactionSatisfiesM, getLogicalTime]
  apply SatisfiesM.bind_pre
  simp
  refine SatisfiesM.imp ?_ (p := fun out => input.tag = tag) (by
    intro a h
    simp [h]
    sorry
  )
  sorry  

def getPhysicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time :=
  fun input => return (input.noop, (← Time.now) - input.physicalOffset)

def setOutput (port : σPortEffect.vars) (v : σPortEffect.type port) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input => 
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, state := input.state }
    return (output, ())

theorem setOutput_def : input -[setOutput port v]→ (·.fst.ports port = some v) := by
  exists do
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    return ⟨({ ports, state := input.state }, ()), by simp⟩

def setState (stv : σState.vars) (v : σState.type stv) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

theorem setState_eq_new_val : input -[setState stv v]→ (·.fst.state stv = some v) := by
  exists do
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    return ⟨({ state }, ()), by simp⟩

theorem setState_eq_old_val : input -[setState stv v]→ (fun out => ∀ stv', (stv' ≠ stv) → out.fst.state stv' = input.state stv') := by
  exists do
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    return ⟨({ state }, ()), by simp_all⟩

def schedule (action : σActionEffect.vars) (delay : Duration) (v : σActionEffect.type action) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit := 
  fun input => 
    let time := input.time.advance delay
    let event := { action, time, value := v }
    let output := { state := input.state, events := #[event]# }
    return (output, ())

theorem schedule_def : input -[schedule action delay v]→ (·.fst.events = #[⟨action, v, input.time.advance delay⟩]#) := by
  exists do
    let time := input.time.advance delay
    return ⟨({ state := input.state, events := #[{ action, time, value := v }]# }, ()), by simp⟩

end ReactionM

inductive Reaction.Trigger (Port Action Timer : Type)
  | startup
  | shutdown
  | port (p : Port)
  | action (a : Action)
  | timer (t : Timer)

structure _root_.Reaction where
  portSources   : Interface.Scheme
  portEffects   : Interface.Scheme
  actionSources : Interface.Scheme
  actionEffects : Interface.Scheme
  state         : Interface.Scheme
  params        : Interface.Scheme
  timers        : Type
  triggers      : Array (Reaction.Trigger portSources.vars actionSources.vars timers)
  body          : ReactionM portSources portEffects actionSources actionEffects state params Unit

namespace Reaction

abbrev inputType (rcn : Reaction) :=
  ReactionM.Input rcn.portSources rcn.actionSources rcn.state rcn.params

abbrev outputType (rcn : Reaction) :=
  ReactionM.Output rcn.portEffects rcn.actionEffects rcn.state 

abbrev bodyType (rcn : Reaction) :=
  ReactionM rcn.portSources rcn.portEffects rcn.actionSources rcn.actionEffects rcn.state rcn.params Unit

def run (rcn : Reaction) (input : rcn.inputType) : IO (rcn.outputType input.time) := 
  Prod.fst <$> rcn.body input

end Reaction