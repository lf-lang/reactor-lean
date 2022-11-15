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

def getInput (port : σPortSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σPortSource.type port) :=
  fun input => return (input.noop, input.ports port)
  
def getState (stv : σState.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σState.type stv) :=
  fun input => return (input.noop, input.state stv)

def getAction (action : σActionSource.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (Option $ σActionSource.type action) :=
  fun input => return (input.noop, input.actions action)

def getParam (param : σParam.vars) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam (σParam.type param) :=
  fun input => return (input.noop, input.params param)

def getTag : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Tag := 
  fun input => return (input.noop, input.tag)

def getLogicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time := do
  return (← getTag).time

def getPhysicalTime : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Time :=
  fun input => return (input.noop, (← Time.now) - input.physicalOffset)

def setOutput (port : σPortEffect.vars) (v : σPortEffect.type port) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input => 
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, state := input.state }
    return (output, ())

def setState (stv : σState.vars) (v : σState.type stv) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σActionEffect.vars) (delay : Duration) (v : σActionEffect.type action) : ReactionM σPortSource σPortEffect σActionSource σActionEffect σState σParam Unit := 
  fun input => 
    let time := input.time.advance delay
    let event := { action, time, value := v }
    let output := { state := input.state, events := #[event]# }
    return (output, ())

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