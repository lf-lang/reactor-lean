import Runtime.Time
import Runtime.Interface
import Runtime.Utilities

namespace ReactionT

structure Event (σA : Interface.Scheme) where
  action : σA.vars
  value  : σA.type action
  time   : Time

instance : EventType (Event σA) where
  Id := σA.vars
  id := Event.action
  time := Event.time

structure Input (σPS σAS σS σP : Interface.Scheme) where
  ports          : Interface? σPS
  actions        : Interface? σAS
  state          : Interface σS
  params         : Interface σP
  tag            : Tag
  physicalOffset : Duration

abbrev Input.time (input : Input σPS σAS σS σP) := input.tag.time

-- Note: The `writtenPorts` field is used to record when a given port was written to.
--       This information is used for the implementation of connections with delays.
--       If we didn't force reaction bodies to be written in `do` notation,
--       this field could be manipulated to break the semantics of reactor execution,
--       by marking a port as unwritten, even though it was written to. In this case,
--       the port's value would not be propagated along a delayed connection.
-- TODO: If there's an implementation of a dependent hash map available, combine the
--       fields `ports` and `writtenPorts` by using a dependent hash map.
@[ext]
structure Output (σPE σAE σS : Interface.Scheme) (min : Time) where
  ports         : Interface? σPE        := Interface?.empty
  state         : Interface σS
  events        : Queue (Event σAE) min := °[]
  stopRequested : Bool                  := false
  writtenPorts  : Array σPE.vars        := #[]

abbrev _root_.ReactionT (σPS σPE σAS σAE σS σP : Interface.Scheme) (m : Type → Type) (α : Type) :=
  (input : Input σPS σAS σS σP) → m (Output σPE σAE σS input.time × α)

def Output.merge (o₁ o₂ : Output σPE σAE σS time) : Output σPE σAE σS time where
  ports         := o₁.ports.merge o₂.ports
  state         := o₂.state
  events        := o₁.events.merge o₂.events
  stopRequested := o₁.stopRequested ∨ o₂.stopRequested
  writtenPorts  := o₁.writtenPorts ++ o₂.writtenPorts

@[simp]
theorem Output.merge_ports : (Output.merge o₁ o₂).ports = o₁.ports.merge o₂.ports := rfl

@[simp]
theorem Output.merge_state : (Output.merge o₁ o₂).state = o₂.state := rfl

@[simp]
theorem Output.merge_events : (Output.merge o₁ o₂).events = o₁.events.merge o₂.events := rfl

@[simp]
theorem Output.merge_stopRequested :
  (Output.merge o₁ o₂).stopRequested = (o₁.stopRequested ∨ o₂.stopRequested) := by simp [merge]

@[simp]
theorem Output.merge_writtenPorts :
  (Output.merge o₁ o₂).writtenPorts = o₁.writtenPorts ++ o₂.writtenPorts := rfl

def Input.noop (input : Input σPS σAS σS σP) : Output σPE σAE σS input.time where
  state := input.state

@[simp]
theorem Input.noop_ports_isEmpty (input : Input σPS σAS σS σP) {σPE σAE} :
  input.noop (σPE := σPE) (σAE := σAE) |>.ports.isEmpty := rfl

variable [Monad m]

instance : Monad (ReactionT σPS σPE σAS σAE σS σP m) where
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

instance : MonadLift IO (ReactionT σPS σPE σAS σAE σS σP IO) where
  monadLift io input world :=
    match io world with
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'

def getInput (port : σPS.vars) : ReactionT σPS σPE σAS σAE σS σP m (Option $ σPS.type port) :=
  fun input => return (input.noop, input.ports port)

def getState (stv : σS.vars) : ReactionT σPS σPE σAS σAE σS σP m (σS.type stv) :=
  fun input => return (input.noop, input.state stv)

def getAction (action : σAS.vars) : ReactionT σPS σPE σAS σAE σS σP m (Option $ σAS.type action) :=
  fun input => return (input.noop, input.actions action)

def getParam (param : σP.vars) : ReactionT σPS σPE σAS σAE σS σP m (σP.type param) :=
  fun input => return (input.noop, input.params param)

def getTag : ReactionT σPS σPE σAS σAE σS σP m Tag :=
  fun input => return (input.noop, input.tag)

def getLogicalTime : ReactionT σPS σPE σAS σAE σS σP m Time := do
  return (← getTag).time

def getPhysicalTime : ReactionT σPS σPE σAS σAE σS σP IO Time :=
  fun input => return (input.noop, (← Time.now) - input.physicalOffset)

def setOutput (port : σPE.vars) (v : σPE.type port) : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, writtenPorts := #[port], state := input.state }
    return (output, ())

def setState (stv : σS.vars) (v : σS.type stv) : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σAE.vars) (delay : Duration) (v : σAE.type action) : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let time := input.time + delay
    let event : Event σAE := { action, time, value := v }
    let output := {
      state := input.state,
      events := °[event]' (Nat.le_trans (Nat.le_refl _) (Nat.le_add_right ..))
    }
    return (output, ())

def requestStop : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let output := { stopRequested := true, state := input.state }
    return (output, ())

end ReactionT
