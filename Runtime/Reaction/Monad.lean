import Runtime.Time
import Runtime.Interface
import Runtime.Utilities

namespace ReactionT

structure Event (σA : Interface.Scheme) (min : Time) where 
  action : σA.vars
  value  : σA.type action
  time   : Time.From min

instance : LE (Event σA time) where
  le e₁ e₂ := e₁.time ≤ e₂.time

instance : Decidable ((e₁ : Event σA time) ≤ e₂) := by
  simp [LE.le]; infer_instance

structure Input (σPS σAS σS σP : Interface.Scheme) where
  ports          : Interface? σPS
  actions        : Interface? σAS
  state          : Interface σS
  params         : Interface σP
  tag            : Tag
  physicalOffset : Duration

abbrev Input.time (input : Input σPS σAS σS σP) := input.tag.time

@[ext]
structure Output (σPE σAE σS : Interface.Scheme) (min : Time) where
  ports  : Interface? σPE := Interface?.empty
  state  : Interface σS
  events : SortedArray (Event σAE min) := #[]#

abbrev _root_.ReactionT (σPS σPE σAS σAE σS σP : Interface.Scheme) (m : Type → Type) (α : Type) := 
  (input : Input σPS σAS σS σP) → m (Output σPE σAE σS input.time × α)

def Output.merge (o₁ o₂ : Output σPE σAE σS time) : Output σPE σAE σS time where
  ports  := o₁.ports.merge o₂.ports
  state  := o₂.state
  events := o₁.events.merge o₂.events

theorem Output.merge_idem {o : Output σPE σAE σS time} : (o.events = #[]#) → o.merge o = o := by
  intro h
  simp [Output.merge, Interface?.merge_idem, h, SortedArray.merge_empty]
  ext <;> simp [*]

@[simp]
theorem Output.merge_ports : (Output.merge o₁ o₂).ports = o₁.ports.merge o₂.ports := rfl

@[simp]
theorem Output.merge_state : (Output.merge o₁ o₂).state = o₂.state := rfl

@[simp]
theorem Output.merge_events : (Output.merge o₁ o₂).events = o₁.events.merge o₂.events := rfl

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
    let output := { ports := ports, state := input.state }
    return (output, ())

def setState (stv : σS.vars) (v : σS.type stv) : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

def schedule (action : σAE.vars) (delay : Duration) (v : σAE.type action) : ReactionT σPS σPE σAS σAE σS σP m Unit := 
  fun input => 
    let time := input.time.advance delay
    let event := { action, time, value := v }
    let output := { state := input.state, events := #[event]# }
    return (output, ())

end ReactionT