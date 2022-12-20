import Runtime.Time
import Runtime.Interface
import Runtime.Utilities

namespace ReactionT

/--
An event `{ action, value, time }` indicates that the action identified by name `action` should be
set to the value `value` at time `time`.
-/
structure Event (σA : Interface.Scheme) where
  action : σA.vars
  value  : σA.type action
  time   : Time

/-- Cf. `EventType` -/
instance : EventType (Event σA) where
  Id := σA.vars
  id := Event.action
  time := Event.time

/--
An `Input` in the context of a `ReactionT`-based monad carries all of the information that should be
readable by a reaction. That is:
* `ports`: source ports of the reaction
* `actions`: source action of the reaction
* `state`: state variables of the parent reactor
* `params`: parameters of the parent reactor
* `tag`: the logical tag at the time of the reaction's execution

The `physicalOffset` is not exposed directly by any monadic operation on `ReactionT` (below), but is
required by `ReactionT.getPhysicalTime`. It is used to normalize physical be 0 at the start of
execution of the program.
-/
structure Input (σPS σAS σS σP : Interface.Scheme) where
  ports          : Interface? σPS
  actions        : Interface? σAS
  state          : Interface σS
  params         : Interface σP
  tag            : Tag
  physicalOffset : Duration

/-- The time of an input is the time component of its `tag`. -/
abbrev Input.time (input : Input σPS σAS σS σP) := input.tag.time

/--
An `Output` in the context of a `ReactionT`-based monad carries all of the information that should
be writable by a reaction. That is:
* `ports`: effect ports of the reaction
* `state`: state variables of the parent reactor
* `events`: a list of `Event`s scheduled for effect actions of the reaction
* `stopRequested`: an indicator for whether the reaction requested execution to stop

The `writtenPorts` field is a (temporary) implementation detail used to record when a given port was
written to. This information is used for the implementation of connections with delays. If we didn't
force reaction bodies to be written in `do` notation, this field could be manipulated to break the
semantics of reactor execution, by marking a port as unwritten, even though it was written to. In
this case, the port's value would not be propagated along a delayed connection.
-/
-- TODO: If there's an implementation of a dependent hash map available, combine the fields `ports`
--       and `writtenPorts` by using a dependent hash map.
@[ext]
structure Output (σPE σAE σS : Interface.Scheme) (min : Time) where
  ports         : Interface? σPE        := Interface?.empty
  state         : Interface σS
  events        : Queue (Event σAE) min := °[]
  stopRequested : Bool                  := false
  writtenPorts  : Array σPE.vars        := #[]

/--
The `ReactionT` monad transformer adds readable `ReactionT.Input` and writable `ReactionT.Output` to
a given monad.
-/
abbrev _root_.ReactionT (σPS σPE σAS σAE σS σP : Interface.Scheme) (m : Type → Type) (α : Type) :=
  (input : Input σPS σAS σS σP) → m (Output σPE σAE σS input.time × α)

/--
Merges outputs `o₁` and `o₂` assuming `o₂` was produced *after* `o₁`. This order is relevant for
`ports`, `state` and `events`:
* Writes to ports of `o₂` override those of `o₁`.
* The state of `o₂` is considered to be the resulting state.
* For a fixed action and time, events of `o₂` are queued *after* those of `o₁`.
-/
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

/--
Produces the `Output` for a given `Input` that should be the result of performing no (monadic)
operation. This amounts to simply propagating the state from input to output.
-/
def Input.noop (input : Input σPS σAS σS σP) : Output σPE σAE σS input.time where
  state := input.state

@[simp]
theorem Input.noop_ports_isEmpty (input : Input σPS σAS σS σP) {σPE σAE} :
  input.noop (σPE := σPE) (σAE := σAE) |>.ports.isEmpty := rfl

variable [Monad m]

instance : Monad (ReactionT σPS σPE σAS σAE σS σP m) where
  -- A pure value results in a noop `Output`.
  pure a input := do
    let output := input.noop
    return (output, a)
  -- Mapping a value retains the `Output`.
  map f ma input := do
    let (output, a) ← ma input
    return (output, f a)
  -- Sequencing requires the `Input` of the second operation to receive the state from the `Output`
  -- of the first operation.
  seq mf ma input₁ := do
    let (output₁, a) ← ma () input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, f) ← mf input₂
    return (output₂, f a)
  -- Binding requires the `Input` of the second operation to receive the state from the `Output` of
  -- the first operation. Additionally the outputs need to be merged at the end.
  bind ma f input₁ := do
    let (output₁, a) ← ma input₁
    let input₂ := { input₁ with state := output₁.state }
    let (output₂, b) ← f a input₂
    let output := output₁.merge output₂
    return (output, b)

/-- Any `IO` operation can be used in an impure (cf. `Reaction.Kind`) reaction. -/
-- TODO: This doesn't work in reaction bodies.
instance : MonadLift IO (ReactionT σPS σPE σAS σAE σS σP IO) where
  monadLift io input world :=
    match io world with
    | .error e world' => .error e world'
    | .ok    a world' => .ok (input.noop, a) world'

/--
Gets the value of a given input port. The return value is optional, as the port may be absent.
-/
def getInput (port : σPS.vars) : ReactionT σPS σPE σAS σAE σS σP m (Option $ σPS.type port) :=
  fun input => return (input.noop, input.ports port)

/-- Gets the value of a given state variable. -/
def getState (stv : σS.vars) : ReactionT σPS σPE σAS σAE σS σP m (σS.type stv) :=
  fun input => return (input.noop, input.state stv)

/--
Gets the value of a given action as scheduled for the current tag (cf. `ReactionT.Input.tag` &
`getTag`). The return value is optional, as there may be no event scheduled for the action at the
current tag.
-/
def getAction (action : σAS.vars) : ReactionT σPS σPE σAS σAE σS σP m (Option $ σAS.type action) :=
  fun input => return (input.noop, input.actions action)

/-- Gets the value of a given parameter as set for the parent reactor (instance) of the reaction. -/
def getParam (param : σP.vars) : ReactionT σPS σPE σAS σAE σS σP m (σP.type param) :=
  fun input => return (input.noop, input.params param)

/-- Gets the current logical tag. -/
def getTag : ReactionT σPS σPE σAS σAE σS σP m Tag :=
  fun input => return (input.noop, input.tag)

/-- Gets the current logical time. -/
def getLogicalTime : ReactionT σPS σPE σAS σAE σS σP m Time := do
  return (← getTag).time

/--
Gets the current physical time, which is monotonically increasing and normalized to be 0 upon the
start of the program's execution.

Note that this operation is only available in the context impure reactions (cf. `Reaction.Kind`).
-/
def getPhysicalTime : ReactionT σPS σPE σAS σAE σS σP IO Time :=
  fun input => return (input.noop, (← Time.now) - input.physicalOffset)

/-- Sets a given output port to a given value. -/
def setOutput (port : σPE.vars) (v : σPE.type port) : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let ports := fun p => if h : p = port then some (h ▸ v) else none
    let output := { ports := ports, writtenPorts := #[port], state := input.state }
    return (output, ())

/-- Sets a given state variable to a given value. -/
def setState (stv : σS.vars) (v : σS.type stv) : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let state := fun s => if h : s = stv then h ▸ v else input.state s
    let output := { state := state }
    return (output, ())

/--
Schedules an event for a given action with a given value to occur after a given logical delay.

If `delay = 0`, the action is scheduled for the current time with a microstep delay of 1.
If `delay > 0`, the action is scheduled for the tag `⟨(← getLogicalTime) + delay, 0⟩`.
-/
def schedule (action : σAE.vars) (delay : Duration) (v : σAE.type action) :
  ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let time := input.time + delay
    let event : Event σAE := { action, time, value := v }
    let output := {
      state := input.state,
      events := °[event]' (Nat.le_trans (Nat.le_refl _) (Nat.le_add_right ..))
    }
    return (output, ())

/--
Causes the program to enter shutdown mode. This results in the following steps: After invoking this
operation, execution for the current logical tag will be completed as usual. Afterwards, execution
continues at the immediate successor of the current tag (if the current tag is `⟨t, m⟩` the
immediate successor is `⟨t, m + 1⟩`). The execution of the immediate successor tag will be
accompanied by the `shutdown` trigger being active. Upon completion of that tag, the program will
terminate.
-/
def requestStop : ReactionT σPS σPE σAS σAE σS σP m Unit :=
  fun input =>
    let output := { stopRequested := true, state := input.state }
    return (output, ())

end ReactionT
