import Runtime.Execution.Event

open Network Graph Class

structure Reactor.Timer where
  val : Timer
  isFiring : Bool

structure Reactor {net : Network} (cls : Class net) where
  interface : (kind : Reactor.InterfaceKind) → kind.interfaceType (cls.interface kind)
  timer : cls.timers → Reactor.Timer

namespace Execution.Executable

inductive State
  | executing
  | stopRequested
  | shuttingDown
  deriving DecidableEq

-- During an instantaneous execution, the `toPropagate` field is used to collect the output ports
-- which have been written to. When advancing from to the next tag, this field is processed by
-- generating `.propagation` events for those ports which have delayed connections.
structure _root_.Execution.Executable (net : Network) where
  state          : State := .executing
  tag            : Tag := ⟨0, 0⟩
  queue          : Queue (Event net) tag.time
  reactors       : (id : ReactorId net) → Reactor id.class
  physicalOffset : Duration
  toPropagate    : Array (PortId net .output) := #[]

def isStartingUp (exec : Executable net) : Bool :=
  exec.tag = ⟨0, 0⟩

abbrev time (exec : Executable net) : Time := exec.tag.time

def absoluteTime (exec : Executable net) : Time :=
  exec.time + exec.physicalOffset

def interface (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).interface

end Execution.Executable
