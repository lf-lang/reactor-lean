import Runtime.Execution.Event

open Network

open Graph in
structure Reactor {net : Network} (cls : Class net) where
  interface : (kind : Reactor.InterfaceKind) → kind.interfaceType (cls.interface kind)
  timer : cls.timers → Timer

namespace Execution.Executable

def LawfulQueue (queue : Array (Event net)) (time : Time) := 
  ∀ {event}, (queue[0]? = some event) → event.time ≥ time

theorem LawfulQueue.empty : LawfulQueue (#[] : Array (Event net)) time := by
  simp [LawfulQueue]; intros; contradiction

theorem LawfulQueue.merge :
  (LawfulQueue queue₁ time) → (LawfulQueue queue₂ time) → (LawfulQueue (queue₁.merge queue₂) time) :=
  sorry

inductive State
  | executing
  | stopRequested
  | shuttingDown 
  deriving DecidableEq

structure _root_.Execution.Executable (net : Network) where
  tag : Tag := ⟨0, 0⟩
  physicalOffset : Duration
  queue : Array (Event net)
  reactors : (id : ReactorId net) → Reactor id.class
  state : State := .executing
  lawfulQueue : LawfulQueue queue tag.time

def isStartingUp (exec : Executable net) : Bool := 
  exec.tag = ⟨0, 0⟩

abbrev time (exec : Executable net) : Time := exec.tag.time

def absoluteTime (exec : Executable net) : Time :=
  exec.time + exec.physicalOffset

def interface (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).interface

def timer (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).timer

end Execution.Executable
