import Runtime.Network.Execution.Event

open Network.Graph in
structure Reactor {net : Network} (cls : Class net) where
  interface : (kind : Reactor.InterfaceKind) → kind.interfaceType (cls.interface kind)
  timer : cls.timers → Timer

open Network in
structure Reaction.Output (net : Network) (time : Time) where
  reactor : ReactorId net
  reaction : reactor.class.reactionType
  raw : reaction.outputType time

open Network in
def Reaction.Output.fromRaw {reactor : ReactorId net} {reaction : reactor.class.reactionType} (raw : reaction.outputType time) : Reaction.Output net time where
  reactor := reactor
  reaction := reaction
  raw := raw

def Reaction.Output.events (output : Reaction.Output net time) :=
  output.raw.events.map fun event => 
    Network.Event.action event.time ⟨output.reactor, event.action⟩ event.value

namespace Network

def Executable.LawfulQueue (queue : Array (Event net)) (time : Time) := 
  ∀ {event}, (queue[0]? = some event) → event.time ≥ time

theorem Executable.LawfulQueue.merge :
  (LawfulQueue queue₁ time) → (LawfulQueue queue₂ time) → (LawfulQueue (queue₁.merge queue₂) time) :=
  sorry

structure Executable (net : Network) where
  tag : Tag := ⟨0, 0⟩
  physicalOffset : Duration
  queue : Array (Event net)
  reactors : (id : ReactorId net) → Reactor id.class
  isShuttingDown : Bool := false
  lawfulQueue : Executable.LawfulQueue queue tag.time

namespace Executable

def isStartingUp (exec : Executable net) : Bool := 
  exec.tag = ⟨0, 0⟩

def absoluteTime (exec : Executable net) : Time :=
  exec.tag.time + exec.physicalOffset

def interface (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).interface

def timer (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).timer

-- def timer (exec : Executable net) (id : TimerId net) : Timer :=
--   exec.reactors id.reactor |>.timer id.timer

end Executable

end Network
