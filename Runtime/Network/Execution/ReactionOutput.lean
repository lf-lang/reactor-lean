import Runtime.Network.Execution.Basic

namespace Network.Executable

open Graph.Class (Reaction)

structure ReactionOutput (exec : Executable net) where
  reactor : ReactorId net
  reaction : Reaction reactor.class
  raw : reaction.val.outputType exec.time

namespace ReactionOutput

variable {exec : Executable net}

def fromRaw {reactor : ReactorId net} {reaction : Reaction reactor.class} (raw : reaction.val.outputType exec.time) : ReactionOutput exec :=
  { reactor, reaction, raw }

def stopRequested (output : ReactionOutput exec) := output.raw.stopRequested

def events (output : ReactionOutput exec) :=
  output.raw.events.map fun event => 
    Event.action 
      event.time 
      ⟨output.reactor, output.reaction.subAE.coe event.action⟩ 
      (output.reaction.subAE.coeEqType ▸ event.value)

def «local» (output : ReactionOutput exec) (port : output.reactor.outputs.vars) : Option (output.reactor.outputs.type port) := 
  match h : output.reaction.subPE.inv (.inl port) with
  | none => none -- independent port
  | some port' => output.reaction.subPE.invEqType h ▸ output.raw.ports port'

-- This function implements the core of the `child` function below.
-- It's only missing some type casts for the `port` (and consequently the return type).
private def child' (output : ReactionOutput exec) {child : ReactorId.Child output.reactor} (port : (child.class.class.interface .inputs).vars) : Option (child.class.class.interface .inputs |>.type port) := 
  match h : output.reaction.subPE.inv (.inr ⟨child.class, port⟩) with
  | none => none -- independent port
  | some port' => output.reaction.subPE.invEqType h ▸ output.raw.ports port'

private theorem child_type_correctness {reactor : ReactorId net} {child : ReactorId.Child reactor} {port} :
  (child.class.class.interface .inputs).type (Graph.Path.Child.class_eq_class ▸ port) = (child.val.inputs).type port := by
  simp [ReactorId.inputs, Graph.Class.interface, ReactorId.Child.class]
  congr
  · exact Graph.Path.Child.class_eq_class
  · sorry -- TODO: This should hold by reflexivity.

def child (output : ReactionOutput exec) {child : ReactorId.Child output.reactor} (port : child.val.inputs.vars) : Option (child.val.inputs.type port) := 
  child_type_correctness ▸ output.child' (Graph.Path.Child.class_eq_class ▸ port : child.class.class.interface .inputs |>.vars)

theorem events_LawfulQueue (output : ReactionOutput exec) : Executable.LawfulQueue output.events exec.time := by
  intro _ h
  simp [events, Array.map_getElem?, Bind.bind, Option.bind] at h
  split at h
  · contradiction
  case _ e _ => 
    simp at h
    simp [Event.time, ←h, e.time.property]

end ReactionOutput
end Network.Executable