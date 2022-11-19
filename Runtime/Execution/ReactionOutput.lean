import Runtime.Execution.Basic

namespace Execution

open Network Graph
open Class (Reaction)

structure ReactionOutput (exec : Executable net) where
  reactor : ReactorId net
  reaction : Reaction reactor.class
  raw : reaction.val.outputType exec.time

namespace ReactionOutput

variable {exec : Executable net}

def fromRaw {reactor : ReactorId net} {reaction : Reaction reactor.class} (raw : reaction.val.outputType exec.time) : ReactionOutput exec :=
  { reactor, reaction, raw }

def stopRequested (output : ReactionOutput exec) := output.raw.stopRequested

def writtenPortsWithDelayedConnections (output : ReactionOutput exec) : Array (PortId net .output) :=
  if h : output.reactor.isCons then
    output.raw.writtenPorts.filterMap fun port =>
      match output.reaction.subPE.coe port with
      | .inr _ => none
      | .inl port =>
        let split := output.reactor.split h -- TODO: We can't destruct here because then the type cast on `port'` doesn't work.
        let parent := split.fst
        let leaf := split.snd
        -- TODO: Reevaluate whether it's worth performing this check this early, instead of delaying
        --       it until `Next.for`.
        if parent.class.connections.delayed ⟨leaf, Path.split_class h ▸ port⟩ |>.isEmpty
        then none
        else some ⟨output.reactor, port⟩
  else
    -- In this case the reaction that produced the output lives in the top level reactor,
    -- so there are no connections and hence no propagations.
    #[]

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

def actionEvents (output : ReactionOutput exec) :=
  output.raw.events.map fun event =>
    Event.action
      event.time
      ⟨output.reactor, output.reaction.subAE.coe event.action⟩
      (output.reaction.subAE.coeEqType ▸ event.value)

theorem actionEvents_LawfulQueue (output : ReactionOutput exec) :
  Executable.LawfulQueue output.actionEvents exec.time := by
  intro _ h
  simp [actionEvents, Array.map_getElem?, Bind.bind, Option.bind] at h
  split at h
  · contradiction
  case _ e _ =>
    simp at h
    simp [Event.time, ←h, e.time.property]

end ReactionOutput
end Execution
