import Runtime.Execution.ReactionOutput

namespace Execution.Executable
open Network

def apply (exec : Executable net) (output : ReactionOutput exec) : Executable net := { exec with
  queue := exec.queue.merge output.actionEvents
  state := stateAfter output
  reactors := fun id => { exec.reactors id with
    interface :=
      if      h : id = output.reactor then h ▸ container output -- Updates the output ports of the reaction's container.
      else if h : id ≻ output.reactor then child output ⟨id, h⟩ -- Updates the input ports of child reactors.
      else                                 exec.interface id    -- Unaffected reactors.
  }
  toPropagate := exec.toPropagate ++ output.writtenPortsWithDelayedConnections
  lawfulQueue := LawfulQueue.merge exec.lawfulQueue output.actionEvents_LawfulQueue
}
where
  container (output : ReactionOutput exec) : (kind : Reactor.InterfaceKind) → kind.interfaceType (output.reactor.class.interface kind)
    | .outputs => fun var => (output.local var).orElse (fun _ => exec.interface output.reactor .outputs var)
    | .state   => output.reaction.eqState ▸ output.raw.state
    | _        => exec.interface output.reactor _

  child (output : ReactionOutput exec) (child : ReactorId.Child output.reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType ((child : ReactorId net).class.interface kind)
    | .inputs => fun var => (output.child var).orElse (fun _ => exec.interface child .inputs var)
    | _       => exec.interface child _

  stateAfter (output : ReactionOutput exec) : Executable.State :=
    if output.stopRequested then
      -- When requesting to stop, we need to make sure we don't override
      -- if we're already in the process of shutting down.
      match exec.state with
      | .executing | .stopRequested => .stopRequested
      | .shuttingDown               => .shuttingDown
    else
      exec.state

end Execution.Executable
