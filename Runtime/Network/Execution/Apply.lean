import Runtime.Network.Execution.ReactionOutput

namespace Network.Executable

def apply (exec : Executable net) (output : ReactionOutput exec) : Executable net := { exec with
  queue := exec.queue.merge output.events
  reactors := fun id => { exec.reactors id with
    interface := 
      if      h : id = output.reactor then h ▸ container output -- Updates the output ports of the reaction's container.
      else if h : id ≻ output.reactor then child output ⟨id, h⟩ -- Updates the input ports of child reactors.
      else                                 exec.interface id    -- Unaffected reactors.
  }
  lawfulQueue := LawfulQueue.merge exec.lawfulQueue output.events_LawfulQueue
}
where 
  container (output : ReactionOutput exec) : (kind : Reactor.InterfaceKind) → kind.interfaceType (output.reactor.class.interface kind)
    | .outputs => fun var => (output.local var).orElse (fun _ => exec.interface output.reactor .outputs var)
    | .state => output.raw.state
    | _ => exec.interface output.reactor _
  child (output : ReactionOutput exec) (id : ReactorId.Child output.reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType ((id : ReactorId net).class.interface kind)
    | .inputs => fun var => (output.child var).orElse (fun _ => exec.interface id .inputs var)
    | _ => exec.interface id _

end Network.Executable