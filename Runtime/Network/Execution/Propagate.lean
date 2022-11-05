import Runtime.Network.Execution.Basic

namespace Network.Executable

def Sib (reactor : ReactorId net) := { id : ReactorId net // id ≂ reactor }

-- Note: By the definition of `Connections`, the root reactor can't have a connection to itself.
--       Hence, if `reactor` = `sib` = `nil`, we automatically get `none`. 
private def aux (exec : Executable net) (reaction : ReactionId net) (sib : Sib reaction.reactor) (dst : sib.val.inputs.vars) : Option (sib.val.inputs.type dst) :=
  if h₁ : sib.val.isRoot then 
    none -- cf. note above
  else
    let split := sib.val.split (Graph.Path.isCons_iff_not_isNil.mpr h₁) -- TODO: We can't destruct here because then the type cast on `dst` doesn't work.
    let parent := split.fst
    let leaf := split.snd
    match h₂ : parent.class.connections.source ⟨leaf, Graph.Path.split_class (path := sib.val) ▸ dst⟩ with
    | none => none -- independent
    | some src => 
      -- TODO: Make this check more precise, by checking whether the given port is an effect of the reaction.
      if h₃ : src.child.class = reaction.reactor.class then 
        have H := parent.class.connections.eqType h₂                      -- (subport.child.class.interface .inputs).type subport.port = (src.child.class.interface .outputs).type src.port
        let a := exec.interface reaction.reactor .outputs (h₃ ▸ src.port) -- Option (reactor.class.interface .outputs).type (h₃ ▸ src.port)
        sorry                                                             -- Option (sib.val.inputs.type dst)
      else 
        none -- independent

def propagate (exec : Executable net) (reaction : ReactionId net) : Executable net := { exec with
  reactors := fun id => { exec.reactors id with
    interface := if h : id ≂ reaction.reactor then sibling exec reaction ⟨id, h⟩ else exec.interface id
  }
}
where
  sibling (exec : Executable net) (reaction : ReactionId net) (sib : Sib reaction.reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (sib.val.class.interface kind)
    | .inputs => fun port => (aux exec reaction sib port).orElse (fun _ => exec.interface sib.val .inputs port)
    | _       => (exec.reactors sib.val).interface _

end Network.Executable