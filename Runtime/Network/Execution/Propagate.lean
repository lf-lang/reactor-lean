import Runtime.Network.Execution.Basic

namespace Network.Executable

def Sib (reactor : ReactorId net) := { id : ReactorId net // id ≂ reactor }

-- Note: By the definition of `Connections`, the root reactor can't have a connection to itself.
--       Hence, if `reactor` = `sib` = `nil`, we automatically get `none`. 
private def aux (exec : Executable net) {reactor : ReactorId net} (sib : Sib reactor) (dst : sib.val.inputs.vars) : Option (sib.val.inputs.type dst) :=
  if h₁ : sib.val.isRoot then 
    none -- cf. note above
  else
    let parent := sib.val.prefix (Graph.Path.isCons_iff_not_isNil.mpr h₁)
    let subport : Graph.Class.Subport parent.class .input := sorry -- ⟨sorry, dst⟩  -- CONTINUE HERE
    match h₂ : parent.class.connections.source subport with
    | none => none -- independent
    | some src => 
      if h₃ : src.child.class = reactor.class then 
        have H := parent.class.connections.eqType h₂             -- (subport.child.class.interface .inputs).type subport.port = (src.child.class.interface .outputs).type src.port
        let a := exec.interface reactor .outputs (h₃ ▸ src.port) -- Option (reactor.class.interface .outputs).type (h₃ ▸ src.port)
        sorry                                                    -- Option (sib.val.inputs.type dst)
      else 
        none -- independent

def propagate (exec : Executable net) (reactor : ReactorId net) : Executable net := { exec with
  reactors := fun id => { exec.reactors id with
    interface := if h : id ≂ reactor then sibling exec ⟨id, h⟩ else exec.interface id
  }
}
where
  sibling (exec : Executable net) {reactor : ReactorId net} (sib : Sib reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (sib.val.class.interface kind)
    | .inputs => fun port => (aux exec sib port).orElse (fun _ => exec.interface sib.val .inputs port)
    | _ => (exec.reactors sib.val).interface _

end Network.Executable