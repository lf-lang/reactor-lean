import Runtime.Network.Execution.Basic

namespace Network.Executable

def Sib (reactor : ReactorId net) := { id : ReactorId net // id ≂ reactor }

inductive Value (α : Type)
  | independent
  | absent
  | present (value : α)

def Value.value? : Value α → Option α
  | present value        => value
  | independent | absent => none

private def aux (exec : Executable net) {reactor : ReactorId net} (sib : Sib reactor) (port : sib.val.inputs.vars) : Value (sib.val.inputs.type port) :=
  sorry

def propagate (exec : Executable net) (reactor : ReactorId net) : Executable net := { exec with
  reactors := fun id => { exec.reactors id with
    interface := if h : id ≂ reactor then sibling exec ⟨id, h⟩ else exec.interface id
  }
}
where
  sibling (exec : Executable net) {reactor : ReactorId net} (sib : Sib reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (sib.val.class.interface kind)
    | .inputs => let x := (aux exec sib sorry).value?; sorry
    | _ => (exec.reactors sib.val).interface _
      /-
      fun var => 
        have hc : id.isChildOf id.prefix := open Graph.Path in by have ⟨_, _, hc⟩ := isSiblingOf_is_cons hs; simp [hc, cons_isChildOf_prefix]
        have H : (net.subinterface (net.class id.prefix) (id.last hc) .inputs).vars = ((net.scheme id).interface .inputs).vars := sorry
        let connections := net.connections' id.prefix
        let destination : Subport net (net.class id.prefix) .input := { reactor := id.last hc, port := H ▸ var }
        match hc : connections.source destination with
        | none => currentReactor.interface .inputs var
        | some source =>
          -- The reactor identified by `reactorID` is the only one that can have a changed output port, 
          -- so we only need to propagate a value if the source is part of that reactor.
          -- TODO: We should only have to check if source.reactor = reactorID.last, because by hs we know that id.prefix = reactorID.prefix
          if he : id.prefix.extend source.reactor = reactorID then 
            let x := source.port
            let y := exec.reactors reactorID |>.interface .outputs
            have h : net.subinterface (net.class id.prefix) source.reactor = (net.scheme reactorID).interface := by
              have h1 : id.prefix = reactorID.prefix := sorry -- cf. TODO above.
              have h2 : ∀ id h, net.subinterface (net.class id.prefix) (id.last h) = (net.scheme id).interface := sorry
              sorry
            let val := y (h ▸ x)
            have HH : ((net.scheme reactorID).interface .outputs).type (h ▸ x) = ((net.scheme id).interface .inputs).type var := by
              have := connections.eqType hc
              sorry
            HH ▸ val
          else
            currentReactor.interface .inputs var
          -/

end Network.Executable