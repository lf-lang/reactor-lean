import Runtime.Network.Execution.Basic

namespace Network.Executable

def Sib (reactor : ReactorId net) := { id : ReactorId net // id ≂ reactor }

theorem aux_type_correctness {reaction : ReactionId net} {sib : Sib reaction.reactor} {dst h port src} :
  ((sib.val.split h).fst.class.connections.source ⟨(sib.val.split h).snd, Graph.Path.split_class (path := sib.val) ▸ dst⟩ = some src) → 
  (reaction.reactor.class.interface .outputs).type port =
  (sib.val.class.interface .inputs).type dst := by
  intro h'
  have := (sib.val.split h).fst.class.connections.eqType h'
  sorry

-- TODO: Now that you have ReactionOutput.local, perhaps it would be easy to reintegrate propagation into `apply`?

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
      if h₃ : src.child.class = reaction.reactor.class then 
        let port := h₃ ▸ src.port
        if reaction.affects port 
        then aux_type_correctness h₂ ▸ exec.interface reaction.reactor .outputs port
        else none -- independent
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