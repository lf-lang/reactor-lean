import Runtime.Network.Execution.Basic

namespace Network.Executable

open Graph

private def Sib (reactor : ReactorId net) := { id : ReactorId net // id ≂ reactor }

def propagate (exec : Executable net) (reaction : ReactionId net) : Executable net := { exec with
  reactors := fun id => { exec.reactors id with
    interface := if h : id ≂ reaction.reactor then sibling exec reaction ⟨id, h⟩ else exec.interface id
  }
}
where
  sibling (exec : Executable net) (reaction : ReactionId net) (sib : Sib reaction.reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (sib.val.class.interface kind)
    | .inputs => fun port => (aux₁ sib port).orElse (fun _ => exec.interface sib.val .inputs port)
    | _       => (exec.reactors sib.val).interface _

  -- Note: By the definition of `Connections`, the root reactor can't have a connection to itself.
  --       Hence, if `reactor` = `sib` = `nil`, we automatically get `none`. 
  aux₁ {reaction : ReactionId net} (sib : Sib reaction.reactor) (dst : sib.val.inputs.vars) : Option (sib.val.inputs.type dst) :=
    if h : sib.val.isRoot 
    then none -- cf. note above
    else aux₂ sib dst (Graph.Path.isCons_iff_not_isNil.mpr h)

  aux₂ {reaction : ReactionId net} (sib : Sib reaction.reactor) (dst : sib.val.inputs.vars) (h : sib.val.isCons) : Option (sib.val.inputs.type dst) :=
    let split := sib.val.split h -- TODO: We can't destruct here because then the type cast on `dst` doesn't work.
    let parent := split.fst
    let leaf := split.snd
    type_correctness₂ ▸ aux₃ parent leaf (Path.split_class (path := sib.val) ▸ dst)

  aux₃ (parent : ReactorId net) (leaf : Class.Child parent.class) (dst : (leaf.class.interface .inputs).vars) : Option ((leaf.class.interface .inputs).type dst) :=
    match h : parent.class.connections.source ⟨leaf, dst⟩ with
    | some src => type_correctness₃ h ▸ aux₄ src
    | none => none -- independent

  aux₄ {parent : ReactorId net} (src : Class.Subport parent.class .output) : Option src.type :=
    if h : src.child.class = reaction.reactor.class 
    then type_correctness₄ h ▸ aux₅ (h ▸ src.port)
    else none -- independent
  
  aux₅ (port : reaction.reactor.class.interface .outputs |>.vars) : Option (reaction.reactor.outputs.type port) :=
    if reaction.affects port 
    then exec.interface reaction.reactor .outputs port
    else none -- independent

  type_correctness₂ {reaction : ReactionId net} {sib : Sib reaction.reactor} {dst h} : 
    (sib.val.inputs).type dst = ((sib.val.split h).snd.class.interface .inputs).type (Path.split_class (path := sib.val) ▸ dst) := by
    simp
    congr
    · exact Path.split_class.symm
    · have h' : (sib.val.class.interface .inputs).vars = ((sib.val.split h).snd.class.interface .inputs).vars := by congr; exact Path.split_class.symm
      sorry 
        -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Simple.20HEq
        -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Questions.20on.20dependent.20elimination.20failures

  type_correctness₃ {parent : ReactorId net} {src : Class.Subport parent.class .output} {leaf : Class.Child parent.class} {dst} :
    (parent.class.connections.source ⟨leaf, dst⟩ = some src) → src.type = (leaf.class.interface .inputs).type dst :=
    (by simp [parent.class.connections.eqType ·])

  type_correctness₄ {reaction : ReactionId net} {parent : ReactorId net} {src : Class.Subport parent.class .output} :
    (h : src.child.class = reaction.reactor.class) →
    (reaction.reactor.class.interface .outputs).type (h ▸ src.port) = src.type := by 
    intro h
    simp [Class.Subport.type]
    congr
    · exact h.symm
    · have h' : (reaction.reactor.class.interface .outputs).vars = (src.child.class.interface .outputs).vars := by simp [h]
      sorry 
        -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Simple.20HEq
        -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Questions.20on.20dependent.20elimination.20failures

end Network.Executable