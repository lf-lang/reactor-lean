import Runtime.Execution.Basic

namespace Execution.Executable

open Network Graph

private def Sib (reactor : ReactorId net) := { id : ReactorId net // id ≂ reactor }

def propagate (exec : Executable net) (reaction : ReactionId net) : Executable net := { exec with
  reactors := fun id => { exec.reactors id with
    interface :=
      if h : id ≂ reaction.reactor
      then sibling exec reaction ⟨id, h⟩
      else exec.interface id
  }
}
where
  sibling (exec : Executable net) (reaction : ReactionId net) (sib : Sib reaction.reactor) :
    (kind : Reactor.InterfaceKind) → kind.interfaceType (sib.val.class.interface kind)
    | .inputs => fun port => (aux₁ sib port).orElse (fun _ => exec.interface sib.val .inputs port)
    | _       => (exec.reactors sib.val).interface _

  -- Note: By the definition of `Connections`, the root reactor can't have a connection to itself.
  --       Hence, if `reactor` = `sib` = `nil`, we automatically get `none`.
  aux₁ {reaction : ReactionId net} (sib : Sib reaction.reactor) (dst : sib.val.inputs.vars) :
    Option (sib.val.inputs.type dst) :=
    if h : sib.val.isRoot
    then none -- cf. note above
    else aux₂ sib dst (Graph.Path.isCons_iff_not_isNil.mpr h)

  aux₂
    {reaction : ReactionId net} (sib : Sib reaction.reactor) (dst : sib.val.inputs.vars)
    (h : sib.val.isCons) : Option (sib.val.inputs.type dst) :=
    let split := sib.val.split h -- TODO: We can't destruct here because then `Path.split_class` doesn't work.
    let parent := split.fst
    let leaf := split.snd
    have h₁ := by rw [Path.split_class h]
    have h₂ := by congr <;> simp [Path.split_class h, cast_heq _ _]
    aux₃ parent leaf (dst |> cast h₁) |> cast h₂

  aux₃
    (parent : ReactorId net)
    (leaf : Class.Child parent.class)
    (dst : (leaf.class.interface .inputs).vars) :
    Option ((leaf.class.interface .inputs).type dst) :=
    match h : parent.class.connections.instantaneous ⟨leaf, dst⟩ with
    | none => none -- independent
    | some src =>
      have h := by simp [← parent.class.connections.instEqType h]
      aux₄ src |> cast h

  aux₄ {parent : ReactorId net} (src : Class.Subport parent.class .output) : Option src.type :=
    if h : src.child.class = reaction.reactor.class
    then
      have h₁ := by rw [h]
      have h₂ := by congr <;> simp [h, cast_heq _ _]
      aux₅ (src.port |> cast h₁) |> cast h₂
    else
      none -- independent

  aux₅ (port : reaction.reactor.class.interface .outputs |>.vars) :
    Option (reaction.reactor.outputs.type port) :=
    if reaction.affects port
    then exec.interface reaction.reactor .outputs port
    else none -- independent

end Execution.Executable
