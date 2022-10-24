import Runtime.Network.Execution.Basic

namespace Network.Executable

structure ReactionOutput (exec : Executable net) where
  reactor : ReactorId net
  reaction : reactor.class.reactionType
  raw : reaction.outputType exec.tag.time

namespace ReactionOutput

variable {exec : Executable net}

def fromRaw {reactor : ReactorId net} {reaction : reactor.class.reactionType} (raw : reaction.outputType exec.tag.time) : ReactionOutput exec :=
  { reactor, reaction, raw }

def events (output : ReactionOutput exec) :=
  output.raw.events.map fun event => Event.action event.time ⟨output.reactor, event.action⟩ event.value

inductive Value (α : Type)
  | independent
  | absent
  | present (value : α)

def Value.value? : Value α → Option α
  | present value        => value
  | independent | absent => none

-- Note: This theorem is really only needed for `Reaction.Output.local`.
private def local_type_correctness {output : ReactionOutput exec} {port port'} : 
  (output.reaction.portEffectsInjCoe.inv (.inl port) = some port') → 
  (output.reactor.class.reactionOutputScheme |>.restrict output.reaction.portEffects |>.type port') = output.reactor.outputs.type port :=
  (by rw [Interface.Scheme.restrict_type, output.reaction.portEffectsInjCoe.invCoeId _ ·])

def «local» (output : ReactionOutput exec) (port : output.reactor.outputs.vars) : Value (output.reactor.outputs.type port) := 
  match h : output.reaction.portEffectsInjCoe.inv (.inl port) with
  | none => .independent
  | some port' =>
    match output.raw.ports port' with
    | none => .absent
    | some value => .present (local_type_correctness h ▸ value)

def child (output : ReactionOutput exec) {child : ReactorId.Child output.reactor} (port : (child : ReactorId net).inputs.vars) : Value ((child : ReactorId net).inputs.type port) := 
  -- match h : output.reaction.portEffectsInjCoe.inv (.inr ⟨child.class, port⟩) with
  -- | none => .independent
  -- | some port' =>
  --   match output.raw.ports port' with
  --   | none => .absent
  --   | some value => .present (local_type_correctness h ▸ value)
  sorry
    -- nestedInputs (exec : Executable net) (output : Reaction.Output net) (id : ReactorId net) (hc : id ≻ output.reactor) : Interface? (id.class.interface .inputs) :=
  --  let currentReactor := exec.reactors id
  --  fun var =>
      /-
      let nestedID := id.last hc
      have h₁ : (net.scheme id |>.interface .inputs).vars = (net.subinterface (net.class reactorID) nestedID .inputs).vars := by sorry -- rw [Graph.child_schemes_eq_parent_subschemes]
      let var₁ : (net.reactionOutputScheme' reactorID).vars := .inr ⟨nestedID, h₁ ▸ var⟩
      match h : InjectiveCoe.inv var₁ with 
      | none => currentReactor.interface .inputs var
      | some var₂ =>
        match output.ports var₂ with
        | none => currentReactor.interface .inputs var
        | some val =>
          have h : (net.class reactorID |> net.reactionOutputScheme |>.restrict reaction.portEffects).type var₂ = (net.scheme id |>.interface .inputs).type var := by
            rw [(net.reactionOutputScheme' reactorID).restrict_type]
            rw [InjectiveCoe.invCoeId _ h]
            -- have := Graph.child_schemes_eq_parent_subschemes hc
            sorry
          h ▸ val
      -/




theorem events_LawfulQueue (output : ReactionOutput exec) : Executable.LawfulQueue output.events exec.tag.time := by
  intro _ h
  simp [events, Array.map_getElem?, Bind.bind, Option.bind] at h
  split at h
  · contradiction
  case _ e _ => 
    simp at h
    simp [Event.time, ←h, e.time.property]

end ReactionOutput
end Network.Executable