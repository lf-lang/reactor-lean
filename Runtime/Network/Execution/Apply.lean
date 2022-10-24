import Runtime.Network.Execution.Basic

open Network

structure Reaction.Output (net : Network) where
  reactor : ReactorId net
  reaction : reactor.class.reactionType
  time : Time
  raw : reaction.outputType time

abbrev Reaction.Output.domain (output : Reaction.Output net) : Interface.Scheme :=
  output.reactor.class.interface .outputs

def Reaction.Output.fromRaw {reactor : ReactorId net} {reaction : reactor.class.reactionType} {time} (raw : reaction.outputType time) : Reaction.Output net :=
  { reactor, reaction, time, raw }

def Reaction.Output.events (output : Reaction.Output net) :=
  output.raw.events.map fun event => Event.action event.time ⟨output.reactor, event.action⟩ event.value

inductive Reaction.Output.LocalValue (output : Reaction.Output net) (port : output.domain.vars)
  | independent
  | absent
  | present (value : output.domain.type port) -- {port : output.reaction.portEffects} (value : (output.reactor.class.interface .outputs).restrict output.reaction.portEffects |>.type port)

def Reaction.Output.LocalValue.value? : LocalValue output port → Option (output.domain.type port)
  | present value        => value
  | independent | absent => none

-- Note: This theorem is really only needed for `Reaction.Output.local`.
def Reaction.Output.local_type_correctness {port'} : 
  (output.reaction.portEffectsInjCoe.inv (.inl port) = some port') → 
  (output.reactor.class.reactionOutputScheme |>.restrict output.reaction.portEffects |>.type port') = (domain output).type port :=
  (by rw [Interface.Scheme.restrict_type, output.reaction.portEffectsInjCoe.invCoeId _ ·])

def Reaction.Output.local (output : Reaction.Output net) (port : output.domain.vars) : LocalValue output port := 
  match h : output.reaction.portEffectsInjCoe.inv (.inl port) with
  | none => .independent
  | some port' =>
    match output.raw.ports port' with
    | none => .absent
    | some value => .present (local_type_correctness h ▸ value)

namespace Network.Executable    

def apply (exec : Executable net) (output : Reaction.Output net) : Executable net := { exec with
  queue := exec.queue.merge output.events
  reactors := fun id => { exec.reactors id with
    interface := 
      if      h : id = output.reactor then h ▸ targetReactor exec output  -- Updates the output ports of the reaction's reactor.
      else if h : id ≻ output.reactor then nestedReactor exec output id h -- Updates the input ports of nested reactors.
      else                                 exec.reactors id |>.interface  -- Unaffected reactors.
  }
  lawfulQueue := sorry
}
where 
  targetReactor (exec : Executable net) (output : Reaction.Output net) : (kind : Reactor.InterfaceKind) → kind.interfaceType (output.reactor.class.interface kind)
    | .outputs => fun var => (output.local var).value?.orElse (fun _ => exec.interface output.reactor .outputs var)
    | .state => output.raw.state
    | interface => exec.interface output.reactor interface
  nestedReactor (exec : Executable net) (output : Reaction.Output net) (id : ReactorId net) (hc : id ≻ output.reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (id.class.interface kind)
    | .inputs => nestedInputs exec output id hc
    | interface => exec.reactors id |>.interface interface 
  nestedInputs (exec : Executable net) (output : Reaction.Output net) (id : ReactorId net) (hc : id ≻ output.reactor) : Interface? (id.class.interface .inputs) :=
    let currentReactor := exec.reactors id
    fun var =>
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
      sorry


end Network.Executable    