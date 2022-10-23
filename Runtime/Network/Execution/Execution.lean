import Runtime.Network.Execution.Next

theorem Network.Graph.Path.reactionInputScheme_right_type_eq_extend_child_type {path : Path graph start} {child childOutput} : 
  path.class.reactionInputScheme.type (.inr ⟨child, childOutput⟩) = 
  ((path.extend child).class.interface .outputs).type (extend_class ▸ childOutput) := by
  simp
  sorry -- by extend_class

namespace Network.Executable

-- An interface for all ports (local and nested) that can act as inputs of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactor : ReactorId net) : Interface? reactor.class.reactionInputScheme
  | .inl localInput           => exec.interface reactor .inputs localInput
  | .inr ⟨child, childOutput⟩ => open Graph Path Class in reactionInputScheme_right_type_eq_extend_child_type ▸ exec.interface (reactor.extend child) .outputs (extend_class ▸ childOutput)

def triggers (exec : Executable net) {reactor : ReactorId net} (reaction : reactor.class.reactionType) : Bool :=
  reaction.triggers.any fun trigger =>
    match trigger with
    | .port   port   => exec.reactionInputs reactor     |>.isPresent port
    | .action action => exec.interface reactor .actions |>.isPresent action
    | .timer  timer  => exec.timer reactor timer        |>.firesAtTag exec.tag
    | .startup       => exec.isStartingUp
    | .shutdown      => exec.isShuttingDown

def apply (exec : Executable net) (output : Reaction.Output net exec.tag.time) : Executable net := { exec with
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
  targetReactor (exec : Executable net) (output : Reaction.Output net exec.tag.time) : (kind : Reactor.InterfaceKind) → kind.interfaceType (output.reactor.class.interface kind)
    | .outputs => localOutputs exec output
    | .state => output.raw.state
    | interface => exec.interface output.reactor interface
  nestedReactor (exec : Executable net) (output : Reaction.Output net exec.tag.time) (id : ReactorId net) (hc : id ≻ output.reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (id.class.interface kind)
    | .inputs => nestedInputs exec output id hc
    | interface => exec.reactors id |>.interface interface 
  localOutputs (exec : Executable net) (output : Reaction.Output net exec.tag.time) : Interface? (output.reactor.class.interface .outputs) :=
    fun var =>
      match h : InjectiveCoe.inv (Sum.inl var) with 
      | none => exec.interface output.reactor .outputs var
      | some var' =>
        match output.raw.ports var' with
        | none => exec.interface output.reactor .outputs var
        | some val =>
          sorry -- h ▸ val
  nestedInputs (exec : Executable net) (output : Reaction.Output net exec.tag.time) (id : ReactorId net) (hc : id ≻ output.reactor) : Interface? (id.class.interface .inputs) :=
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

def propagate (exec : Executable net) (reactor : ReactorId net) : Executable net := { exec with
  reactors := fun id => { exec.reactors id with
    interface := 
      if h : id ≂ reactor 
      then siblingReactor exec reactor id h
      else exec.interface id
  }
}
where
  siblingReactor (exec : Executable net) (reactor : ReactorId net) (id : ReactorId net) (hs : id ≂ reactor) : (kind : Reactor.InterfaceKind) → kind.interfaceType (id.class.interface kind) :=
    let currentReactor := exec.reactors id
    fun
    | .inputs => 
      sorry /-
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
    | interface => currentReactor.interface interface 

-- Advances the given executable to the state given by `next`.
-- This includes:
-- * advancing the tag
-- * dequeueing events for that tag
-- * clearing all ports
-- * setting actions' values for the given tag
def advance (exec : Executable net) (next : Next net) : Executable net := { exec with
  tag := next.tag
  queue := next.queue
  reactors := fun id => { exec.reactors id with
    interface := fun
      | .inputs | .outputs => Interface?.empty
      | .actions           => next.actions id
      | unaffected         => exec.interface id unaffected
  }
  lawfulQueue := next.lawfulQueue 
}

def prepareForShutdown (exec : Executable net) : Executable net := { exec with
  tag := { exec.tag with microstep := exec.tag.microstep + 1 }
  isShuttingDown := true
}

-- We can't separate out a `runInst` function at the moment as `IO` isn't universe polymorphic.
partial def run (exec : Executable net) (topo : Array (ReactionId net)) (reactionIdx : Nat) : IO Unit := do
  match topo[reactionIdx]? with 
  | none => 
    unless exec.isShuttingDown do
      match Next.for exec with
      | none => run exec.prepareForShutdown topo 0
      | some next => run (exec.advance next) topo 0
  | some reactionId =>
    IO.sleepUntil exec.absoluteTime
    let mut exec := exec
    let reaction := reactionId.reaction
    if exec.triggers reaction then
      let reactor := reactionId.reactor
      let ports   := exec.reactionInputs reactor
      let actions := exec.interface reactor .actions
      let state   := exec.interface reactor .state
      let params  := exec.interface reactor .params
      let rawOutput ← reaction.run ports actions state params exec.tag exec.physicalOffset
      let output := Reaction.Output.fromRaw rawOutput
      exec := exec.apply output |>.propagate reactor
    run exec topo (reactionIdx + 1)

end Network.Executable