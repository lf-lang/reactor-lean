import Runtime.Network.Execution.Event

open Network.Graph in
structure Reactor {net : Network} (cls : Class net) where
  interface : (kind : Reactor.InterfaceKind) → kind.interfaceType (cls.interface kind)
  timer : cls.timers → Timer

open Network in
structure Reaction.Output (net : Network) (time : Time) where
  reactor : ReactorId net
  reaction : reactor.class.reactionType
  raw : reaction.outputType time

def Network.ReactorId.mkEvents (reactor : ReactorId net) {reaction : reactor.class.reactionType} (output : reaction.outputType time) :=
  output.events.map fun event => Event.action event.time ⟨reactor, event.action⟩ event.value

namespace Network

structure Executable (net : Network) where
  tag : Tag := ⟨0, 0⟩
  physicalOffset : Duration
  queue : Array (Event net)
  reactors : (id : ReactorId net) → Reactor id.class
  isShuttingDown : Bool := false
  lawfulQueue : (queue[0]? = some event) → event.time ≥ tag.time

namespace Executable

def isStartingUp (exec : Executable net) : Bool := 
  exec.tag = ⟨0, 0⟩

def absoluteTime (exec : Executable net) : Time :=
  exec.tag.time + exec.physicalOffset

def interface (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).interface

def timer (exec : Executable net) (id : ReactorId net) :=
  (exec.reactors id).timer

-- def timer (exec : Executable net) (id : TimerId net) : Timer :=
--   exec.reactors id.reactor |>.timer id.timer

open Graph Path Class in
theorem _root_.Network.Graph.Path.reactionInputScheme_right_type_eq_extend_child_type {path : Path graph start} {child childOutput} : 
  path.class.reactionInputScheme.type (.inr ⟨child, childOutput⟩) = 
  ((path.extend child).class.interface .outputs).type (extend_class ▸ childOutput) := by
  simp
  sorry -- by extend_class

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

def apply (exec : Executable net) {reactor : ReactorId net} {reaction : reactor.class.reactionType} (output : reaction.outputType exec.tag.time) : Executable net := { exec with
  queue := exec.queue.merge (reactor.mkEvents output)
  reactors := fun id => { exec.reactors id with
    interface := 
      -- 1. Updates the output ports of the reaction's reactor.
      -- 2. Updates the input ports of nested reactors.
      -- 3. Unaffected reactors.
      if      h : id = reactor then targetReactor exec (reaction := h ▸ reaction) (h ▸ output)
      else if h : id ≻ reactor then nestedReactor exec output id h
      else                          exec.reactors id |>.interface 
  }
  lawfulQueue := sorry
}
where 
  targetReactor (exec : Executable net) (output : Reaction.Output net exec.tag.time) : (kind : Reactor.InterfaceKind) → kind.interfaceType (output.reactor.class.interface kind)
    | .outputs => localOutputs exec output
    | .state => output.raw.state
    | interface => exec.interface output.reactor interface
  nestedReactor (exec : Executable net) {reactorId : ReactorId net} {reaction : reactorId.class.reactionType} (output : reaction.outputType exec.tag.time) (id : ReactorId net) (hc : id ≻ reactorId) : (kind : Reactor.InterfaceKind) → kind.interfaceType (id.class.interface kind)
    | .inputs => nestedInputs exec output id hc
    | interface => exec.reactors id |>.interface interface 
  localOutputs (exec : Executable net) (output : Reaction.Output net exec.tag.time) : Interface? (output.reactor.class.interface .outputs) :=
    let currentReactor := exec.reactors output.reactor
    fun var =>
      match h : InjectiveCoe.inv (Sum.inl var) with 
      | none => currentReactor.interface .outputs var
      | some var' =>
        match output.raw.ports var' with
        | none => currentReactor.interface .outputs var
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
      if h : id.isSiblingOf reactorId then 
        siblingReactor exec reactorId id h
      else                                  
        exec.reactors id |>.interface
  }
}
where
  siblingReactor (exec : Executable net) (reactorID : ReactorId net) (id : ReactorId net) (hs : id.isSiblingOf reactorId) : (kind : Reactor.InterfaceKind) → kind.interfaceType (id.class.interface kind) :=
    let currentReactor := exec.reactors id
    fun
    | .inputs => 
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
    | interface => currentReactor.interface interface 

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net)
  queue  : Array (Event net)

def next (exec : Executable net) : Option (Next net) := 
  match h : exec.queue[0]? with 
  | none => none
  | some nextEvent =>
    let nextTag := exec.tag.advance ⟨nextEvent.time, exec.lawfulQueue h⟩
    let ⟨candidates, later⟩ := exec.queue.split (·.time = nextTag.time)  
    let ⟨next, postponed⟩ := candidates.unique (·.id)
    some {
      tag := nextTag
      events := next
      queue := (postponed ++ later).merge (newTimerEvents exec nextTag.time next)
    }
where 
  -- This function assumes that each timer event in `next` fires at `exec.tag.time`.
  newTimerEvents (exec : Executable net) (nextTime : Time) (next : Array (Event net)) : Array (Event net) := 
    next.filterMap fun event =>
      match event with 
      | .action .. => none
      | .timer _ id =>
        match exec.timer id |>.period with
        | none => none
        | some p => return .timer (nextTime + p) id

def advance (exec : Executable net) (next : Next net) : Executable net := { exec with
  tag := next.tag
  queue := next.queue
  reactors := fun id => { exec.reactors id with
    interface := fun
      | .inputs | .outputs => Interface?.empty
      | .actions           => (actionForEvents next.events ⟨id, ·⟩)
      | unchanged          => exec.reactors id |>.interface unchanged
  }
  lawfulQueue := sorry
}
where 
  actionForEvents (events : Array <| Event net) (id : ActionId net) : Option <| (id.reactor.class.interface .actions).type id.action :=
    match h : events.findP? (·.id = .action id) with
    | none => none
    | some event => 
      have h := Array.findP?_property h
      have h := of_decide_eq_true h
      have H : (event.action' h).id = id := sorry
      H ▸ (event.action' h |>.value)

def prepareForShutdown (exec : Executable net) : Executable net := { exec with
  tag := { exec.tag with microstep := exec.tag.microstep + 1 }
  isShuttingDown := true
}

-- We can't separate out a `runInst` function at the moment as `IO` isn't universe polymorphic.
partial def run (exec : Executable net) (topo : Array (ReactionId net)) (reactionIdx : Nat) : IO Unit := do
  match topo[reactionIdx]? with 
  | none => 
    unless exec.isShuttingDown do
      match exec.next with
      | none => run exec.prepareForShutdown topo 0
      | some next => run (exec.advance next) topo 0
  | some reactionId =>
    IO.sleepUntil exec.absoluteTime
    let mut exec := exec
    let reaction := reactionId.reaction
    if exec.triggers reaction then
      let reactorId := reactionId.reactor
      let ports     := exec.reactionInputs reactorId
      let actions   := exec.reactors reactorId |>.interface .actions
      let state     := exec.reactors reactorId |>.interface .state
      let params    := exec.reactors reactorId |>.interface .params
      let output ← reaction.run ports actions state params exec.tag exec.physicalOffset
      exec := exec.apply output |>.propagate reactorID
    run exec topo (reactionIdx + 1)

end Executable

end Network
