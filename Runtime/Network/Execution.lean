import Runtime.Network.Basic

namespace Network

structure Event (graph : Graph) where
  time  : Time
  id    : ActionID graph
  value : (graph.schemes id.reactor .actions).type id.action

instance {graph} : Ord (Event graph) where
  compare e₁ e₂ := compare e₁.time e₂.time

structure Executable (net : Network) where
  tag : Tag
  queue : Array (Event net.graph) 
  reactors : (id : ReactorID net.tree) → Reactor (net.schemes id)

namespace Executable

-- An interface for all ports (local and nested) that can act as inputs of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactorID : ReactorID net.tree) : Interface (net.reactionInputScheme reactorID) 
  | .inl localInput => (exec.reactors reactorID) .inputs localInput
  | .inr ⟨subreactor, nestedOutput⟩ => exec.reactors (reactorID.extend subreactor) .outputs nestedOutput

def triggers (exec : Executable net) {reactorID : ReactorID net.tree} (reaction : net.reactionType reactorID) : Bool :=
  reaction.triggers.any fun trigger =>
    match trigger with
    | .port   port   => (exec.reactionInputs reactorID).isPresent port
    | .action action => (exec.reactors reactorID .actions).isPresent action

def apply (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) : Executable net := { exec with
  queue := exec.queue.merge $ output.events.map fun event => {
    time := event.time
    id := ⟨reactorID, event.action⟩
    value := event.value
  }
  reactors := fun id =>
    if h : id = reactorID then 
      -- Updates the output ports of the reaction's reactor.
      targetReactor exec (reaction := h ▸ reaction) (h ▸ output)
    else if h : id.isChildOf reactorID then 
      -- Updates the input ports of nested reactors.
      nestedReactor exec output id h
    else
      -- TODO: Propagates the reaction's reactor's updated output ports.
      exec.reactors id 
}
where 
  targetReactor (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) : Reactor (net.graph.schemes reactorID) :=
    let currentReactor := exec.reactors reactorID
    fun
    | .outputs => 
      fun var =>
        match h : InjectiveCoe.inv (Sum.inl var) with 
        | none => currentReactor .outputs var
        | some var' =>
          match output.ports var' with
          | none => currentReactor .outputs var
          | some val =>
            have h : (net.schemes reactorID .outputs).type var = ((net.reactionOutputScheme reactorID).restrict reaction.portEffects).type var' := by
              rw [(net.reactionOutputScheme reactorID).restrict_preserves_type, InjectiveCoe.invCoeId _ h]
            h ▸ val
    | .state => output.state
    | interface => currentReactor interface
  nestedReactor (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) (id : ReactorID net.tree) (h : id.isChildOf reactorID) : Reactor (net.graph.schemes id) :=
    let currentReactor := exec.reactors id
    fun
    | .inputs => 
      fun var =>
        let nestedID := id.last h
        have h₁ : (net.schemes id .inputs).vars = (net.subschemes reactorID nestedID .inputs).vars := by rw [Graph.child_schemes_eq_parent_subschemes]
        let var₁ : (net.reactionOutputScheme reactorID).vars := .inr ⟨nestedID, h₁ ▸ var⟩
        match hv : InjectiveCoe.inv var₁ with 
        | none => currentReactor .inputs var
        | some var₂ =>
          match output.ports var₂ with
          | none => currentReactor .inputs var
          | some val =>
            have h : (net.schemes id .inputs).type var = ((net.reactionOutputScheme reactorID).restrict reaction.portEffects).type var₂ := by
              rw [(net.reactionOutputScheme reactorID).restrict_preserves_type, InjectiveCoe.invCoeId _ hv]
              simp
              have := Graph.child_schemes_eq_parent_subschemes h
              sorry
            h ▸ val
    | interface => currentReactor interface 

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net.graph)
  queue  : Array (Event net.graph)

def next (exec : Executable net) : Option (Next net) := do
  let nextEvent ← exec.queue[0]?
  let nextTag := exec.tag.advance nextEvent.time
  let ⟨candidates, later⟩ := exec.queue.split (·.time = nextTag.time)  
  let ⟨current, postponed⟩ := candidates.unique (·.id)
  return {
    tag := nextTag
    events := current
    queue := postponed ++ later
  }

def advance (exec : Executable net) (next : Next net) : Executable net := {  
  tag := next.tag
  queue := next.queue
  reactors := fun id => fun
    | .inputs | .outputs => Interface.empty
    | .state             => exec.reactors id .state
    | .actions           => (actionForEvents next.events ⟨id, ·⟩)
}
where actionForEvents (events : Array $ Event net.graph) (id : ActionID net.graph) : Option $ (net.graph.schemes id.reactor .actions).type id.action :=
  match h : events.findP? (·.id = id) with
  | none => none
  | some event => 
    have h := Array.findP?_property h
    (of_decide_eq_true h) ▸ event.value

-- We can't separate out a `runInst` function at the moment as `IO` isn't universe polymorphic.
partial def run (exec : Executable net) (topo : Array (ReactionID net)) (reactionIdx : Nat) : IO Unit := do
  match topo[reactionIdx]? with 
  | none => 
    match exec.next with
    | some next => run (exec.advance next) topo 0
    | none => return
  | some reactionID =>
    IO.sleepUntil exec.tag.time
    let mut exec := exec
    let reaction := net.reaction reactionID
    if exec.triggers reaction then
      let reactorID := reactionID.reactor
      let ports     := exec.reactionInputs reactorID
      let actions   := exec.reactors reactorID .actions
      let state     := exec.reactors reactorID .state
      let output ← reaction.run ports actions state exec.tag
      exec := exec.apply output
    run exec topo (reactionIdx + 1)

end Executable

end Network
