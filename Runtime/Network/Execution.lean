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
      targetReactor exec (reaction := h ▸ reaction) (h ▸ output)
    else if h : id.isChildOf reactorID then 
      nestedReactor exec output id h
    else
      exec.reactors id
}
where 
  targetReactor (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) : Reactor (net.graph.schemes reactorID) :=
    fun
    | .state => output.state
    | .outputs => 
      -- TODO: This should be achievable with `Interface.merge'`.
      let i₁ : Interface (net.schemes reactorID .outputs) := exec.reactors reactorID .outputs
      let i₂ : Interface ((net.reactionOutputScheme reactorID).restrict reaction.portEffects) := output.ports
      -- have h₁ : net.reactionOutputScheme reactorID = net.schemes reactorID .outputs := sorry
      -- have h₂ : InjectiveCoe reaction.portEffects (net.schemes reactorID .outputs).vars := sorry
      -- let a := @Interface.merge' (net.schemes reactorID .outputs) reaction.portEffects inferInstance h₂ i₁ i₂
      fun var =>
        let var := var
        let fallback := i₁ var
        sorry
      -- fun var => do
      -- let var : (net.reactionOutputScheme reactorID).vars := .inl (h ▸ var)
      -- let var' : reaction.portEffects ← InjectiveCoe.inv var
      -- let value ← output.ports var'
      -- have h := Interface.Scheme.restrict_preserves_type (net.graph.reactionOutputScheme reactorID) reaction.portEffects var'
      -- have h' := InjectiveCoe.coeInvId var
      -- sorry
    | other => exec.reactors reactorID other
  nestedReactor (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) (id : ReactorID net.tree) (h : id.isChildOf reactorID) : Reactor (net.graph.schemes id) :=
    fun
    | .inputs => sorry -- nested inputs
    | other => exec.reactors id other

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
partial def run (exec : Executable net) (topo : Array (ReactionID net)) : IO Unit := do
  let mut exec := exec
  for reactionID in topo do
    let reaction := net.reaction reactionID
    unless exec.triggers reaction do continue
    let reactorID := reactionID.reactor
    let ports     := exec.reactionInputs reactorID
    let actions   := exec.reactors reactorID .actions
    let state     := exec.reactors reactorID .state
    let ⟨output, _⟩ ← reaction.run ports actions state exec.tag
    sorry -- exec := exec.apply output
    -- TODO: You're not propagating ports at the moment.
  match exec.next with
  | some next => run (exec.advance next) topo
  | none => return

end Executable

end Network