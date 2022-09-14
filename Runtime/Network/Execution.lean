import Runtime.Network.Basic

namespace Network

structure Event (graph : Graph) where
  time  : Time
  id    : ActionID graph
  value : (graph.schemes id.reactor .actions).type id.action

structure Executable extends Network where
  tag : Tag
  queue : /-Sorted-/Array (Event toNetwork.graph) 
  reactors : (id : ReactorID tree) → Reactor (toNetwork.schemes id)

abbrev Executable.network (exec : Executable) := exec.toNetwork

def Executable.reactionInputs (exec : Executable) (reactorID : ReactorID exec.tree) : Interface (exec.graph.reactionInputScheme reactorID) 
  | .inl localInput => (exec.reactors reactorID) .inputs localInput
  | .inr ⟨subreactor, nestedOutput⟩ => exec.reactors (reactorID.extend subreactor) .outputs nestedOutput

def Executable.reactionOutputs (exec : Executable) (reactorID : ReactorID exec.tree) : Interface (exec.graph.reactionOutputScheme reactorID) 
  | .inl localOutput => (exec.reactors reactorID) .outputs localOutput
  | .inr ⟨subreactor, nestedInput⟩ => exec.reactors (reactorID.extend subreactor) .inputs nestedInput

def triggers (exec : Executable) (reactionID : ReactionID exec.network) : Bool :=
  let reaction := exec.network.reaction reactionID
  reaction.triggers.any fun trigger =>
    match trigger with
    | .port   port   => (exec.reactionInputs reactionID.reactor).isPresent port
    | .action action => (exec.reactors reactionID.reactor .actions).isPresent action

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net.graph)
  queue  : Array (Event net.graph)

def next (exec : Executable) : Option (Next exec.toNetwork) := do
  let nextEvent ← exec.queue[0]?
  let nextTag := exec.tag.advance nextEvent.time
  let ⟨candidates, later⟩ := exec.queue.split (·.time = nextTag.time)  
  let ⟨current, postponed⟩ := candidates.unique (·.id)
  return {
    tag := nextTag
    events := current
    queue := postponed ++ later
  }




  

-- Note: Running a reactor at a time isnt possible. Eg:
--       rcn1 -> subreactor.input -> subreaction -> subreactor.output -> rcn2
def instantaneousRun (ν : Network) (topo : Array (ReactionID ν)) : Network := Id.run do
  for reactionID in topo do
    let reaction := ν.reaction reactionID
    let reactor := ν.reactors reactionID.reactor
    if triggers reactor reaction then
      sorry
    else
      sorry
  sorry

def actionMapForEvents {ν : Network} (events : Array $ Event ν.tree ν.tag.time) : 
  (id : ActionID ν.tree) → Option (((ν.tree[id.reactor]).scheme .actions).type id.action) := 
  fun id => 
    match h : events.findP? (·.actionID = id) with
    | none => none
    | some event =>
      have h₁ : id.reactor = event.reactor := by have h' := Array.findP?_property h; simp at h'; rw [←h']; rfl
      have h₂ : HEq id.action event.local.action := by have h' := Array.findP?_property h; simp at h'; rw [←h']; simp; rfl
      -- (eq_of_heq h₂) ▸ h₁ ▸ event.local.value
      sorry

partial def run (ν : Network) : Network :=
  let topo : Array (ReactionID ν) := sorry
  let ν' := ν.instantaneousRun topo
  match ν'.nextTag with
  | none => ν'
  | some nextTag => 
    let next := ν'.next nextTag.time
    let actionMap := actionMapForEvents next.events 
    run { ν' with
      reactors := fun id => fun
        | .inputs =>  Interface.empty
        | .outputs => Interface.empty
        | .actions => (actionMap ⟨id, ·⟩)
        | .state =>   (ν'.reactors id) .state
      tag := nextTag
      events := next.remaining
    }  

end Network