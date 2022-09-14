import Runtime.Network.Basic

namespace Network

structure Event (graph : Graph) where
  time  : Time
  id    : ActionID graph
  value : (graph.schemes id.reactor .actions).type id.action

structure Executable extends Network where
  tag : Tag
  events : /-Sorted-/Array (Event toNetwork.graph) 
  reactors : (id : ReactorID tree) → Reactor (toNetwork.schemes id)

structure Next (net : Network) where
  tag : Tag
  events : Array (Event net.graph)
  remaining : Array (Event net.graph)

def next (exec : Executable) : Option (Next exec.toNetwork) := 
  match exec.events[0]? with
  | none => none
  | some nextEvent => 
    let nextTag := exec.tag.advance nextEvent.time
    let ⟨candidates, later⟩ := exec.events.split (·.time = nextTag.time)  
    let ⟨current, postponed⟩ := candidates.unique (·.id)
    sorry


def nextTag (ν : Network) : Option (Tag.From ν.tag.time) :=
  
def next (ν : Network) (time : Time.From ν.tag.time) : Next ν time :=
  -- TODO: somehow use the fact that the given time is in fact the 
  --       time of the prefix of `ν.events` to show that the times 
  --       of the events in `later` and `postponed` are `≥ time`.
  let ⟨candidates, later⟩ := ν.events.split (·.local.time.val = time)  
  let ⟨current, postponed⟩ := candidates.unique (·.actionID)
  let postponed' : SortedArray _ := ⟨postponed, sorry⟩
  let remaining := postponed'.append later sorry
  {
    events := current,
    remaining := 
      have : Coe (Event ν.tree ν.tag.time) (Event ν.tree time) := sorry -- This is not provable!
      remaining.coe sorry
  }

def triggers {ν : Network} {id : ReactorID ν.tree} (rtr : Reactor (ν.tree[id]).scheme) (rcn : (ν.tree[id]).reactionType) : Bool :=
  rcn.triggers.any fun trigger =>
    match trigger with
    | .port   port   => true -- rtr.inputs.isPresent port
    | .action action => true -- rtr.actions.isPresent action

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