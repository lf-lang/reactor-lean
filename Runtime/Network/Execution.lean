import Runtime.Network.Basic

namespace Network

structure Event (net : Network) where
  time  : Time
  id    : ActionID net
  value : (net.scheme id.reactor).interface .actions |>.type id.action

instance {graph} : Ord (Event graph) where
  compare e₁ e₂ := compare e₁.time e₂.time

structure Executable (net : Network) where
  tag : Tag
  queue : Array (Event net) 
  reactors : (id : ReactorID net) → (kind : Reactor.InterfaceKind) → Interface (net.scheme id |>.interface kind)

namespace Executable

-- An interface for all ports (local and nested) that can act as inputs of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactorID : ReactorID net) : Interface (net.reactionInputScheme' reactorID) 
  | .inl localInput => (exec.reactors reactorID) .inputs localInput
  | .inr ⟨child, nestedOutput⟩ => 
    have h₁ : ((net.schemes ((net.schemes (net.class reactorID)).class child)).interface .outputs).vars = ((net.scheme (reactorID.extend child)).interface .outputs).vars := sorry
    have h₂ : ((net.scheme (reactorID.extend child)).interface .outputs).type (h₁ ▸ nestedOutput) = (net.reactionInputScheme' reactorID).type (.inr ⟨child, nestedOutput⟩) := sorry
    h₂ ▸ (exec.reactors $ reactorID.extend child) .outputs (h₁ ▸ nestedOutput)

def triggers (exec : Executable net) {reactorID : ReactorID net} (reaction : net.reactionType' reactorID) : Bool :=
  reaction.triggers.any fun trigger =>
    match trigger with
    | .port   port   => (exec.reactionInputs reactorID).isPresent port
    | .action action => (exec.reactors reactorID .actions).isPresent action

/-
def apply (exec : Executable net) {reactorID : ReactorID net} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) : Executable net := { exec with
  queue := exec.queue.merge $ output.events.map fun event => {
    time := event.time
    id := ⟨reactorID, scheme_def ▸ event.action⟩
    value := event.value
  }
  reactors := fun id =>
    -- 1. Updates the output ports of the reaction's reactor.
    -- 2. Updates the input ports of nested reactors.
    -- 3. Propagates the reaction's reactor's updated output ports.
    -- 4. Unaffected reactors.
    if      h : id = reactorID         then targetReactor exec (reaction := h ▸ reaction) (h ▸ output)
    else if h : id.isChildOf reactorID then nestedReactor exec output id h
    else if id.isSiblingOf reactorID   then siblingReactor exec output id
    else                                    exec.reactors id 
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
  nestedReactor (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) (id : ReactorID net.tree) (hc : id.isChildOf reactorID) : Reactor (net.graph.schemes id) :=
    let currentReactor := exec.reactors id
    fun
    | .inputs => 
      fun var =>
        let nestedID := id.last hc
        have h₁ : (net.schemes id .inputs).vars = (net.subschemes reactorID nestedID .inputs).vars := by rw [Graph.child_schemes_eq_parent_subschemes]
        let var₁ : (net.reactionOutputScheme reactorID).vars := .inr ⟨nestedID, h₁ ▸ var⟩
        match h : InjectiveCoe.inv var₁ with 
        | none => currentReactor .inputs var
        | some var₂ =>
          match output.ports var₂ with
          | none => currentReactor .inputs var
          | some val =>
            have h : (net.schemes id .inputs).type var = ((net.reactionOutputScheme reactorID).restrict reaction.portEffects).type var₂ := by
              rw [(net.reactionOutputScheme reactorID).restrict_preserves_type, InjectiveCoe.invCoeId _ h]
              simp
              have := Graph.child_schemes_eq_parent_subschemes hc
              sorry
            h ▸ val
    | interface => currentReactor interface 
  siblingReactor (exec : Executable net) {reactorID : ReactorID net.tree} {reaction : net.reactionType reactorID} (output : reaction.outputType exec.tag.time) (id : ReactorID net.tree) : Reactor (net.graph.schemes id) :=
    let currentReactor := exec.reactors id
    fun
    | .inputs => 
      fun var => 
        match hc : net.connections ⟨id, var⟩ with
        | none => currentReactor .inputs var
        | some source =>
          if h : source.reactor = reactorID then
            match hi : InjectiveCoe.inv (Sum.inl (h ▸ source.port)) with 
            | none => currentReactor .inputs var
            | some var' => 
              match output.ports var' with
              | none => currentReactor .inputs var
              | some val =>
                have h : (net.schemes id .inputs).type var = ((net.reactionOutputScheme reactorID).restrict reaction.portEffects).type var' := by
                  rw [(net.reactionOutputScheme reactorID).restrict_preserves_type, InjectiveCoe.invCoeId _ hi, ←net.connections.eqType hc]
                  subst h; rfl
                h ▸ val
          else
            currentReactor .inputs var
    | interface => currentReactor interface 
-/

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net)
  queue  : Array (Event net)

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
where actionForEvents (events : Array <| Event net) (id : ActionID net) : Option <| net.scheme id.reactor |>.interface .actions |>.type id.action :=
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
      -- exec := exec.apply output
    run exec topo (reactionIdx + 1)

end Executable

end Network
