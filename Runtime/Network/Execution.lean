import Runtime.Network.Basic

namespace Network

namespace Event

structure ActionEvent (net : Network) where
  time  : Time
  id    : ActionId net
  value : (id.reactor.class.interface .actions).type id.action
  
structure TimerEvent (net : Network) where
  time : Time
  id   : TimerId net

inductive _root_.Network.Event (net : Network)
  | action : ActionEvent net → Event net
  | timer  : TimerEvent  net → Event net

def time : Event net → Time
  | .action { time := time, .. } => time
  | .timer  { time := time, .. } => time

instance : LE (Event net) where
  le e₁ e₂ := e₁.time ≤ e₂.time

instance : Decidable ((e₁ : Event net) ≤ e₂) := by
  simp [LE.le]; infer_instance

inductive ID (net : Network)
  | action : ActionId net → ID net
  | timer  : TimerId net → ID net
  deriving DecidableEq

def id : Event net → Event.ID net
  | .action { id := id, .. } => .action id
  | .timer  { id := id, .. } => .timer id

def action? : Event net → Option (ActionEvent net)
  | .action event => event
  | .timer  _     => none

def timer? : Event net → Option (TimerEvent net)
  | .timer  event => event
  | .action _     => none

def action' {id} : (event : Event net) → (h : event.id = .action id) → ActionEvent net
  | .action ae, _ => ae
  | .timer _,   h => by simp [Event.id] at h

end Event

structure Reactor (cls : Graph.Class graph) where
  interface : (kind : Reactor.InterfaceKind) → kind.interfaceType (cls.interface kind)
  timer : cls.timers → Timer

structure Executable (net : Network) where
  tag : Tag := ⟨0, 0⟩ -- TODO: Define the current time as a computed property of the queue? Only have the microstep explicitly.
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

def timer (exec : Executable net) (id : TimerId net) : Timer :=
  exec.reactors id.reactor |>.timer id.timer

-- An interface for all ports (local and nested) that can act as inputs of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactorId : ReactorId net) : Interface? reactorId.class.reactionInputScheme
  | .inl localInput => exec.reactors reactorId |>.interface .inputs localInput
  | .inr ⟨child, nestedOutput⟩ => 
    -- have h : ((net.scheme (reactorId.extend child)).interface .outputs).type (Graph.Path.extend_scheme ▸ nestedOutput) = (net.reactionInputScheme' reactorID).type (.inr ⟨child, nestedOutput⟩) := sorry
    -- h ▸ (exec.reactors <| reactorID.extend child).interface .outputs (Graph.Path.extend_scheme ▸ nestedOutput)
    sorry

def triggers (exec : Executable net) {reactorId : ReactorId net} (reaction : reactorId.class.reactionType) : Bool :=
  reaction.triggers.any fun trigger =>
    match trigger with
    | .port   port   => exec.reactionInputs reactorId |>.isPresent port
    | .action action => exec.reactors reactorId |>.interface .actions |>.isPresent action
    | .timer  timer  => exec.reactors reactorId |>.timer timer |>.firesAtTag exec.tag
    | .startup       => exec.isStartingUp
    | .shutdown      => exec.isShuttingDown

def apply (exec : Executable net) {reactorId : ReactorId net} {reaction : reactorId.class.reactionType} (output : reaction.outputType exec.tag.time) : Executable net := { exec with
  queue := exec.queue.merge <| output.events.map fun event => .action {
    time := event.time
    id := ⟨reactorId, event.action⟩
    value := event.value
  }
  reactors := fun id => { exec.reactors id with
    interface := 
      -- 1. Updates the output ports of the reaction's reactor.
      -- 2. Updates the input ports of nested reactors.
      -- 3. Unaffected reactors.
      if      h : id = reactorId then targetReactor exec (reaction := h ▸ reaction) (h ▸ output)
      else if h : id ≻ reactorId then nestedReactor exec output id h
      else                            exec.reactors id |>.interface 
  }
  lawfulQueue := sorry
}
where 
  targetReactor (exec : Executable net) {reactorId : ReactorId net} {reaction : reactorId.class.reactionType} (output : reaction.outputType exec.tag.time) : (kind : Reactor.InterfaceKind) → kind.interfaceType (reactorId.class.interface kind)
    | .outputs => localOutputs exec output
    | .state => output.state
    | interface => exec.reactors reactorId |>.interface interface
  nestedReactor (exec : Executable net) {reactorId : ReactorId net} {reaction : reactorId.class.reactionType} (output : reaction.outputType exec.tag.time) (id : ReactorId net) (hc : id ≻ reactorId) : (kind : Reactor.InterfaceKind) → kind.interfaceType (id.class.interface kind)
    | .inputs => nestedInputs exec output id hc
    | interface => exec.reactors id |>.interface interface 
  localOutputs (exec : Executable net) {reactorId : ReactorId net} {reaction : reactorId.class.reactionType} (output : reaction.outputType exec.tag.time) : Interface? (reactorId.class.interface .outputs) :=
    let currentReactor := exec.reactors reactorId
    fun var =>
      match h : InjectiveCoe.inv (Sum.inl var) with 
      | none => currentReactor.interface .outputs var
      | some var' =>
        match output.ports var' with
        | none => currentReactor.interface .outputs var
        | some val =>
          have h : ((net.reactionOutputScheme (net.class reactorId)).restrict reaction.portEffects).type var' = ((net.scheme reactorID).interface .outputs).type var := by
            rw [(net.reactionOutputScheme' reactorId).restrict_type, InjectiveCoe.invCoeId _ h]
          h ▸ val
  nestedInputs (exec : Executable net) {reactorID : ReactorId net} {reaction : reactorId.class.reactionType} (output : reaction.outputType exec.tag.time) (id : ReactorId net) (hc : id ≻ reactorId) : Interface? (id.class.interface .inputs) :=
    let currentReactor := exec.reactors id
    fun var =>
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

def propagate (exec : Executable net) (reactorID : ReactorId net)  : Executable net := { exec with
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
      match event.timer? with 
      | none => none
      | some timerEvent =>
        match exec.timer timerEvent.id |>.period with
        | none => none
        | some p => return .timer { id := timerEvent.id, time := nextTime + p }

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
