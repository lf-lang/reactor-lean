import Runtime.Reactor

namespace Network

inductive Tree 
  | node (scheme : Reactor.Scheme) (Nested : Type) (nested : Nested → Tree) (decEq : DecidableEq Nested)

abbrev Tree.scheme : Tree → Reactor.Scheme 
  | .node scheme .. => scheme

abbrev Tree.Nested : Tree → Type 
  | .node _ Nested .. => Nested

abbrev Tree.nested : (tree : Tree) → (tree.Nested → Tree)  
  | .node _ _ nested _ => nested

def Tree.decEq : (tree : Tree) → (DecidableEq tree.Nested)  
  | .node _ _ _ decEq => decEq

attribute [instance] Tree.decEq

def Tree.leaf (scheme : Reactor.Scheme) : Tree :=
  .node scheme Empty (·.rec) inferInstance

inductive ReactorID.Nested : Tree → Type _
  | final [decEq : DecidableEq IDs] (id : IDs) (nested : IDs → Tree) : Nested (.node _ IDs nested decEq)
  | cons [decEq : DecidableEq IDs] (head : IDs) (nested : IDs → Tree) : (Nested $ nested head) → (Nested $ .node _ IDs nested decEq)

inductive ReactorID (tree : Tree)
  | main
  | nested : ReactorID.Nested tree → ReactorID tree

abbrev Tree.subtree (tree : Tree) : ReactorID tree → Tree
  | .main => tree
  | .nested n =>
    match n with 
    | ReactorID.Nested.final id nested  => nested id
    | ReactorID.Nested.cons head tail nestedID => subtree (tail head) (.nested nestedID)

notation tree:max "[" id "]" => Tree.subtree tree id

abbrev Tree.reactionType (tree : Tree) : Type _ :=
  Reaction 
    ((tree.scheme .inputs).sum (Interface.Scheme.sum' tree.Nested fun n => (tree.nested n).scheme .outputs))   
    ((tree.scheme .outputs).sum (Interface.Scheme.sum' tree.Nested fun n => (tree.nested n).scheme .inputs))
    (tree.scheme .actions)
    (tree.scheme .state)

structure PortID (kind : Reactor.PortKind) (tree : Tree) where
  reactor : ReactorID tree
  port : (tree[reactor].scheme kind).vars

abbrev Connection (tree : Tree) := (PortID .output tree) × (PortID .input tree)

structure Event (tree : Tree) (min : Time) where
  reactor : ReactorID tree
  «local» : _root_.Event (tree[reactor].scheme .actions) min

instance : Ord (Network.Event tree time) where
  compare e₁ e₂ := compare e₁.local.time e₂.local.time

structure ActionID (tree : Tree) where
  reactor : ReactorID tree
  action : (tree[reactor].scheme .actions).vars

def Event.actionID (event : Event tree time) : ActionID tree := {
  reactor := event.reactor
  action := event.local.action
}

instance : DecidableEq (ActionID tree) := sorry

structure _root_.Network where
  tree : Tree
  reactions : (id : ReactorID tree) → Array $ tree[id].reactionType
  connections : Array (Connection tree)
  reactors :  (id : ReactorID tree) → Reactor $ tree[id].scheme
  tag : Tag
  events : SortedArray (Event tree tag.time) 

structure ReactionID (ν : Network) where
  reactor : ReactorID ν.tree
  reactionIdx : Fin (ν.reactions reactor).size

def reaction (ν : Network) (id : ReactionID ν) : ν.tree[id.reactor].reactionType :=
  (ν.reactions id.reactor)[id.reactionIdx]

structure Next (ν : Network) (min : Time) where
  events : Array (Event ν.tree ν.tag.time)
  remaining : SortedArray (Event ν.tree min)

def nextTag (ν : Network) : Option (Tag.From ν.tag.time) :=
  match ν.events.get? 0 with
  | none => none
  | some nextEvent => ν.tag.advance nextEvent.local.time

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