import Runtime.Utilities.Extensions

class EventType (α : Type _) where
  Id : Type
  id : α → Id
  time : α → Time
  [decEqId : DecidableEq Id]

attribute [instance] EventType.decEqId

inductive Queue.Sorted [inst : EventType ε] : List ε → Prop
  | nil : Sorted []
  | singleton : Sorted [e]
  | cons : (inst.time fst ≤ inst.time snd) → Sorted (snd :: tl) → Sorted (hd :: snd :: tl)

structure Queue (ε : Type) [inst : EventType ε] (bound : Time) where
  elems : Array ε
  sorted : Queue.Sorted elems.data
  bounded : ∀ {event}, (elems[0]? = some event) → bound ≤ inst.time event

namespace Queue
open EventType

variable [EventType ε]

-- TODO: What's the story for theorems about `Array`s in Lean 4?

theorem all_elems_bounded {queue : Queue ε bound} :
  ∀ {event}, event ∈ queue.elems.data → bound ≤ time event := by
  sorry

def isEmpty (q : Queue ε bound) : Bool := q.elems.isEmpty

def size (q : Queue ε bound) : Nat := q.elems.size

instance : GetElem (Queue ε bound) Nat { e : ε // bound ≤ time e } (fun q i => i < q.size) where
  getElem queue i _ := {
    val := queue.elems[i]
    property := sorry
  }

@[simp]
theorem getElem?_some_elems_getElem?_some {queue : Queue ε bound} {i : Nat} :
  (queue[i]? = some event) → (queue.elems[i]? = event.val) := by
  intro h
  sorry

@[simp]
theorem getElem?_none_elems_getElem?_none {queue : Queue ε bound} {i : Nat} :
  (queue[i]? = none) → (queue.elems[i]? = none) := by
  intro h
  sorry

def nil : Queue ε bound where
  elems := #[]
  sorted := .nil
  bounded := by simp

notation "°[]" => Queue.nil

instance : Inhabited (Queue ε bound) where
  default := °[]

def singleton (event : ε) (h : bound ≤ time event) : Queue ε bound where
  elems := #[event]
  sorted := .singleton
  bounded := by simp [h]

notation "°[" e "]' " h => Queue.singleton e h

def nextTime (queue : Queue ε bound) : Option (Time.From bound) :=
  match queue[0]? with
  | none => none
  | some nextEvent => some {
      val := time nextEvent.val
      property := by have := nextEvent.property; simp_all [EventType.time]
    }

theorem nextTime_some {queue : Queue ε bound} :
  (queue.nextTime = some next) →
  (∃ event, queue[0]? = some event ∧ (time event.val) ≥ next.val) := by
  intro h
  unfold nextTime at h
  split at h <;> simp at h
  case _ event h' =>
    exists event
    apply And.intro h'
    simp [←h]

theorem nextTime_isSome_iff_not_isEmpty {queue : Queue ε bound} :
  queue.nextTime.isSome ↔ ¬queue.isEmpty := by
  rw [Queue.isEmpty, ←Array.getElem?_zero_isSome_iff_not_isEmpty]
  simp [nextTime]
  constructor <;> split <;> simp_all [Option.isSome]
  · simp [Queue.getElem?_some_elems_getElem?_some ‹_›]

-- The first array are the next events to be executed at `time`.
-- The second array is the remaining queue.
def split
  (queue : Queue ε bound) (anchor : Time) (h : ∀ next, queue.nextTime = some next → anchor ≤ next) :
  Array ε × Queue ε anchor :=
  let ⟨candidates, later⟩ := queue.elems.split (time · = anchor)
  let ⟨next, postponed⟩ := candidates.unique (EventType.id ·)
  {
    fst := next
    snd := {
      elems := postponed ++ later
      sorted := sorry
      bounded := sorry
    }
  }

-- Note: For the purposes of reactor execution, it is important that this merge is stable.
--       That is, it should be the same as would be produced by a stable sorting algorithm on
--       input `q₁ ++ q₂`.
--
-- TODO: Implement this properly.
def merge (queue₁ queue₂ : Queue ε bound) : Queue ε bound :=
  if queue₁.isEmpty      then queue₂
  else if queue₂.isEmpty then queue₁
  else {
    elems := (queue₁.elems ++ queue₂.elems).insertionSort (time · ≤ time ·)
    sorted := sorry
    bounded := sorry
  }

def map [EventType δ] (queue : Queue ε bound) (f : ε → δ) (h : ∀ e : ε, time e = time (f e)) :
  Queue δ bound where
  elems := queue.elems.map f
  sorted := sorry
  bounded := sorry

namespace Queue
