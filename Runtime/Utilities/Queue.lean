import Runtime.Utilities.Extensions

/-- An event type is a type which has an identifier and an associated time stamp. -/
class EventType (α : Type _) where
  Id : Type
  id : α → Id
  time : α → Time
  [decEqId : DecidableEq Id]

attribute [instance] EventType.decEqId

-- TODO: Use `List.Sorted` once it arrives in Mathlib.
inductive Queue.Sorted [inst : EventType ε] : List ε → Prop
  | nil : Sorted []
  | singleton : Sorted [e]
  | cons : (inst.time fst ≤ inst.time snd) → Sorted (snd :: tl) → Sorted (hd :: snd :: tl)

/--
A queue is a sorted list of events where each event has a time stamp greater or equal to a given
lower `bound`.
-/
structure Queue (ε : Type) [inst : EventType ε] (bound : Time) where
  events : Array ε
  sorted : Queue.Sorted events.toList
  bounded : ∀ {event}, (events[0]? = some event) → bound ≤ inst.time event
  -- TODO: Add the property:
  -- ∀ {event₁ event₂}, (event₁ ∈ events) → (event₂ ∈ events) → (time event₁ > bound) →
  --                    (time event₁ ≠ time event₂) ∨ (id event₁ ≠ id event₂)

namespace Queue
open EventType

variable [EventType ε]

@[reducible]
instance : Membership ε (Queue ε bound) where
  mem q e := e ∈ q.events.toList

-- TODO: What's the story for theorems about `Array`s in Lean 4?
theorem all_events_bounded {queue : Queue ε bound} :
  ∀ {event}, event ∈ queue.events.toList → bound ≤ time event := by
  sorry

/-- A queue is empty if its underlying list of events is empty. -/
def isEmpty (q : Queue ε bound) : Bool := q.events.isEmpty

/-- The size of a queue is the number of its events. -/
def size (q : Queue ε bound) : Nat := q.events.size

instance : GetElem (Queue ε bound) Nat { e : ε // bound ≤ time e } (fun q i => i < q.size) where
  getElem queue i _ := {
    val := queue.events[i]
    property := sorry
  }

@[simp]
theorem getElem?_some_events_getElem?_some {queue : Queue ε bound} {i : Nat} :
  (queue[i]? = some event) → (queue.events[i]? = event.val) := by
  intro h
  sorry

@[simp]
theorem getElem?_none_events_getElem?_none {queue : Queue ε bound} {i : Nat} :
  (queue[i]? = none) → (queue.events[i]? = none) := by
  intro h
  sorry

/-- Creates an empty queue. -/
def nil : Queue ε bound where
  events := #[]
  sorted := .nil
  bounded := by simp

notation "°[]" => Queue.nil

instance : Inhabited (Queue ε bound) where
  default := °[]

/-- Creates a queue with a single event. -/
def singleton (event : ε) (h : bound ≤ time event) : Queue ε bound where
  events := #[event]
  sorted := .singleton
  bounded := by intros; simp_all

notation "°[" e "]' " h => Queue.singleton e h

/--
Creates a queue from an array of events by sorting its elements. The time bound fulfilled trivially
by choosing it to be 0.
-/
def sorting (events : Array ε) : Queue ε 0 where
  events := events.insertionSort (time · ≤ time ·)
  sorted := sorry
  bounded := by intros; simp

/--
The "next time" of a queue is the time of its next event (if it exists).

*Note:* The next event is considered to be the one at index 0.
-/
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
  sorry
  /-
  constructor <;> split <;> simp_all [Option.isSome]
  · simp [Queue.getElem?_some_events_getElem?_some ‹_›]
  -/

/--
Splits a queue into a list of "next events" and "remaining events".
* "Next events" are those which have a time stamp matching the `nextTime` and are the first among
  all events with the same id.
* "Remaining events" are those which have a time stamp greater than the `nextTime` or have an event
  in with the same id earlier in the queue.

For example, let's assume each event has the form `(time, id, value)`. Then the queue:
```
(10, a, 0) (10, a, 1) (10, b, 2) (11, a, 3)
```
... would be split into:
* next events `(10, a, 0) (10, b, 2)`, and
* remaining events `(10, a, 1) (11, a, 3)`.
-/
def split
  (queue : Queue ε bound) (anchor : Time) (h : ∀ next, queue.nextTime = some next → anchor ≤ next) :
  Array ε × Queue ε anchor :=
  let ⟨candidates, later⟩ := queue.events.partition (time · = anchor)
  let ⟨next, postponed⟩ := candidates.unique (EventType.id ·)
  {
    fst := next
    snd := {
      events := postponed ++ later
      sorted := sorry
      bounded := sorry
    }
  }

-- *Note*: For adherence to the LF scheduling semantics, this operation overrides events of equal id
--         and time, except those whose time is `bound`.
--
-- *Note:* It is important that this merge is stable. That is, it should be the same as would be
-- produced by a stable sorting algorithm on input `queue₁ ++ queue₂`.
-- TODO: Implement all of this properly once something like `Array.merge` arrives in Std.
def merge [inst : EventType ε] (queue₁ queue₂ : Queue ε bound) : Queue ε bound :=
  if queue₁.isEmpty      then queue₂
  else if queue₂.isEmpty then queue₁
  else
  -- Note, using `split` is inefficient as it traverses the entire array.
  let ⟨immediate₁, future₁⟩ := queue₁.events.partition (time · = bound)
  let ⟨immediate₂, future₂⟩ := queue₂.events.partition (time · = bound)
  {
    events := (mergeImmediate immediate₁ immediate₂) ++ (mergeFuture future₁ future₂)
    sorted := sorry
    bounded := sorry
  }
where
  mergeImmediate (is₁ is₂ : Array ε) : Array ε :=
    (is₁ ++ is₂).insertionSort (time · ≤ time ·)
  mergeFuture (fs₁ fs₂ : Array ε) : Array ε :=
    let fs₁' := fs₁.filter fun event₁ =>
      ¬ fs₂.any fun event₂ =>
        (inst.time event₁ = inst.time event₂) ∧
        (inst.id event₁ = inst.id event₂)
    (fs₁' ++ fs₂).insertionSort (time · ≤ time ·)

theorem merge_mem₂ {queue₁ queue₂ : Queue ε bound} :
  (event ∈ queue₂) → (event ∈ queue₁.merge queue₂) := by
  intro h
  simp [merge]
  split <;> try split
  case isTrue => exact h
  case isFalse.isTrue he =>
    rw [isEmpty, Array.isEmpty_iff_toList_eq_nil] at he
    simp [Membership.mem, he] at h
    contradiction
  case isFalse.isFalse =>
    by_cases time event = bound
    case pos ht =>
      -- `event` is in `immediate₂` and thus retained as part of `mergeImmediate`
      sorry
    case neg ht =>
      -- `event` is in `future₂` and thus retained as part of `mergeFuture`
      sorry

/--
Maps a queue of event type `ε` to a queue of event type `δ`. To ensure that the resulting queue is
still sorted and bounded, the map must preserve time stamps.
-/
def map [EventType δ] (queue : Queue ε bound) (f : ε → δ) (h : ∀ e : ε, time e = time (f e)) :
  Queue δ bound where
  events := queue.events.map f
  sorted := sorry
  bounded := sorry

namespace Queue
