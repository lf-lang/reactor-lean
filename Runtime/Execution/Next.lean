import Runtime.Execution.Basic

namespace Execution.Executable
open Network

def nextTime (exec : Executable net) : Option (Time.From exec.time) :=
  match h : exec.queue[0]? with
  | none => none
  | some nextEvent => some ⟨nextEvent.time, exec.lawfulQueue h⟩

theorem nextTime_some {exec : Executable net} {time} :
  (exec.nextTime = some time) → (∃ event, exec.queue[0]? = some event ∧ event.time ≥ time.val) := by
  intro h
  unfold nextTime at h
  split at h <;> simp at h
  case _ event h' =>
    exists event
    apply And.intro h'
    simp [←h]

theorem nextTime_isSome_iff_queue_not_isEmpty {exec : Executable net} :
  exec.nextTime.isSome ↔ ¬exec.queue.isEmpty := by
  rw [←Array.getElem?_zero_isSome_iff_not_isEmpty]
  simp [nextTime]
  constructor <;> split <;> simp_all [Option.isSome]

private def propagationEvents (exec : Executable net) :=
  exec.toPropagate.uniqueMergeMap fun port =>
    match exec.reactors port.reactor |>.interface .outputs port.port with
    | none => #[] -- TODO: This case is unreachable by the semantics of `toPropagate`.
    | some value =>
      let events := port.delayedDestinations.map fun { dst, delay, eqType } =>
        Event.propagation (exec.time + delay) dst (eqType ▸ value)
      events.insertionSort (·.time ≤ ·.time) -- TODO: Use `qsort` when it drops `[Inhabited α]`.

private theorem propagationEvents_LawfulQueue {exec : Executable net} {time} :
  (LawfulQueue exec.propagationEvents time) := sorry
  -- TODO: We need theorems about `Array.uniqueMergeMap/.map` to prove this.

-- The first array are the next events to be executed at `time`.
-- The second array is the remaining queue.
private def eventSplit (queue : Array (Event net)) (time : Time) : Array (Event net) × Array (Event net) :=
  let ⟨candidates, later⟩ := queue.split (·.time = time)
  let ⟨next, postponed⟩ := candidates.unique (·.id)
  (next, postponed ++ later)

private theorem eventSplit_fst_LawfulQueue {queue : Array (Event net)} {time} :
  (LawfulQueue queue time) →
  (LawfulQueue (eventSplit queue time).fst time) := sorry
  -- TODO: We need theorems about `Array.unique/.split` to prove this.

private theorem eventSplit_snd_LawfulQueue {queue : Array (Event net)} {time} :
  (LawfulQueue queue time) →
  (LawfulQueue (eventSplit queue time).snd time) := sorry
  -- TODO: We need theorems about `Array.unique/.split` to prove this.

private def nextTimerEvents (exec : Executable net) (timers : Array (TimerId net)) (anchor : Time) : Array (Event net) :=
  timers.filterMap fun ⟨reactor, timer⟩ =>
    match exec.reactors reactor |>.timer timer |>.val.period with
    | none => none
    | some period => return .timer (anchor + period) ⟨reactor, timer⟩

theorem nextTimerEvents_LawfulQueue {exec : Executable net} :
  LawfulQueue (exec.nextTimerEvents timers anchor) anchor := sorry
  -- TODO: We need theorems about `Array.filterMap` to prove this.

structure Next (net : Network) where
  tag         : Tag
  events      : Array (Event net)
  queue       : Array (Event net)
  lawfulQueue : LawfulQueue queue tag.time

namespace Next

def empty (tag : Tag) : Next net where
  tag := tag
  events := #[]
  queue := #[]
  lawfulQueue := LawfulQueue.empty

protected def «for» (exec : Executable net) {time} (h : exec.nextTime = some time) : Next net :=
  -- TODO: We can't destruct here, as this causes problems in the proof of `lawfulQueue`.
  let eventSplit := eventSplit (exec.queue.merge exec.propagationEvents) time
  let events := eventSplit.fst
  let later := eventSplit.snd
  let timers := events.filterMap (·.timer?)
  let timerEvents := exec.nextTimerEvents timers time
  {
    tag         := exec.tag.advance time
    events      := events
    queue       := later.merge timerEvents
    lawfulQueue := by
      rw [exec.tag.advance_time time]
      refine LawfulQueue.merge ?_ nextTimerEvents_LawfulQueue
      refine eventSplit_snd_LawfulQueue (LawfulQueue.merge ?_ propagationEvents_LawfulQueue)
      have ⟨e, he, h'⟩ := nextTime_some h
      intro event he'
      simp [he] at he'
      simp [←he', h']
  }

theorem for_preserves_events :
  (Next.for exec h = next) →
  ∃ timerEvents propagationEvents,
    (next.events ++ next.queue) ~ (exec.queue ++ timerEvents ++ propagationEvents) := by
  sorry

-- The actions-interface for a given reactor according to the `Next` instance.
def actions (next : Next net) (reactor : ReactorId net) :
  Interface? (reactor.class.interface .actions) :=
  fun action =>
    match h : next.events.findP? (·.id = .action ⟨reactor, action⟩) with
    | none       => none
    | some event => have h := Array.findP?_property h; event.actionValue (of_decide_eq_true h)

-- The inputs-interface for a given reactor according to the `Next` instance.
def inputs (next : Next net) (reactor : ReactorId net) :
  Interface? (reactor.class.interface .inputs) :=
  fun input =>
    match h : next.events.findP? (·.id = .propagation ⟨reactor, input⟩) with
    | none => none
    | some event => have h := Array.findP?_property h; event.propagationValue (of_decide_eq_true h)

def timers (next : Next net) (exec : Executable net) (reactor : ReactorId net) :
  reactor.class.timers → Reactor.Timer :=
  fun timer => {
    val      := exec.reactors reactor |>.timer timer |>.val
    isFiring := next.events.any (·.timer? = some ⟨reactor, timer⟩)
  }

end Next
end Execution.Executable
