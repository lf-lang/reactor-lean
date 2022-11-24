import Runtime.Execution.Basic

namespace Execution.Executable
open Network

def nextTime (exec : Executable net) : Option (Time.From exec.time) :=
  match exec.state with
  | .shuttingDown => none
  | .stopRequested => some exec.time
  | .executing => exec.queue.nextTime

theorem nextTime_le_queue_nextTime {exec : Executable net} {t q} :
  (exec.nextTime = some t) → (exec.queue.nextTime = some q) → (t ≤ q) := by
  intro ht hq
  simp [nextTime] at ht
  split at ht <;> simp_all
  simp [←ht]
  exact q.property

private def propagationEvents (exec : Executable net) : Queue (Event net) exec.time where
  elems :=
    exec.toPropagate.uniqueMergeMap (le := (·.time ≤ ·.time)) fun port =>
      match exec.reactors port.reactor |>.interface .outputs port.port with
      | none => #[] -- TODO: This case is unreachable by the semantics of `toPropagate`.
      | some value =>
        let events := port.delayedDestinations.map fun { dst, delay, eqType } =>
          Event.propagation (exec.time + delay) dst (eqType ▸ value)
        events.insertionSort (·.time ≤ ·.time) -- TODO: Use `qsort` when it drops `[Inhabited α]`.
  sorted := sorry
  bounded := sorry

private def nextTimerEvents (exec : Executable net) (timers : Array (TimerId net)) (anchor : Time) :
  Queue (Event net) anchor where
  elems :=
    timers.filterMap fun ⟨reactor, timer⟩ =>
      match exec.reactors reactor |>.timer timer |>.val.period with
      | none => none
      | some period => return .timer (anchor + period) ⟨reactor, timer⟩
  sorted := sorry
  bounded := sorry

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net)
  queue  : Queue (Event net) tag.time

namespace Next

def empty (tag : Tag) : Next net where
  tag := tag
  events := #[]
  queue := °[]

protected def «for» (exec : Executable net) : Option (Next net) :=
  -- TODO: It feels like this doesn't belong here.
  let exec := { exec with queue := exec.queue.merge exec.propagationEvents }
  match h : exec.nextTime with
  | none => none
  | some time =>
    -- TODO: We can't destruct here, as this causes problems in the proof of `bounded` below.
    let eventSplit := exec.queue.split time (fun _ h' => nextTime_le_queue_nextTime h h')
    let events := eventSplit.fst
    let later := eventSplit.snd
    let timers := events.filterMap (·.timer?)
    let timerEvents := exec.nextTimerEvents timers time
    some {
      tag    := exec.tag.advance time
      events := events
      queue  := Tag.advance_time ▸ later.merge timerEvents
    }

theorem for_isSome_if_stopRequested (exec : Executable net) :
  (exec.state = .stopRequested) → (Next.for exec).isSome :=
  sorry

theorem for_preserves_events :
  (Next.for exec = some next) →
  ∃ timerEvents propagationEvents,
    (next.events ++ next.queue.elems) ~ (exec.queue.elems ++ timerEvents ++ propagationEvents) := by
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
