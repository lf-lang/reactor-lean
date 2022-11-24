import Runtime.Execution.Basic

namespace Execution.Executable
open Network

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

-- BUG: It's not sufficient for `time = exec.queue.nextTime`.
--      The `propagationEvents` aren't accounted for in this version of "next time" yet.
protected def «for» (exec : Executable net) {time} (h : exec.queue.nextTime = some time) : Next net :=
  -- TODO: We can't destruct here, as this causes problems in the proof of `bounded` below.
  let eventSplit := (exec.queue.merge exec.propagationEvents).split time <| by
    intro next h
  let events := eventSplit.fst
  let later := eventSplit.snd
  let timers := events.filterMap (·.timer?)
  let timerEvents := exec.nextTimerEvents timers time
  {
    tag    := exec.tag.advance time
    events := events
    queue  := {
      elems := later.merge timerEvents
      sorted := sorry
      bounded := by
        rw [exec.tag.advance_time time]
        refine LawfulQueue.merge ?_ nextTimerEvents_LawfulQueue
        refine eventSplit_snd_LawfulQueue (LawfulQueue.merge ?_ propagationEvents_LawfulQueue)
        have ⟨e, he, h'⟩ := nextTime_some h
        intro event he'
        simp [he] at he'
        simp [←he', h']
      }
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
