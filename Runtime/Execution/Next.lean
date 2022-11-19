import Runtime.Execution.Basic

namespace Execution.Executable
open Network

def nextTime (exec : Executable net) : Option (Time.From exec.time) :=
  match h : exec.queue[0]? with
  | none => none
  | some nextEvent => some ⟨nextEvent.time, exec.lawfulQueue h⟩

theorem nextTime_isSome_iff_queue_not_isEmpty {exec : Executable net} :
  exec.nextTime.isSome ↔ ¬exec.queue.isEmpty := by
  rw [←Array.getElem?_zero_isSome_iff_not_isEmpty]
  simp [nextTime]
  constructor <;> split <;> simp_all [Option.isSome]

-- The first array are the next events to be executed at `time`.
-- The second array is the remaining queue.
private def eventSplit (exec : Executable net) (time : Time) : Array (Event net) × Array (Event net) :=
  let ⟨candidates, later⟩ := exec.queue.split (·.time = time)
  let ⟨next, postponed⟩ := candidates.unique (·.id)
  (next, postponed ++ later)

theorem eventSplit_fst_LawfulQueue {exec : Executable net} {time} :
  LawfulQueue (exec.eventSplit time).fst time := sorry
  -- TODO: We need theorems about `Array.unique/.split` to prove this.

theorem eventSplit_snd_LawfulQueue {exec : Executable net} {time} :
  LawfulQueue (exec.eventSplit time).snd time := sorry
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

-- UNFINISHED: Add propagation events.
protected def «for» (exec : Executable net) (time : Time.From exec.time) : Next net :=
  let eventSplit := exec.eventSplit time -- TODO: We can't destruct here, as this causes problems in the proof of `lawfulQueue`.
  let events := eventSplit.fst
  let later := eventSplit.snd
  let timers := events.filterMap (·.timer?)
  let timerEvents := exec.nextTimerEvents timers time
  {
    tag         := exec.tag.advance time
    queue       := later.merge timerEvents
    lawfulQueue := (exec.tag.advance_time time) ▸ LawfulQueue.merge eventSplit_snd_LawfulQueue nextTimerEvents_LawfulQueue
    events
  }

/- For the UNFINISHED above:
exec.toPropagate.uniqueMergeMap fun port =>
  match output.raw.ports port with
  | none => #[] -- TODO: This case is unreachable by the semantics of `toPropagate`.
  | some value =>
      parent.class.connections.delayed ⟨leaf, Path.split_class h₁ ▸ port'⟩ |>.map fun ⟨delay, dst⟩ =>
        let input : InputPortId net := {
          reactor := parent.extend dst.child
          port := sorry -- dst.port
        }
        have H : input.reactor.inputs.type input.port = output.reaction.val.portEffects.type port := sorry
        Event.propagation (exec.time + delay) input (H ▸ value)
-/

theorem for_preserves_events {time} : (Next.for exec time = next) → ∃ timerEvents, (next.events ++ next.queue) ~ (exec.queue ++ timerEvents) := by
  intro h
  simp [Next.for] at h
  let events := (exec.eventSplit time).fst
  let timers := events.filterMap (·.timer?)
  exists exec.nextTimerEvents timers time
  sorry

-- The actions-interface for a given reactor according to the `Next` instance.
def actions (next : Next net) (reactor : ReactorId net) : Interface? (reactor.class.interface .actions) :=
  fun action =>
    match h : next.events.findP? (·.id = .action ⟨reactor, action⟩) with
    | none => none
    | some event => have h := Array.findP?_property h; event.actionValue (of_decide_eq_true h)

-- The inputs-interface for a given reactor according to the `Next` instance.
def inputs (next : Next net) (reactor : ReactorId net) : Interface? (reactor.class.interface .inputs) :=
  fun input =>
    match h : next.events.findP? (·.id = .propagation ⟨reactor, input⟩) with
    | none => none
    | some event => have h := Array.findP?_property h; event.propagationValue (of_decide_eq_true h)

def timers (next : Next net) (exec : Executable net) (reactor : ReactorId net) : reactor.class.timers → Reactor.Timer :=
  fun timer => {
    val      := exec.reactors reactor |>.timer timer |>.val
    isFiring := next.events.any (·.timer? = some ⟨reactor, timer⟩)
  }

end Next
end Execution.Executable
