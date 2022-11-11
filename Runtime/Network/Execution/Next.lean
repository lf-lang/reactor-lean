import Runtime.Network.Execution.Basic

namespace Network.Executable    

private def nextTime (exec : Executable net) : Option (Time.From exec.tag.time) :=
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

theorem eventSplit_fst_LawfulQueue {exec : Executable net} : 
  LawfulQueue (exec.eventSplit time).fst time := sorry
  -- TODO: We need theorems about `Array.unique/.split` to prove this.

theorem eventSplit_snd_LawfulQueue {exec : Executable net} : 
  LawfulQueue (exec.eventSplit time).snd time := sorry
  -- TODO: We need theorems about `Array.unique/.split` to prove this.

private def nextTimerEvents (exec : Executable net) (timers : Array (TimerId net)) (anchor : Time) : Array (Event net) :=
  timers.filterMap fun ⟨reactor, timer⟩ =>
    match exec.reactors reactor |>.timer timer |>.period with
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

protected def Next.for (exec : Executable net) : Option (Next net) := 
  match exec.nextTime with 
  | none => none
  | some time =>
    let tag := exec.tag.advance time
    let eventSplit := exec.eventSplit time -- TODO: We can't destruct here, as this causes problems in the proof of `lawfulQueue`.
    let events := eventSplit.fst
    let later := eventSplit.snd
    let timers := events.filterMap (·.timer?)
    let timerEvents := exec.nextTimerEvents timers time
    let queue := later.merge timerEvents
    some { tag, events, queue, lawfulQueue := (exec.tag.advance_time time) ▸ LawfulQueue.merge eventSplit_snd_LawfulQueue nextTimerEvents_LawfulQueue }

theorem Next.for_isSome_iff_nextTime_isSome {exec : Executable net} :
  (Next.for exec).isSome ↔ exec.nextTime.isSome := by
  simp [Next.for]
  constructor <;> split <;> simp_all [Option.isSome]
    
theorem Next.for_isSome_iff_queue_not_isEmpty {exec : Executable net} :
  (Next.for exec).isSome ↔ ¬exec.queue.isEmpty := by
  simp [for_isSome_iff_nextTime_isSome, nextTime_isSome_iff_queue_not_isEmpty]

theorem Next.for_preserves_events : (Next.for exec = some next) → ∃ timerEvents, (next.events ++ next.queue) ~ (exec.queue ++ timerEvents) := by
  intro h
  simp [Next.for] at h
  split at h
  · contradiction
  case _ time _ =>
    simp at h
    let events := (exec.eventSplit time).fst
    let timers := events.filterMap (·.timer?)
    exists exec.nextTimerEvents timers time
    sorry 

-- The actions-interface for a given reactor according to the `Next` instance.
def Next.actions (next : Next net) (reactor : ReactorId net) : Interface? (reactor.class.interface .actions) := 
  fun action => 
    match h : next.events.findP? (·.id = .action ⟨reactor, action⟩) with
    | none => none
    | some event => have h := Array.findP?_property h; event.actionValue (of_decide_eq_true h)

end Network.Executable