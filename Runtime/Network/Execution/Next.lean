import Runtime.Network.Execution.Basic

namespace Network.Executable

private def nextTime (exec : Executable net) : Option (Time.From exec.tag.time) :=
  match h : exec.queue[0]? with 
  | none => none
  | some nextEvent => some ⟨nextEvent.time, exec.lawfulQueue h⟩

theorem nextTime_isSome_iff_queue_not_isEmpty {exec : Executable net} : 
  exec.nextTime.isSome ↔ ¬exec.queue.isEmpty := by
  simp [Array.isEmpty, Option.isSome_def, nextTime]
  constructor
  case mp =>
    intro ⟨_, h⟩ hc
    split at h
    · contradiction
    case _ h' => 
      simp [getElem?] at h'
      split at h' 
      case inl h => simp [hc] at h
      case inr => contradiction
  case mpr =>
    intro h
    let fst := exec.queue[0]' (Nat.zero_lt_of_ne_zero h)
    by_cases exec.queue[0]? = some fst
    case inl hc =>
      have hq := exec.lawfulQueue hc
      exists ⟨fst.time, hq⟩
      split 
      · simp_all [hc]
      · simp_all
    case inr hc =>
      simp [getElem?] at hc
      split at hc
      case inl => contradiction
      case inr => simp_all [Nat.zero_lt_of_ne_zero h]

private def nextTag (exec : Executable net) : Option Tag := 
  match exec.nextTime with
  | none => none
  | some time => exec.tag.advance time

theorem nextTag_isSome_iff_nextTime_isSome {exec : Executable net} :
  exec.nextTag.isSome ↔ exec.nextTime.isSome := by
  simp [nextTag]
  split <;> simp [Option.isSome_def]
  · intro ⟨_, _⟩; simp_all
  case _ time _ =>
    simp_all
    constructor <;> intro _
    · exists ‹_›
    · exists exec.tag.advance time

theorem nextTag_isSome_iff_queue_not_isEmpty {exec : Executable net} : 
  exec.nextTag.isSome ↔ ¬exec.queue.isEmpty := by
  simp [nextTag_isSome_iff_nextTime_isSome, nextTime_isSome_iff_queue_not_isEmpty]

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

def Next.for (exec : Executable net) : Option (Next net) := 
  match exec.nextTag with 
  | none => none
  | some tag =>
    let eventSplit := exec.eventSplit tag.time -- We can't directly destruct here, as this causes problems in the proof of `lawfulQueue`.
    let events := eventSplit.fst
    let later := eventSplit.snd
    let timers := events.filterMap (·.timer?)
    let timerEvents := exec.nextTimerEvents timers tag.time
    let queue := later.merge timerEvents
    some { tag, events, queue, lawfulQueue := LawfulQueue.merge eventSplit_snd_LawfulQueue nextTimerEvents_LawfulQueue }

theorem Next.for_isSome_iff_nextTag_isSome {exec : Executable net} :
  (Next.for exec).isSome ↔ ¬exec.queue.isEmpty := by
  simp [Next.for]
  sorry

theorem Next.for_isSome_iff_queue_not_isEmpty {exec : Executable net} :
  (Next.for exec).isSome ↔ ¬exec.queue.isEmpty := by
  sorry

theorem Next.for_preserves_events : ∃ timerEvents, (Next.for exec = some next) → (next.events ++ next.queue) ~ (exec.queue ++ timerEvents) :=
  sorry

-- The actions-interface for a given reactor according to the `Next` instance.
def Next.actions (next : Next net) (reactor : ReactorId net) : Interface? (reactor.class.interface .actions) := 
  fun action => 
    match h : next.events.findP? (·.id = .action ⟨reactor, action⟩) with
    | none => none
    | some event => have h := Array.findP?_property h; event.actionValue (of_decide_eq_true h)

end Network.Executable