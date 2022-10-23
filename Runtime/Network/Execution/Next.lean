import Runtime.Network.Execution.Basic

namespace Network.Executable

private def nextTime (exec : Executable net) : Option (Time.From exec.tag.time) :=
  match h : exec.queue[0]? with 
  | none => none
  | some nextEvent => some ⟨nextEvent.time, exec.lawfulQueue h⟩

private def nextTag (exec : Executable net) : Option Tag := 
  match exec.nextTime with
  | none => none
  | some time => exec.tag.advance time

-- The first array are the next events to be executed at `time`.
-- The second array is the remaining queue. 
private def eventSplit (exec : Executable net) (time : Time) : Array (Event net) × Array (Event net) := 
  let ⟨candidates, later⟩ := exec.queue.split (·.time = time)  
  let ⟨next, postponed⟩ := candidates.unique (·.id)
  (next, postponed ++ later)

private def nextTimerEvents (exec : Executable net) (timers : Array (TimerId net)) (anchor : Time) : Array (Event net) :=
  timers.filterMap fun ⟨reactor, timer⟩ =>
    match exec.reactors reactor |>.timer timer |>.period with
    | none => none
    | some period => return .timer (anchor + period) ⟨reactor, timer⟩

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net)
  queue  : Array (Event net)

def Next.for (exec : Executable net) : Option (Next net) := 
  match exec.nextTag with 
  | none => none
  | some tag =>
    let ⟨events, later⟩ := exec.eventSplit tag.time
    let timers := events.filterMap (·.timer?)
    let timerEvents := exec.nextTimerEvents timers tag.time
    let queue := later.merge timerEvents
    some { tag, events, queue }

theorem Next.lawfulQueue (next : Next net) : LawfulQueue next.queue next.tag.time := sorry

-- The actions-interface for a given reactor according to the `Next` instance.
def Next.actions (next : Next net) (reactor : ReactorId net) : Interface? (reactor.class.interface .actions) := 
  fun action => 
    match h : next.events.findP? (·.id = .action ⟨reactor, action⟩) with
    | none => none
    | some event => 
      have h := Array.findP?_property h
      event.actionValue (of_decide_eq_true h)

end Network.Executable