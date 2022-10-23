import Runtime.Network.Execution.Basic

namespace Network.Executable

structure Next (net : Network) where
  tag    : Tag
  events : Array (Event net)
  queue  : Array (Event net)

def Next.for (exec : Executable net) : Option (Next net) := 
  match h : exec.queue[0]? with 
  | none => none
  | some nextEvent =>
    let nextTag := exec.tag.advance ⟨nextEvent.time, exec.lawfulQueue h⟩
    let ⟨candidates, later⟩ := exec.queue.split (·.time = nextTag.time)  
    let ⟨next, postponed⟩ := candidates.unique (·.id)
    some {
      tag := nextTag
      events := next
      queue := (postponed ++ later).merge (newTimerEvents exec nextTag.time next)
    }
where 
  -- This function assumes that each timer event in `next` fires at `exec.tag.time`.
  newTimerEvents (exec : Executable net) (nextTime : Time) (next : Array (Event net)) : Array (Event net) := 
    next.filterMap fun event =>
      match event with 
      | .action .. => none
      | .timer _ id =>
        match exec.reactors id.reactor |>.timer id.timer |>.period with
        | none => none
        | some p => return .timer (nextTime + p) id

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