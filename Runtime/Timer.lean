import Runtime.Time

namespace Timer

/--
The period of a timer can be either absent or a positive duration. Thus, a period can't have a value
of 0. We model the absent case explicitly (instead of implicitly by using the value 0), so that an
absent period can't accidentally be overlooked at the call site.
-/
abbrev Period := Option { dur : Duration // dur ≠ 0 }

/-- Constructs a period from a given duration by mapping a duration of 0 to the absent period. -/
def Period.of (dur : Duration) : Timer.Period :=
  if h : dur = 0 then none else some ⟨dur, h⟩

/--
A timer is a component that can appear in a reactor (cf. `Reactor.timer`). It can be used as a
trigger for reactions (cf. `Reaction.Trigger.timer` & `Execution.Executable.triggers`). During
execution, if the timer has a non-absent period, the firing of a timer produces a new event on the
event queue (cf. `Execution.Event.timer` & `Execution.Executable.Next.nextTimerEvents`).
-/
structure _root_.Timer where
  /-- The `offset` is the logical time at which the timer should fire for the first time. -/
  offset : Time
  /-- A period of `none` means that the timer should only fire once at its `offset`. -/
  period : Timer.Period

/--
The time of the timer's first firing after time 0.

This value is used in the code generator to get the time of the first event that is added to the
event queue for each timer.
-/
def initialFiring (timer : Timer) : Option Time :=
  if timer.offset = 0 then timer.period else timer.offset

end Timer
