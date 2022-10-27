import Runtime.Time

namespace Timer

abbrev Period := Option { dur : Duration // dur ≠ 0 }

def Period.of (dur : Duration) : Timer.Period :=
  if h : dur = 0 then none else some ⟨dur, h⟩

-- This is used for `firesAtTag`.
private def Period.duration : Timer.Period → Duration
  | none => 0
  | some dur => dur

structure _root_.Timer where
  offset : Time
  period : Timer.Period -- A duration of 0 means that the timer should only fire once. 

def firesAtTag (timer : Timer) (tag : Tag) : Bool :=
  timer.offset ≤ tag.time ∧ 
  tag.microstep = 0       ∧
  (tag.time - timer.offset) % timer.period.duration = 0 -- TODO: Write this using the Dvd typeclass.

-- The time of the timer's first firing after time 0.
def initalFiring (timer : Timer) : Option Time :=
  if timer.offset = 0 then timer.period else timer.offset
  
