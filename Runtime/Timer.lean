import Runtime.Time

structure Timer where
  offset : Time
  period : Option Duration

def Timer.firesAtTag (timer : Timer) (tag : Tag) : Bool := Id.run do
  unless (timer.offset ≤ tag.time) ∧ (tag.microstep = 0) do return false
  match timer.period with
  | some period => return (tag.time - timer.offset) % period = 0
  | none        => return tag.time = timer.offset

-- The time of the timer's first firing after time 0.
def Timer.initalFiring (timer : Timer) : Option Time :=
  if timer.offset = 0 then timer.period else timer.offset
  
