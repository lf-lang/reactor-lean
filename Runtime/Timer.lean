import Runtime.Time

structure Timer where
  offset : Time
  period : Option Duration

def Timer.firesAtTag (timer : Timer) (tag : Tag) : Bool :=
  if (timer.offset ≤ tag.time) ∧ (tag.microstep = 0) then 
    match timer.period with
    | some period => (tag.time - timer.offset) % period = 0
    | none        => tag.time = timer.offset
  else 
    false

