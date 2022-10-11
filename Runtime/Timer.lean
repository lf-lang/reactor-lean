import Runtime.Time

structure Timer where
  offset : Time := 0
  period : Option Duration

def Timer.firesAtTag (timer : Timer) (tag : Tag) : Bool :=
  match tag.microstep, timer.period with
  | 0, none        => tag.time - timer.offset = 0
  | 0, some period => (tag.time - timer.offset) % period = 0
  | _, _           => false
