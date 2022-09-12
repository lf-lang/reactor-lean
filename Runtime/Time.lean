abbrev Time := Nat
abbrev Duration := Nat
abbrev Time.From (time : Time) := { t : Time // t ≥ time }

instance : Ord (Time.From time) where
  compare t₁ t₂ := compare t₁.val t₂.val

def Time.From.lift (t : Time.From later) (h : later ≥ earlier) : Time.From earlier := {
  val := t
  property := Nat.le_trans h t.property
}

instance {later : Time.From earlier} : Coe (Time.From later) (Time.From earlier) where
  coe t := t.lift later.property

structure Tag where
  time : Time
  microstep : Nat

abbrev Tag.From (time : Time) := { tag : Tag // tag.time ≥ time }

def Tag.From.time {time : Time} (tag : Tag.From time) : Time.From time := { 
  val := tag.val.time
  property := tag.property
}

def Tag.From.lift (t : Tag.From later) (h : later ≥ earlier) : Tag.From earlier := {
  val := t
  property := Nat.le_trans h t.property
}

instance {later : Time.From earlier} : Coe (Tag.From later) (Tag.From earlier) where
  coe t := t.lift later.property

def Time.advance (time : Time) (d : Duration) : Time.From time := {
  val := time + d
  property := by simp_arith
}

def Tag.advance (tag : Tag) (time : Time.From tag.time) : Tag.From time := {
  val := {
    time := time
    microstep := if tag.time = time then tag.microstep + 1 else 0
  }
  property := by simp
}
