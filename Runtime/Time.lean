import Runtime.Utilities.Lean

inductive Time.Scale
  | ns | μs | ms | s | min | hour | day | week

def Time.Scale.nsRatio : Scale → Nat
  | .ns   => 1
  | .μs   => 1000
  | .ms   => 1000 * 1000
  | .s    => 1000 * 1000 * 1000
  | .min  => 1000 * 1000 * 1000 * 60
  | .hour => 1000 * 1000 * 1000 * 60 * 60
  | .day  => 1000 * 1000 * 1000 * 60 * 60 * 24
  | .week => 1000 * 1000 * 1000 * 60 * 60 * 24 * 7

structure Time where
  private mk :: 
  private ns : Nat
  deriving DecidableEq

instance : ToString Time where
  toString t := s!"{t.ns} ns"

instance : LT Time where
  lt t₁ t₂ := t₁.ns < t₂.ns

instance : LE Time where
  le t₁ t₂ := t₁.ns ≤ t₂.ns

instance : Decidable ((t₁ : Time) < t₂) := by
  simp [LT.lt]; infer_instance

instance : Decidable ((t₁ : Time) ≤ t₂) := by
  simp [LE.le]; infer_instance

abbrev Duration := Time

def Time.of (value : Nat) (scale : Scale) : Time :=
  { ns := value * scale.nsRatio }

def Time.to (time : Time) (scale : Scale) : Nat :=
  time.ns / scale.nsRatio

theorem Time.of_to : (Time.of value scale).to scale = value := by
  simp [of, to, Scale.nsRatio]
  cases scale <;> simp only [Nat.mul_div_same_eq] 

def Time.now : IO Time := 
  return { ns := ← IO.monoNanosNow }

instance : OfNat Time 0 where
  ofNat := { ns := 0 }

theorem Time.zero_eq_zero : (0 : Time) = Time.of 0 scale := by simp [of]

instance : HAdd Time Duration Time where
  hAdd t d := { ns := t.ns + d.ns }

instance : HSub Time Duration Time where
  hSub t d := { ns := t.ns - d.ns }

instance : HSub Time Time Duration where
   hSub t₁ t₂ := { ns := t₁.ns - t₂.ns }

instance : HMod Duration Duration Duration where
   hMod d₁ d₂ := { ns := d₁.ns % d₂.ns }

abbrev Time.From (time : Time) := { t : Time // t ≥ time }

instance : LE (Time.From t) where
  le t₁ t₂ := t₁.val ≤ t₂.val

def Time.advance (time : Time) (d : Duration) : Time.From time := {
  val := time + d
  property := by simp_arith [GE.ge, LE.le, HAdd.hAdd, Add.add]
}

structure Tag where
  time : Time
  microstep : Nat
  deriving DecidableEq

instance : ToString Tag where
  toString tag := s!"⟨{tag.time}, {tag.microstep}⟩"

instance : LT Tag where
  lt tag₁ tag₂ := 
    if tag₁.time = tag₂.time 
    then tag₁.microstep < tag₂.microstep 
    else tag₁.time < tag₂.time 

def Tag.advance (tag : Tag) (time : Time.From tag.time) : Tag := 
  if tag.time < time then { time := time, microstep := 0 }
  else                    { tag with microstep := tag.microstep + 1 }

theorem Tag.lt_advance : tag < (tag : Tag).advance t := by
  simp [advance]
  split
  case inr => simp_arith [LT.lt]
  case inl => simp [LT.lt] at *; split <;> simp_all
    