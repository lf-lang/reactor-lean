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
  deriving Ord, DecidableEq

instance : ToString Time where
  toString t := s!"{t.ns} ns"

instance : LE Time := leOfOrd
instance : LT Time := ltOfOrd

abbrev Duration := Time

def Time.of (value : Nat) (scale : Scale) : Time :=
  { ns := value / scale.nsRatio }

def Time.to (time : Time) (scale : Scale) : Nat :=
  time.ns * scale.nsRatio

def Time.now : IO Time := 
  return { ns := ← IO.monoNanosNow }

instance : OfNat Time 0 where
  ofNat := { ns := 0 }

instance : HAdd Time Duration Time where
  hAdd t d := { ns := t.ns + d.ns }

instance : HSub Time Duration Time where
  hSub t d := { ns := t.ns - d.ns }

instance : HSub Time Time Duration where
   hSub t₁ t₂ := { ns := t₁.ns - t₂.ns }

instance : HMod Duration Duration Duration where
   hMod d₁ d₂ := { ns := d₁.ns % d₂.ns }

abbrev Time.From (time : Time) := { t : Time // t ≥ time }

instance : Ord (Time.From time) where
  compare t₁ t₂ := compare t₁.val t₂.val

def Time.advance (time : Time) (d : Duration) : Time.From time := {
  val := time + d
  property := by 
    simp [HAdd.hAdd, Add.add]
    -- TODO: Unfold ≥
    simp_arith
    sorry
}

structure Tag where
  time : Time
  microstep : Nat
  deriving DecidableEq

instance : ToString Tag where
  toString tag := s!"⟨{tag.time}, {tag.microstep}⟩"

def Tag.advance (tag : Tag) (time : Time) : Tag := 
  match compare tag.time time with
  | .lt => { time := time, microstep := 0 }
  | .eq => { tag with microstep := tag.microstep + 1 }
  | .gt => tag -- TODO: This can only happen if there is an error in the implementation of reactor execution.

