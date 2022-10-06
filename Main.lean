import Runtime

/-
network {
  main reactor Main {
    connections := [x.o1 → y.i3]

    reaction first (startup, i1, !i2, !@a1, x.o1) → (o1, x.i2) { 
      let i ← getInput i1
      let i' := (i.getD 0) + 1
      let b := if i' = 0 then true else false
      setOutput o1 b
      setOutput o1 true
      setState s1 (-1 : Int)
      match ← getState s1 with
      | none => return
      | some v => 
        setState s1 (v * 12)
        setState s2 false
    }

    reaction second (i1, !@a1, !@a2) → (o1, @a2) { 
      let _ := (← getAction a1).map (· ++ "suffix")
      let _ ← getInput i1
      schedule a2 112 "First"
      schedule a2 113 "Second"
      IO.println "Hello"
      let dir := IO.appDir
      let dir' ← IO.appDir
    }
  }
}
-/

gen_graph graph where
  Main where
    inputs  := [i1 : Nat, i2 : String]
    outputs := [o1 : Bool, o2 : Unit]
    actions := [a1 : String, a2 : Bool × Nat]
    state   := [s1 : Int, s2 : Bool]
    nested  := [x : Sub, y : Sub]
  Sub where
    inputs  := [i1 : Nat, i2 : Bool, i3 : Unit]
    outputs := [o1 : Unit]
    actions := []
    state   := []
    nested  := [a : Grand, b : Grand]
  Grand where
    inputs  := []
    outputs := []
    actions := []
    state   := []
    nested  := []

inductive graph.Main.Reaction1.PortSource   | i1 | i2 | x.o1 deriving DecidableEq
inductive graph.Main.Reaction1.PortEffect   | o1 | x.i2 deriving DecidableEq
inductive graph.Main.Reaction1.ActionSource | a1 deriving DecidableEq
inductive graph.Main.Reaction1.ActionEffect deriving DecidableEq

inductive graph.Main.Reaction2.PortSource   | i1 deriving DecidableEq
inductive graph.Main.Reaction2.PortEffect   | o1 | o2 deriving DecidableEq
inductive graph.Main.Reaction2.ActionSource | a1 | a2 deriving DecidableEq
inductive graph.Main.Reaction2.ActionEffect | a2 deriving DecidableEq

@[reducible]
instance : InjectiveCoe graph.Main.Reaction1.PortSource (graph.reactionInputScheme .Main).vars where
  coe
    | .i1   => .inl .i1
    | .i2   => .inl .i2
    | .x.o1 => .inr ⟨.x, .o1⟩
  inv
    | .inl .i1       => some .i1  
    | .inl .i2       => some .i2  
    | .inr ⟨.x, .o1⟩ => some .x.o1
    | _              => none

@[reducible]
instance : InjectiveCoe graph.Main.Reaction1.PortEffect (graph.reactionOutputScheme .Main).vars where
  coe
    | .o1   => .inl .o1
    | .x.i2 => .inr ⟨.x, .i2⟩
  inv 
    | .inl .o1       => some .o1
    | .inr ⟨.x, .i2⟩ => some .x.i2
    | _              => none

@[reducible]
instance : InjectiveCoe graph.Main.Reaction1.ActionSource (graph.schemes .Main |>.interface .actions |>.vars) where
  coe
    | .a1 => .a1
  inv
    | .a1 => some .a1
    | _   => none

@[reducible]
instance : InjectiveCoe graph.Main.Reaction1.ActionEffect (graph.schemes .Main |>.interface .actions |>.vars) where
  coe := (·.casesOn)
  inv _ := none

@[reducible]
instance : InjectiveCoe graph.Main.Reaction2.PortSource (graph.reactionInputScheme .Main).vars where
  coe
    | .i1 => .inl .i1
  inv
    | .inl .i1 => some .i1
    | _        => none

@[reducible]
instance : InjectiveCoe graph.Main.Reaction2.PortEffect (graph.reactionOutputScheme .Main).vars where
  coe
    | .o1 => .inl .o1
    | .o2 => .inl .o2
  inv
    | .inl .o1 => some .o1
    | .inl .o2 => some .o2
    | _        => none

@[reducible]
instance : InjectiveCoe graph.Main.Reaction2.ActionSource (graph.schemes .Main |>.interface .actions |>.vars) where
  coe
    | .a1 => .a1
    | .a2 => .a2
  inv
    | .a1 => some .a1
    | .a2 => some .a2

@[reducible]
instance : InjectiveCoe graph.Main.Reaction2.ActionEffect (graph.schemes .Main |>.interface .actions |>.vars) where
  coe
    | .a2 => .a2
  inv
    | .a2 => some .a2
    | _   => none

abbrev network : Network where
  toGraph := graph
  reactions 
    | .Main => #[
      {
        portSources   := graph.Main.Reaction1.PortSource
        portEffects   := graph.Main.Reaction1.PortEffect
        actionSources := graph.Main.Reaction1.ActionSource
        actionEffects := graph.Main.Reaction1.ActionEffect
        triggers      := #[.startup, .shutdown, .port .i2, .action .a1]
        body := open ReactionM graph Main Reaction1 PortSource PortEffect ActionSource ActionEffect State in do
          let i ← getInput i1
          let i' := (i.getD 0) + 1 
          let b := if i' = 0 then true else false
          setOutput o1 b
          setOutput o1 true
          setState s1 (-1 : Int)
          match ← getState s1 with
          | none => return
          | some v => 
            setState s1 (v * 12)
            setState s2 false
          monadLift <| IO.println s!"{← getInput i1}"
          monadLift <| IO.println s!"{← getInput i2}"
          monadLift <| IO.println s!"{← getState s1}"
          monadLift <| IO.println s!"{← getState s2}"
          monadLift <| IO.println s!"{← getAction a1}"
      },
      {
        portSources   := graph.Main.Reaction2.PortSource
        portEffects   := graph.Main.Reaction2.PortEffect
        actionSources := graph.Main.Reaction2.ActionSource
        actionEffects := graph.Main.Reaction2.ActionEffect
        triggers      := #[.action .a1, .action .a2]
        body := open ReactionM graph Main Reaction2 PortSource PortEffect ActionSource ActionEffect State in do
          let a ← getAction a1
          -- let _ := a.map (· ++ "suffix") -- TODO: Why doesn't this work?
          let _ ← getInput i1
          let s ← getState s2
          if s.getD false
          then 
            schedule a2 0 (true, 1)
            setState s2 false
          else 
            schedule a2 0 (false, 0)
            setState s2 true
          monadLift (IO.println "Hello")
          monadLift (IO.println "World")
          let dir ← monadLift IO.appDir
          monadLift (IO.println dir)
      }
    ]
    | .Sub => #[]
    | .Grand => #[]
  connections 
    | .Main => {
      source := fun input => -- TODO: Try to get pattern matching working for this.
        if input = ⟨.y, .i3⟩ then some ⟨.x, .o1⟩
        else none
      eqType := by intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp
    }
    | .Sub => .empty
    | .Grand => .empty

def main : IO Unit := do
  let exec : Network.Executable network := {
    tag := ⟨0, 0⟩
    queue := #[]
    reactors := fun id interface =>
      match id, interface with
      | .nil, .inputs  => fun
        | .i1 => some (1 : Nat)
        | .i2 => some ""
      | .nil, .state   => fun
        | .s1 => some (-1 : Int)
        | _ => none
      | .nil, .actions => fun
        | .a1 => some ""
        | _ => none
      | .nil, .outputs => Interface.empty
      | _, _ => Interface.empty
  }
  let topo : Array (Network.ReactionID network) := #[
    ⟨.nil, ⟨0, by simp⟩⟩,
    ⟨.nil, ⟨1, by simp⟩⟩
  ]
  exec.run topo 0