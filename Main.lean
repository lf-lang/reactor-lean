import Runtime

/-
network {

  main reactor Main {
    input  := [i1 : Nat,    i2 : String]
    output := [o1 : Bool,   o2 : Unit]
    action := [a1 : String, a2 : Bool × Nat]
    state  := [s1 : Int,    s2 : Bool]
    nested := [x : Sub, y : Sub]
    connections := [x.o1 → y.i3]

    reaction first (i1, !i2, !@a1, x.o1) → (o1, x.i2) { 
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

  reactor Sub {
    input  := [i1 : Nat, i2 : Bool, i3 : Unit]
    output := [o1 : Unit]
    action := []
    state  := []
    nested := [a : Grand, b : Grand]
    connections := []
  }

  reactor Grand {
    input  := []
    output := []
    action := []
    state  := []
    nested := []
    connections := []
  }
}
-/

inductive Classes 
  | Main
  | Sub
  | Grand

inductive Main.Input  | i1 | i2 deriving DecidableEq
inductive Main.Output | o1 | o2 deriving DecidableEq
inductive Main.Action | a1 | a2 deriving DecidableEq
inductive Main.State  | s1 | s2 deriving DecidableEq
inductive Main.Nested | x  | y  deriving DecidableEq

inductive Main.Reaction1.PortSource   | i1 | i2 | x.o1 deriving DecidableEq
inductive Main.Reaction1.PortEffect   | o1 | x.i2 deriving DecidableEq
inductive Main.Reaction1.ActionSource | a1 deriving DecidableEq
inductive Main.Reaction1.ActionEffect deriving DecidableEq

inductive Main.Reaction2.PortSource   | i1 deriving DecidableEq
inductive Main.Reaction2.PortEffect   | o1 | o2 deriving DecidableEq
inductive Main.Reaction2.ActionSource | a1 | a2 deriving DecidableEq
inductive Main.Reaction2.ActionEffect | a2 deriving DecidableEq

abbrev Main.scheme : Reactor.Scheme Classes := {
  interface := fun
    | .inputs => { 
      vars := Input
      type := fun
        | .i1 => Nat
        | .i2 => String
    }
    | .outputs => {
      vars := Output
      type := fun
        | .o1 => Bool
        | .o2 => Unit
    }
    | .actions => {
      vars := Action
      type := fun
        | .a1 => String
        | .a2 => Bool × Nat
    }
    | .state => {
      vars := State
      type := fun
        | .s1 => Int
        | .s2 => Bool
    }
  children := Main.Nested
  «class» := fun 
    | .x => .Sub
    | .y => .Sub
}

inductive Sub.Input  | i1 | i2 | i3 deriving DecidableEq
inductive Sub.Output | o1 deriving DecidableEq
inductive Sub.Action deriving DecidableEq
inductive Sub.State  deriving DecidableEq
inductive Sub.Nested | a | b deriving DecidableEq

abbrev Sub.scheme : Reactor.Scheme Classes := {
  interface := fun
    | .inputs => { 
      vars := Input
      type := fun
        | .i1 => Nat
        | .i2 => Bool
        | .i3 => Unit
    }
    | .outputs => {
      vars := Output
      type := fun
        | .o1 => Unit
    }
    | .actions => {
      vars := Action
      type := (·.casesOn)
    }
    | .state => {
      vars := State
      type := (·.casesOn)
    }
  children := Sub.Nested
  «class» := fun
    | .a => .Grand
    | .b => .Grand
}

inductive Grand.Input  deriving DecidableEq
inductive Grand.Output deriving DecidableEq
inductive Grand.Action deriving DecidableEq
inductive Grand.State  deriving DecidableEq
inductive Grand.Nested deriving DecidableEq

abbrev Grand.scheme : Reactor.Scheme Classes := {
  interface := fun
    | .inputs => { 
      vars := Input
      type := (·.casesOn)
    }
    | .outputs => {
      vars := Output
      type := (·.casesOn)
    }
    | .actions => {
      vars := Action
      type := (·.casesOn)
    }
    | .state => {
      vars := State
      type := (·.casesOn)
    }
  children := Empty
  «class» := (·.casesOn)
}

abbrev graph : Network.Graph := {
  classes := Classes
  root := .Main
  schemes := fun
    | .Main => Main.scheme
    | .Sub => Sub.scheme
    | .Grand => Grand.scheme
}

@[reducible]
instance : InjectiveCoe Main.Reaction1.PortSource (graph.reactionInputScheme .Main).vars where
  coe
    | .i1   => .inl .i1
    | .i2   => .inl .i2
    | .x.o1 => .inr ⟨.x, .o1⟩
  inv
    | .inl .i1       => some .i1  
    | .inl .i2       => some .i2  
    | .inr ⟨.x, .o1⟩ => some .x.o1
    | _              => none
  invInj := by intro b₁ b₂; cases b₁ <;> cases b₂; repeat rename_i v₁ v₂; cases v₁ <;> cases v₂ <;> simp
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction1.PortEffect (graph.reactionOutputScheme .Main).vars where
  coe
    | .o1   => .inl .o1
    | .x.i2 => .inr ⟨.x, .i2⟩
  inv 
    | .inl .o1       => some .o1
    | .inr ⟨.x, .i2⟩ => some .x.i2
    | _              => none
  invInj := by 
    sorry
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction1.ActionSource (graph.schemes .Main |>.interface .actions |>.vars) where
  coe
    | .a1 => .a1
  inv
    | .a1 => some .a1
    | _   => none
  invInj := sorry
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction1.ActionEffect (graph.schemes .Main |>.interface .actions |>.vars) where
  coe := (·.casesOn)
  inv 
    | _ => none
  invInj := sorry
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction2.PortSource (graph.reactionInputScheme .Main).vars where
  coe
    | .i1 => .inl .i1
  inv
    | .inl .i1 => some .i1
    | _        => none
  invInj := sorry
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction2.PortEffect (graph.reactionOutputScheme .Main).vars where
  coe
    | .o1 => .inl .o1
    | .o2 => .inl .o2
  inv
    | .inl .o1 => some .o1
    | .inl .o2 => some .o2
    | _        => none
  invInj := sorry
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction2.ActionSource (graph.schemes .Main |>.interface .actions |>.vars) where
  coe
    | .a1 => .a1
    | .a2 => .a2
  inv
    | .a1 => some .a1
    | .a2 => some .a2
  invInj := sorry
  coeInvId := (by cases · <;> rfl)

@[reducible]
instance : InjectiveCoe Main.Reaction2.ActionEffect (graph.schemes .Main |>.interface .actions |>.vars) where
  coe
    | .a2 => .a2
  inv
    | .a2 => some .a2
    | _   => none
  invInj := sorry
  coeInvId := (by cases · <;> rfl)

abbrev network : Network := {
  toGraph := graph
  reactions := fun
    | .Main => #[
      {
        portSources   := Main.Reaction1.PortSource
        portEffects   := Main.Reaction1.PortEffect
        actionSources := Main.Reaction1.ActionSource
        actionEffects := Main.Reaction1.ActionEffect
        triggers      := #[.port .i2, .action .a1]
        body := open ReactionM Main Reaction1 PortSource PortEffect ActionSource ActionEffect State in do
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
        portSources   := Main.Reaction2.PortSource
        portEffects   := Main.Reaction2.PortEffect
        actionSources := Main.Reaction2.ActionSource
        actionEffects := Main.Reaction2.ActionEffect
        triggers      := #[.action .a1, .action .a2]
        body := open ReactionM Main Reaction2 PortSource PortEffect ActionSource ActionEffect State in do
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
  connections := fun
    | .Main => {
      source := fun input => -- TODO: Try to get pattern matching working for this.
        if input = ⟨.y, .i3⟩ then some ⟨.x, .o1⟩
        else none
      eqType := by intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp
    }
    | .Sub => .empty
    | .Grand => .empty
}

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
  let debug : Network.Executable.DebugParameters network := {
    callback := fun e => do
      IO.println s!"time: {e.tag.time}\tmicro: {e.tag.microstep}"
      IO.println s!"queue: {e.queue.map (·.time)}"
      let x : Option Nat          := e.reactors .nil .inputs .i1; IO.println  s!"i1: {x}"
      let x : Option String       := e.reactors .nil .inputs .i2; IO.println  s!"i2: {x}"
      let x : Option Bool         := e.reactors .nil .outputs .o1; IO.println s!"o1: {x}"
      let x : Option Unit         := e.reactors .nil .outputs .o2; IO.println s!"o2: {x}"
      let x : Option String       := e.reactors .nil .actions .a1; IO.println s!"a1: {x}"
      let x : Option (Bool × Nat) := e.reactors .nil .actions .a2; IO.println s!"a2: {x}"
      let x : Option Int          := e.reactors .nil .state .s1; IO.println   s!"s1: {x}"
      let x : Option Bool         := e.reactors .nil .state .s2; IO.println   s!"s2: {x}"
      IO.println "---------------------------"
    maxSteps := 10 
  }
  exec.run topo 0 debug
