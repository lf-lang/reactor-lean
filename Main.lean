import Runtime

lf {
  reactor Main
    inputs      [i1 : Nat, i2 : String]
    outputs     [o1 : Bool, o2 : Unit]
    actions     [a1 : String, a2 : Bool × Nat]
    state       [s1 : Int, s2 : Bool]
    nested      [x : Sub, y : Sub]
    connections []
    reactions   [
      {
        portSources   [i1, i2, x.o1]
        portEffects   [o1, x.i2]
        actionSources [a1]
        actionEffects []
        triggers {
          ports   [i1]
          actions [a2]
          meta    [startup, shutdown]
        }
        body {
          sorry
        }
      },
      {
        portSources   [i1]
        portEffects   [o1, o2]
        actionSources [a1, a2]
        actionEffects [a2]
        triggers {
          ports   []
          actions [a2]
          meta    []
        }
        body {
          sorry
        }
      }
    ]

  reactor Sub
    inputs      [i1 : Nat, i2 : Bool, i3 : Unit]
    outputs     [o1 : Unit]
    actions     []
    state       []
    nested      [a : Grand, b : Grand]
    connections []
    reactions   []

  reactor Grand
    inputs      []
    outputs     []
    actions     []
    state       []
    nested      []
    connections []
    reactions   []
}

#print LF.network

/-abbrev network : Network where
  toGraph := graph
  «reactions» 
    | .Main => #[
      {
        «portSources»   := graph.Main.Reaction0.PortSource
        «portEffects»   := graph.Main.Reaction0.PortEffect
        «actionSources» := graph.Main.Reaction0.ActionSource
        «actionEffects» := graph.Main.Reaction0.ActionEffect
        «triggers»      := #[.startup, .shutdown, .port .i2, .action .a1]
        «body» := open graph Main Reaction0 PortSource PortEffect ActionSource ActionEffect State ReactionM in do
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
        «portSources»   := graph.Main.Reaction1.PortSource
        «portEffects»   := graph.Main.Reaction1.PortEffect
        «actionSources» := graph.Main.Reaction1.ActionSource
        «actionEffects» := graph.Main.Reaction1.ActionEffect
        «triggers»      := #[.action .a1, .action .a2]
        «body» := open ReactionM graph Main Reaction1 PortSource PortEffect ActionSource ActionEffect State in do
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
      source := fun 
        | ⟨.y, .i3⟩ => some ⟨.x, .o1⟩
        | _ => none
      eqType := sorry -- TODO: This should be a default parameter.
    }
    | .Sub => .empty
    | .Grand => .empty
-/

def main : IO Unit := do
  let exec : Network.Executable LF.network := {
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
  let topo : Array (Network.ReactionID LF.network) := #[
    ⟨.nil, ⟨0, by simp⟩⟩,
    ⟨.nil, ⟨1, by simp⟩⟩
  ]
  exec.run topo 0