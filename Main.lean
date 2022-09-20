import Runtime

/-
network {

  main reactor Main {
    input  := [i1 : Nat,    i2 : String]
    output := [o1 : Bool,   o2 : Unit]
    action := [a1 : String, a2 : Bool × Nat]
    state  := [s1 : Int,    s2 : Bool]
    nested := [x : Sub, y : Sub]
    connections := [x.o1 → y.i3, o1 → x.i2]

    reaction (i1, !i2, @a1, x.o1) → (o1, x.i2) { 
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

    reaction (i1, !@a1) → (o1, @a2) { 
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
    
    reaction (!i1) → (o1) { 
      let _ ← getInput i1
    }
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

inductive Main.Input  | i1 | i2 deriving DecidableEq
inductive Main.Output | o1 | o2 deriving DecidableEq
inductive Main.Action | a1 | a2 deriving DecidableEq
inductive Main.State  | s1 | s2 deriving DecidableEq
inductive Main.Nested | x  | y  deriving DecidableEq

inductive Main.Reaction1.PortSource   | i1 | i2 | x.o1 deriving DecidableEq
inductive Main.Reaction1.PortEffect   | o1 | x.i2 deriving DecidableEq
inductive Main.Reaction1.ActionSource | a1 deriving DecidableEq
-- inductive Main.Reaction1.ActionEffect deriving DecidableEq 

inductive Main.Reaction2.PortSource   | i1 deriving DecidableEq
inductive Main.Reaction2.PortEffect   | o1 | o2 deriving DecidableEq
inductive Main.Reaction2.ActionSource | a1 deriving DecidableEq
inductive Main.Reaction2.ActionEffect | a2 deriving DecidableEq

def Main.scheme : Reactor.Scheme
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

def Main.reactions 
  [InjectiveCoe Reaction1.PortSource σInput.vars]
  [InjectiveCoe Reaction1.PortEffect σOutput.vars]
  [InjectiveCoe Reaction1.ActionSource σAction.vars]
  [InjectiveCoe Empty σAction.vars] -- [InjectiveCoe Reaction1.ActionEffect σAction.vars]
  [InjectiveCoe Reaction2.PortSource σInput.vars]
  [InjectiveCoe Reaction2.PortEffect σOutput.vars]
  [InjectiveCoe Reaction2.ActionSource σAction.vars]
  [InjectiveCoe Reaction2.ActionEffect σAction.vars] : 
  Array (Reaction σInput σOutput σAction σState) := #[
  {
    portSources   := Reaction1.PortSource
    portEffects   := Reaction1.PortEffect
    actionSources := Reaction1.ActionSource
    actionEffects := Empty -- Reaction1.ActionEffect
    triggers      := #[.port .i2]
    body          := open ReactionM Reaction1.PortSource Reaction1.PortEffect Reaction1.ActionSource in do
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
  },
  {
    portSources   := Reaction2.PortSource
    portEffects   := Reaction2.PortEffect
    actionSources := Reaction2.ActionSource
    actionEffects := Reaction2.ActionEffect
    triggers      := #[.action .a1]
    body          := sorry
  }
]

inductive Sub.Input  | i1 | i2 | i3 deriving DecidableEq
inductive Sub.Output | o1 deriving DecidableEq
inductive Sub.Action deriving DecidableEq
inductive Sub.State  deriving DecidableEq
inductive Sub.Nested | a | b deriving DecidableEq

inductive Sub.Reaction1.PortSource   | i1 deriving DecidableEq
inductive Sub.Reaction1.PortEffect   | o1 deriving DecidableEq
-- inductive Sub.Reaction1.ActionSource deriving DecidableEq
-- inductive Sub.Reaction1.ActionEffect deriving DecidableEq

def Sub.scheme : Reactor.Scheme
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
    type := (·.rec)
  }
  | .state => {
    vars := State
    type := (·.rec)
  }

def Sub.reactions 
  [InjectiveCoe Reaction1.PortSource σInput.vars]
  [InjectiveCoe Reaction1.PortEffect σOutput.vars] 
  [InjectiveCoe Empty σAction.vars] -- [InjectiveCoe Reaction1.ActionSource σAction.vars]
  [InjectiveCoe Empty σAction.vars] : -- [InjectiveCoe Reaction1.ActionEffect σAction.vars]   
  Array (Reaction σInput σOutput σAction σState) := #[
  {
    portSources   := Reaction1.PortSource
    portEffects   := Reaction1.PortEffect
    actionSources := Empty -- Reaction1.ActionSource
    actionEffects := Empty -- Reaction1.ActionEffect
    triggers      := #[.port .i1]
    body          := sorry
  }
]

inductive Grand.Input  deriving DecidableEq
inductive Grand.Output deriving DecidableEq
inductive Grand.Action deriving DecidableEq
inductive Grand.State  deriving DecidableEq
inductive Grand.Nested deriving DecidableEq

def Grand.scheme : Reactor.Scheme
  | .inputs => { 
    vars := Input
    type := (·.rec)
  }
  | .outputs => {
    vars := Output
    type := (·.rec)
  }
  | .actions => {
    vars := Action
    type := (·.rec)
  }
  | .state => {
    vars := State
    type := (·.rec)
  }

def Grand.reactions : Array (Reaction σInput σOutput σAction σState) := #[
]  

abbrev Grand.tree : Tree :=
  .node Empty (·.rec) --! Empty, not Nested

abbrev Sub.tree : Tree :=
  .node Nested fun
    | .a => Grand.tree
    | .b => Grand.tree

abbrev Main.tree : Tree :=
  .node Nested fun
    | .x => Sub.tree
    | .y => Sub.tree

abbrev Grand.subschemes : (Tree.Path Grand.tree) → Reactor.Scheme 
  | .last empty   => empty.rec
  | .cons empty _ => empty.rec

abbrev Sub.subschemes : (Tree.Path Sub.tree) → Reactor.Scheme
  | .last .a    => Grand.scheme
  | .last .b    => Grand.scheme
  | .cons .a id => Grand.subschemes id
  | .cons .b id => Grand.subschemes id

abbrev Main.subschemes : (Tree.Path Main.tree) → Reactor.Scheme
  | .last .x    => Sub.scheme
  | .last .y    => Sub.scheme
  | .cons .x id => Sub.subschemes id
  | .cons .y id => Sub.subschemes id

abbrev graph : Network.Graph := {
  tree := Main.tree
  schemes := fun
    | .branch id => Main.subschemes id
    | .root => Main.scheme
}

instance : InjectiveCoe Main.Reaction1.PortSource (graph.reactionInputScheme .root).vars where 
  coe := fun
    | .i1   => .inl .i1
    | .i2   => .inl .i2
    | .x.o1 => .inr ⟨.x, .o1⟩
  inv := fun
    | .inl .i1       => some .i1  
    | .inl .i2       => some .i2  
    | .inr ⟨.x, .o1⟩ => some .x.o1
    | _              => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Main.Reaction1.PortEffect (graph.reactionOutputScheme .root).vars where 
  coe := fun
    | .o1   => .inl .o1
    | .x.i2 => .inr ⟨.x, .i2⟩
  inv := fun
    | .inl .o1       => some .o1  
    | .inr ⟨.x, .i2⟩ => some .x.i2
    | _              => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Main.Reaction1.ActionSource (Main.scheme .actions).vars where 
  coe := fun
   | .a1 => .a1
  inv := fun
   | .a1 => some .a1  
   | _ => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Empty (Main.scheme .actions).vars where 
  coe := Empty.rec
  inv := fun _ => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Main.Reaction2.PortSource (graph.reactionInputScheme .root).vars where 
  coe := fun
    | .i1 => .inl .i1
  inv := fun
    | .inl .i1 => some .i1  
    | _        => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Main.Reaction2.PortEffect (graph.reactionOutputScheme .root).vars where
  coe := fun
    | .o1 => .inl .o1
    | .o2 => .inl .o2
  inv := fun
    | .inl .o1 => some .o1  
    | .inl .o2 => some .o2  
    | _        => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Main.Reaction2.ActionSource (Main.scheme .actions).vars where 
  coe := fun
    | .a1 => .a1
  inv := fun
    | .a1 => some .a1  
    | _ => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Main.Reaction2.ActionEffect (Main.scheme .actions).vars where 
  coe := fun
    | .a2 => .a2
  inv := fun
    | .a2 => some .a2  
    | _ => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Sub.Reaction1.PortSource (graph.reactionInputScheme $ .branch $ .last .x).vars where 
  coe := fun
    | .i1 => .inl .i1
  inv := fun
    | .inl .i1 => some .i1  
    | _        => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Sub.Reaction1.PortEffect (graph.reactionOutputScheme $ .branch $ .last .x).vars where 
  coe := fun
    | .o1 => .inl .o1
  inv := fun
    | .inl .o1 => some .o1  
    | _        => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Empty (Sub.scheme .actions).vars where 
  coe := Empty.rec
  inv := fun _ => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Empty (Sub.scheme .actions).vars where 
  coe := Empty.rec
  inv := fun _ => none
  invInj := sorry
  coeInvId := sorry


instance : InjectiveCoe Sub.Reaction1.PortSource (graph.reactionInputScheme $ .branch $ .last .y).vars where 
  coe := fun
    | .i1 => .inl .i1
  inv := fun
    | .inl .i1 => some .i1  
    | _        => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Sub.Reaction1.PortEffect (graph.reactionOutputScheme $ .branch $ .last .y).vars where 
  coe := fun
    | .o1 => .inl .o1
  inv := fun
    | .inl .o1 => some .o1  
    | _        => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Empty (Sub.scheme .actions).vars where 
  coe := Empty.rec
  inv := fun _ => none
  invInj := sorry
  coeInvId := sorry

instance : InjectiveCoe Empty (Sub.scheme .actions).vars where 
  coe := Empty.rec
  inv := fun _ => none
  invInj := sorry
  coeInvId := sorry

def network : Network := {
  toGraph := graph
  reactions := fun
    | .root => Main.reactions
    | .branch $ .last .x => Sub.reactions
    | .branch $ .last .y => Sub.reactions
    | .branch $ .cons .x $ .last .a => Grand.reactions
    | .branch $ .cons .x $ .last .b => Grand.reactions
    | .branch $ .cons .y $ .last .a => Grand.reactions
    | .branch $ .cons .y $ .last .b => Grand.reactions
  connections := {
    map := fun port => 
      -- TODO: This is probably a bug similar to https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pattern.20matching.20limitations.3F 
      -- set_option pp.all true in
      -- match port with
      -- | ⟨.branch (.last .y), .i3⟩ => some ⟨.branch (.last .x), .o1⟩
      -- | ⟨.branch (.last .x), .i2⟩ => some ⟨.root, .o1⟩
      -- | _ => none
      --
      -- Workaround:
      if      port = ⟨.branch (.last .y), .i3⟩ then some ⟨.branch (.last .x), .o1⟩
      else if port = ⟨.branch (.last .x), .i2⟩ then some ⟨.root, .o1⟩
      else                                          none
    eqType := sorry
  }
}

def exec : Network.Executable network := {
  tag := ⟨0, 0⟩
  queue := #[]
  reactors := fun _ _ => Interface.empty
}

def main : IO Unit := do
  exec.run #[] 0