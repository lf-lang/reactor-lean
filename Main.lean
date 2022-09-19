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

    reaction first (i1, !i2, @a1, x.o1) → (o1, x.i2) { 
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

    reaction second (i1, !@a1) → (o1, @a2) { 
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

inductive Sub.Input  | i1 | i2 | i3 deriving DecidableEq
inductive Sub.Output | o1 deriving DecidableEq
inductive Sub.Action deriving DecidableEq
inductive Sub.State  deriving DecidableEq
inductive Sub.Nested | a | b deriving DecidableEq

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

def Grand.subschemes : (Tree.Path Grand.tree) → Reactor.Scheme 
  | .last empty   => empty.rec
  | .cons empty _ => empty.rec

def Sub.subschemes : (Tree.Path Sub.tree) → Reactor.Scheme
  | .last .a    => Grand.scheme
  | .last .b    => Grand.scheme
  | .cons .a id => Grand.subschemes id
  | .cons .b id => Grand.subschemes id

def Main.subschemes : (Tree.Path Main.tree) → Reactor.Scheme
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

instance : InjectiveCoe Main.Reaction1.PortSource (graph.reactionInputScheme .root).vars := {
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
}

instance : InjectiveCoe Main.Reaction1.PortEffect (graph.reactionOutputScheme .root).vars := {
  coe := fun
    | .o1   => .inl .o1
    | .x.i2 => .inr ⟨.x, .i2⟩
  inv := fun
    | .inl .o1       => some .o1
    | .inr ⟨.x, .i2⟩ => some .x.i2 
    | _              => none
  invInj := sorry
  coeInvId := sorry
}
  
def Main.reactions : Array (graph.reactionType .root) := #[
  {
    portSources   := Main.Reaction1.PortSource
    portEffects   := Main.Reaction1.PortEffect
    actionSources := Main.Reaction1.ActionSource
    actionEffects := Main.Reaction1.ActionEffect
    triggers      := #[.port .i2]
    body          := sorry
  },
  {
    portSources   := Main.Reaction2.PortSource
    portEffects   := Main.Reaction2.PortEffect
    actionSources := Main.Reaction2.ActionSource
    actionEffects := Main.Reaction2.ActionEffect
    triggers      := #[.action .a1]
    body          := sorry
  }
]

/-
def Sub.subreactions : (id : Tree.Path Sub.tree) → Array (graph.reactionType (.branch id))
  | .last .a    => sorry -- Grand.reactions
  | .last .b    => sorry -- Grand.reactions
  | .cons .a id => sorry -- Grand.subreactions id
  | .cons .b id => sorry -- Grand.subreactions id

def Main.subreactions : (id : Tree.Path Main.tree) → Array (graph.reactionType (.branch id))
  | .last .x    => Sub.reactions
  | .last .y    => Sub.reactions
  | .cons .x id => Sub.subreactions id
  | .cons .y id => Sub.subreactions id
-/

def network : Network := {
  toGraph := graph
  reactions := fun
    | .root => #[] -- Main.reactions
    | .branch id => #[] -- Main.subreactions id
  connections := {
    map := 
      -- TODO: This is probably a bug similar to https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Pattern.20matching.20limitations.3F 
      -- set_option pp.all true in
      -- fun
      -- | ⟨.branch (.last .y), .i3⟩ => some ⟨.branch (.last .x), .o1⟩
      -- | ⟨.branch (.last .x), .i2⟩ => some ⟨.root, .o1⟩
      -- | _ => none
      --
      -- Workaround:
      fun port => 
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