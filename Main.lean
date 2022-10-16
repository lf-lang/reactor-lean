import Runtime

-- set_option trace.Elab.command true

lf {
  reactor Main
    parameters  []
    inputs      []
    outputs     [out : Nat]
    actions     []
    state       [count : Nat := 1]
    timers      [
      {
        name   t
        offset 0
        period some (.of 1 .s)
      }
    ]
    nested      [a₁ : A, a₂ : A]
    connections []
    reactions   [
      {
        portSources   []
        portEffects   [out]
        actionSources []
        actionEffects []
        triggers {
          ports   []
          actions []
          timers  [t]
          meta    []
        }
        body {
          let c ← getState count
          setOutput out c
          setState count (c + 1)
          monadLift <| IO.println s!"{c}"
        }
      }
    ]

  reactor A 
    parameters  [p : Nat := 10]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [c : C]
    connections []
    reactions   []

  reactor C 
    parameters  [c₁ : Bool := true, c₂ : Nat := 10]
    inputs      []
    outputs     []
    actions     []
    state       []
    timers      []
    nested      [d : D]
    connections []
    reactions   []
  
  reactor D
  parameters  [d₁ : String := ""]
  inputs      []
  outputs     []
  actions     []
  state       []
  timers      []
  nested      []
  connections []
  reactions   []
}

-- PLAN BEGIN

def LF.Parameters.a₁.p := 0 -- <expr>
def LF.Parameters.a₂.p := 0 -- <expr>

open LF.Parameters.a₁ in
def LF.Parameters.a₁.c.c₁ := 0 -- <expr>

open LF.Parameters.a₂ in
def LF.Parameters.a₂.c.c₁ := 0 -- <expr>

open LF.Parameters.a₁.c in
def LF.Parameters.a₁.c.d.d₁ := 0 -- <expr>

open LF.Parameters.a₂.c in
def LF.Parameters.a₂.c.d.d₁ := 0 -- <expr>

def exe : Network.Executable LF.network where
  physicalOffset := sorry
  queue := sorry
  reactors
    | .nil => open LF.Parameters in {
      interface := fun
        | .state => fun
          | .count => sorry -- expr
        | .params => (nomatch ·)
        | .inputs | .outputs | .actions => Interface?.empty 
      timer := fun id =>
        sorry
    }
    | .cons .a₁ <| .nil => open LF.Parameters.a₁ in {
      interface := fun
        | .state => (nomatch ·)
        | .params => fun 
          | .p => p -- This just captures the value of parameter `p` in an interface.
                    -- The value has already been computed in the definition called `p` (in this namespace).
        | .inputs | .outputs | .actions => Interface?.empty 
      timer := fun id =>
        sorry
    }
    -- NOTE: This definition is exactly the same as for `a₁`, because their from the same class.
    --       The only things that's different is which namespace we've opened.
    --       Thus, in the code generator, have a function that generates a reactor instance `Term` for
    --       each reactor class. You can then use that here.
    | .cons .a₂ <| .nil => open LF.Parameters.a₂ in {
      interface := fun
        | .state => (nomatch ·)
        | .params => fun 
          | .p => p -- This just captures the value of parameter `p` in an interface.
                    -- The value has already been computed in the definition called `p` (in this namespace).
        | .inputs | .outputs | .actions => Interface?.empty 
      timer := fun id =>
        sorry
    }
    | .cons .a₁ <| .cons .c <| .nil => open LF.Parameters.a₁.c in sorry
    | .cons .a₂ <| .cons .c <| .nil => open LF.Parameters.a₂.c in sorry
    | .cons .a₁ <| .cons .c <| .cons .d <| .nil => open LF.Parameters.a₁.c.d in sorry
    | .cons .a₂ <| .cons .c <| .cons .d <| .nil => open LF.Parameters.a₂.c.d in sorry

-- PLAN END



def main : IO Unit := do
  let exec := LF.executable (← Time.now)
  let topo : Array (Network.ReactionID LF.network) := #[⟨.nil, ⟨0, by simp⟩⟩]
  exec.run topo 0
