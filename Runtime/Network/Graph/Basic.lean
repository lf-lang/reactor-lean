import Runtime.Reaction
import Runtime.Reactor

structure Network.Graph where
  classes : Type
  schemes : classes → (Reactor.Scheme classes)
  [decEqClasses : DecidableEq classes]

attribute [instance] Network.Graph.decEqClasses

namespace Network.Graph

def Class (graph : Graph) := graph.classes

namespace Class

private def scheme (cls : Class graph) := graph.schemes cls

def interface (cls : Class graph) := cls.scheme.interface

abbrev timers (cls : Class graph) := cls.scheme.timers

structure Child (cls : Class graph) where
  id : cls.scheme.children
  deriving DecidableEq

def Child.class {cls : Class graph} (child : Child cls) : Class graph := 
  cls.scheme.class child.id

abbrev subinterface (cls : Class graph) (kind : Reactor.InterfaceKind) :=
  ⨄ fun child : Child cls => child.class.interface kind

abbrev reactionInputScheme (cls : Class graph) :=
  let localInputs := cls.interface .inputs
  let nestedOutputs := cls.subinterface .outputs
  localInputs ⊎ nestedOutputs

@[simp]
theorem reactionInputScheme_type_left {cls : Class graph} (localInput) : 
  cls.reactionInputScheme.type (.inl localInput) = (cls.interface .inputs).type localInput := rfl 

@[simp]
theorem reactionInputScheme_type_right {cls : Class graph} (child childOutput) : 
  cls.reactionInputScheme.type (.inr ⟨child, childOutput⟩) = (child.class.interface .outputs).type childOutput := by
  simp [Interface.Scheme.bUnion_type]  

abbrev reactionOutputScheme (cls : Class graph) :=
  let localOutputs := cls.interface .outputs
  let nestedInputs := cls.subinterface .inputs
  localOutputs ⊎ nestedInputs

abbrev reactionType (cls : Class graph) :=
  Reaction 
    cls.reactionInputScheme cls.reactionOutputScheme 
    (cls.interface .actions) (cls.interface .state) (cls.interface .params) 
    cls.scheme.timers

structure Subport (cls : Class graph) (kind : Reactor.PortKind) where
  child : Child cls
  port : (child.class.interface kind).vars

abbrev Subport.type (subport : Subport cls kind) : Type := 
  (subport.child.class.interface kind).type subport.port

-- TODO: The `eqTypeProof` is probably broken.
macro "eqTypeProof" : tactic => `(intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp)
structure Connections (cls : Class graph) where 
  source : (Subport cls .input) → Option (Subport cls .output)
  eqType : (source input = some output) → (input.type = output.type) := by eqTypeProof

def Connections.empty : Connections cls where
  source _ := none
  eqType := by simp

end Class

end Network.Graph