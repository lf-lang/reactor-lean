import Runtime.Network.Graph.Basic

namespace Network.Graph

def Class (graph : Graph) := graph.classes

namespace Class

def scheme (cls : Class graph) := graph.schemes cls

def interface (cls : Class graph) := cls.scheme.interface

def child (cls : Class graph) (child : cls.scheme.children) : Class graph := 
  cls.scheme.class child

def subinterface (cls : Class graph) (kind : Reactor.InterfaceKind) :=
  ⨄ fun child => (cls.child child).interface kind

abbrev reactionInputScheme (cls : Class graph) :=
  let localInputs := cls.interface .inputs
  let nestedOutputs := cls.subinterface .outputs
  localInputs ⊎ nestedOutputs

abbrev reactionOutputScheme (cls : Class graph) :=
  let localOutputs := cls.interface .outputs
  let nestedInputs := cls.subinterface .inputs
  localOutputs ⊎ nestedInputs

abbrev reactionType (cls : Class graph) :=
  Reaction 
    cls.reactionInputScheme cls.reactionOutputScheme 
    (cls.interface .actions) (cls.interface .state) (cls.interface .params) 
    cls.scheme.timers

end Class
end Network.Graph