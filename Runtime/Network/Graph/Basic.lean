import Runtime.Reaction
import Runtime.Reactor

namespace Network

structure Graph where
  classes : Type
  root    : classes -- TODO: Is the root still needed now that paths are relative? Or should it be moved to `Network`?
  schemes : classes → (Reactor.Scheme classes)
  [decEqClasses : DecidableEq classes]

attribute [instance] Graph.decEqClasses

namespace Graph

abbrev interface (graph : Graph) («class» : graph.classes) :=
  graph.schemes «class» |>.interface 

end Graph
end Network