import Runtime.Reactor

namespace Network

namespace ReactorID

-- This represents a tree of types for reactors' IDs.
inductive Tree 
  | leaf (IDs : Type)
  | node (IDs : Type) (nested : IDs → Tree)

inductive Nested : Tree → Type _
  | final (id : IDs) : ReactorID.Nested (.leaf IDs)
  | cons (head : IDs) {nested : IDs → Tree} : (ReactorID.Nested $ nested head) → (ReactorID.Nested $ .node IDs next)

inductive _root_.ReactorID (tree : Tree)
  | main
  | nested : Nested tree → ReactorID tree

end ReactorID

structure Scheme where
  tree : ReactorID.Tree
  reactor : (ReactorID tree) → Reactor.Scheme 

def Scheme.reactorIDs (σ : Network.Scheme) := ReactorID σ.tree

structure PortID (kind : PortKind) (σ : Network.Scheme) where
  reactor : σ.reactorIDs
  port : σ.reactor reactor |>.ports kind |>.vars

abbrev Connection (σ : Network.Scheme) := (PortID .output σ) × (PortID .input σ)

structure _root_.Network where
  scheme : Network.Scheme
  reactor : (id : scheme.reactorIDs) → Reactor (scheme.reactor id)
  connections : Array (Connection scheme)

end Network