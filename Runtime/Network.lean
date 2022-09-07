import Runtime.Reactor

namespace Network

-- This induces a tree of types.
inductive IDTree 
  | leaf (IDs : Type)
  | node (IDs : Type) (nested : IDs → IDTree)

inductive ID.Nested : IDTree → Type _
  | final (id : IDs) : ID.Nested (.leaf IDs)
  | cons (head : IDs) {nested : IDs → IDTree} : (ID.Nested $ nested head) → (ID.Nested $ .node IDs next)

inductive ID (tree : IDTree)
  | main
  | nested : ID.Nested tree → ID tree

end Network

open Network in
structure Network where
  idTree : IDTree
  structures : (ID idTree) → Reactor.Structure
  reactors : (id : ID idTree) → Reactor (structures id)
