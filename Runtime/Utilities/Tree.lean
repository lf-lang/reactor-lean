inductive Tree 
  | node (branches : Type) (subtrees : branches → Tree) [decEq : DecidableEq branches]

namespace Tree

abbrev branches : Tree → Type 
  | @node branches _ _ => branches

abbrev subtrees : (tree : Tree) → (tree.branches → Tree)  
  | @node _ subtrees _ => subtrees

private def decEq : (tree : Tree) → DecidableEq tree.branches
  | @node _ _ decEq => decEq

attribute [instance] decEq

-- A path defined by the branches taken through the tree.
inductive Path : Tree → Type _
  | last {tree : Tree} (branch : tree.branches) : Path tree
  | cons {tree : Tree} (branch : tree.branches) : Path (tree.subtrees branch) → Path tree

def subtree : Path tree → Tree 
  | @Path.last tree branch => tree.subtrees branch
  | .cons _ subpath => subtree subpath

-- Cf. notation for `Path.Rooted.subtree'` for docs.
macro:max tree:term noWs "[" path:term "]" : term => `(Tree.subtree (tree := $tree) $path)

def Path.extend : (path : Path tree) → tree[path].branches → Path tree
  | .last branch,         extension => .cons branch (.last extension)
  | .cons branch subpath, extension => .cons branch (subpath.extend extension)

inductive Path.Rooted (tree : Tree)
  | root
  | branch (_ : Path tree)

instance : Coe (Path tree) (Path.Rooted tree) where
  coe := .branch

abbrev subtree' : Path.Rooted tree → Tree
  | .root => tree
  | .branch path => tree.subtree path

-- This is used instead of `GetElem`, because `GetElem` caused problems with 
-- propagating instances of `DecidableEq tree[path].branches`. We use `macro`
-- instead of `notation` as the latter conflicted with type class fields in
-- structures and inductives. The macro is stolen from the one used for `GetElem`:
-- https://github.com/leanprover/lean4/blob/26b417acf8d85c397847d7ebec32d80a6b88ed51/stage0/src/Init/Tactics.lean#L826
macro:max tree:term noWs "[" path:term "]" : term => `(Tree.subtree' (tree := $tree) $path)

def Path.Rooted.extend (path : Path.Rooted tree) (extension : tree[path].branches) : Path.Rooted tree :=
  match path with
  | .root => Path.last extension
  | .branch path => path.extend extension

end Tree