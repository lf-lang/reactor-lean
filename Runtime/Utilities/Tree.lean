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

abbrev subtree : Path tree → Tree 
  | @Path.last tree branch => tree.subtrees branch
  | .cons _ subpath => subtree subpath

@[reducible]
instance : GetElem Tree (Path t₁) Tree (fun t₂ _ => t₁ = t₂) where
  getElem tree path h := tree.subtree (h ▸ path)

def Path.extend (path : Path tree) (extension : tree[path].branches) : Path tree :=
  match path with
  | .last branch => .cons branch (.last extension)
  | .cons branch subpath => .cons branch (subpath.extend extension)

def Path.extensions (path : Path tree) : tree[path].branches → Path tree :=
  (path.extend ·)

inductive Path.Rooted (tree : Tree)
  | root
  | branch (_ : Path tree)

instance : Coe (Path tree) (Path.Rooted tree) where
  coe := .branch

abbrev subtree' : Path.Rooted tree → Tree
  | .root => tree
  | .branch path => tree.subtree path

@[reducible]
instance : GetElem Tree (Path.Rooted t₁) Tree (fun t₂ _ => t₁ = t₂) where
  getElem tree path h := tree.subtree' (h ▸ path)

def Path.Rooted.extend (path : Path.Rooted tree) (extension : tree[path].branches) : Path.Rooted tree :=
  match path with
  | .root => Path.last extension
  | .branch path => path.extend extension

def Path.Rooted.extensions : (path : Path.Rooted tree) → tree[path].branches → Path tree
  | .root => (.last ·)
  | .branch path => (path.extend ·)

end Tree