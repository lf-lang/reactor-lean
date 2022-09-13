set_option trace.Meta.synthInstance true -- TEMP

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
inductive Path (tree : Tree) : Type _
  | last (branch : tree.branches)
  | cons (branch : tree.branches) [DecidableEq Branches] {subtrees} : (Path $ subtrees branch) → (Path $ .node Branches subtrees)

abbrev subtree : Path tree → Tree 
  | @Path.last branches _ _ subtrees => .node branches subtrees
  | Path.cons _ subpath => subtree subpath

@[reducible]
instance : GetElem Tree (Path t₁) Tree (fun t₂ _ => t₁ = t₂) where
  getElem tree path h := tree.subtree (h ▸ path)

def Path.extend (path : Path tree) (extension : tree[path].branches) : Path tree :=
  match path with
  | @last _ branch _ subtrees => sorry
    -- let y : Path (tree[path].subtrees extension) := Path.last extension
    -- .cons branch 
  | @cons _ _ _ _ _ => sorry

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

-- Used in `Graph.reactionType`.
instance {tree : Tree} {path : Path.Rooted tree} : DecidableEq tree[path].branches :=
  fun b₁ b₂ => sorry

-- theorem getElem_root_eq_tree (tree : Tree) : tree[@Path.Rooted.root tree] = tree := rfl

def Path.Rooted.extend (path : Path.Rooted tree) (extension : tree[path].branches) : Path.Rooted tree :=
  match path with
  | .root => 
    -- let x : Path.Rooted tree := getElem_root_eq_tree tree ▸ Path.last extension
    -- let y := .branch (.last extension)
    sorry
  | .branch path => path.extend extension

def Path.Rooted.extensions (path : Path.Rooted tree) : tree[path].branches → Path tree :=
  sorry


end Tree