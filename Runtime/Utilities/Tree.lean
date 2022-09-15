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

instance : DecidableEq (Path tree) :=
  fun p₁ p₂ => aux p₁ p₂
where aux : {tree : Tree} → (p₁ : Path tree) → (p₂ : Path tree) → Decidable (p₁ = p₂) 
  | _, .last branch₁, .last branch₂ =>
    if h : branch₁ = branch₂ 
    then .isTrue (by rw [h])
    else .isFalse (by simp [h])
  | _, .cons branch₁ subpath₁, .cons branch₂ subpath₂ =>
    if h : branch₁ = branch₂ then
      match aux subpath₁ (h ▸ subpath₂) with
      | .isTrue h' => .isTrue (by subst h' h; rfl)
      | .isFalse h' => .isFalse (by subst h; simp [h'])  
    else 
      .isFalse (by simp [h])
  | _, .last .., .cons .. => .isFalse (by simp)
  | _, .cons .., .last .. => .isFalse (by simp)

def subtree : Path tree → Tree 
  | @Path.last tree branch => tree.subtrees branch
  | .cons _ subpath => subtree subpath

-- Cf. notation for `Path.Rooted.subtree'` for docs.
macro:max tree:term noWs "[" path:term "]" : term => `(Tree.subtree (tree := $tree) $path)

def Path.extend : (path : Path tree) → tree[path].branches → Path tree
  | .last branch,         extension => .cons branch (.last extension)
  | .cons branch subpath, extension => .cons branch (subpath.extend extension)

def Path.isChildOf : Path tree → Path tree → Bool
  | .cons branch₁ (.last _), .last branch₂ => branch₁ = branch₂ 
  | .cons branch₁ subpath₁, .cons branch₂ subpath₂ => 
    if h : branch₁ = branch₂ 
    then subpath₁.isChildOf (h ▸ subpath₂) 
    else false
  | _, _ => false

inductive Path.Rooted (tree : Tree)
  | root
  | branch (_ : Path tree)

instance : Coe (Path tree) (Path.Rooted tree) where
  coe := .branch

instance : DecidableEq (Path.Rooted tree) :=
  fun
    | .root, .root => .isTrue (by simp)
    | .branch p₁, .branch p₂ =>
      match _root_.decEq p₁ p₂ with
      | .isTrue h => .isTrue (by rw [h])
      | .isFalse h => .isFalse (by simp [h])
    | .root, .branch _ => .isFalse (by simp)
    | .branch _, .root => .isFalse (by simp)

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

def Path.Rooted.isChildOf : Path.Rooted tree → Path.Rooted tree → Bool
  | .branch (.last _), .root => true
  | .branch child, .branch parent => child.isChildOf parent
  | _, _ => false

def Path.Rooted.last (child : Path.Rooted tree) {parent} (h : child.isChildOf parent) : tree[parent].branches :=
  match child with
  | .root => by contradiction
  | .branch (.last last) => sorry -- last
  | .branch (.cons _ subpath) => sorry
  
end Tree