import Runtime.Utilities.Extensions

inductive Tree 
  | node (branches : Type) (subtrees : branches → Tree) [decEq : DecidableEq branches]

namespace Tree

instance : Inhabited Tree where
  default := .node Empty (·.rec)

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
  | .cons _ subpath        => subtree subpath

-- Cf. notation for `Path.Rooted.subtree'` for docs.
macro:max tree:term noWs "[" path:term "]" : term => `(Tree.subtree (tree := $tree) $path)

theorem Path.branches_subtree_cons {path} : (subtree (Path.cons branch path)).branches = (subtree path).branches := rfl

def Path.extend : (path : Path tree) → tree[path].branches → Path tree
  | .last branch,         extension => .cons branch (.last extension)
  | .cons branch subpath, extension => .cons branch (subpath.extend extension)

theorem Path.extend_cons_eq_cons_extend : (Path.cons branch₁ path).extend branch₂ = .cons branch₁ (path.extend $ branches_subtree_cons ▸ branch₂) := rfl

def Path.isChildOf : Path tree → Path tree → Bool
  | .cons branch₁ (.last _), .last branch₂ => branch₁ = branch₂ 
  | .cons branch₁ subpath₁, .cons branch₂ subpath₂ => 
    if h : branch₁ = branch₂ 
    then subpath₁.isChildOf (h ▸ subpath₂) 
    else false
  | _, _ => false

theorem Path.isChildOf_cons_eq_branch : isChildOf (.cons branch₁ child) (.cons branch₂ parent) → branch₁ = branch₂ := by
  intro h
  simp [isChildOf] at h
  split at h <;> simp [*]

theorem Path.isChildOf_cons : isChildOf (.cons branch child) (.cons branch parent) → child.isChildOf parent :=
  fun _ => by simp_all [isChildOf]

def Path.last' (child : Path tree) {parent} (h : child.isChildOf parent) : tree[parent].branches :=
  match child, parent with
  | .cons branch₁ (.last l), .last branch₂ => 
    have h : branch₁ = branch₂ := by simp_all [isChildOf]
    h ▸ l
  | .cons branch₁ subpath₁,  .cons branch₂ subpath₂ =>
    have hb : branch₁ = branch₂ := isChildOf_cons_eq_branch h
    (hb ▸ subpath₁).last' (by subst hb; exact isChildOf_cons h)

theorem Path.last'_cons_eq_last' : branches_subtree_cons ▸ Path.last' (.cons branch path) h₁ = path.last' h₂ := by
  simp [isChildOf] at h₁
  simp [last']

theorem Path.extend_parent_child_last'_eq_child {child parent : Path tree} (h : child.isChildOf parent) :
  parent.extend (child.last' h) = child := by
  induction child
  case last => simp [isChildOf] at h
  case cons branch₁ childPath hi =>
    cases parent
    case cons branch₂ parentPath =>
      have hb := Path.isChildOf_cons_eq_branch h
      subst hb
      have h' : last' (cons branch₁ childPath) h = last' childPath (Path.isChildOf_cons h) := by rw [←last'_cons_eq_last'] 
      simp [extend_cons_eq_cons_extend, h', hi (Path.isChildOf_cons h)]
    case last => 
      cases childPath <;> simp [isChildOf] at h
      subst h
      rfl

def Path.isSiblingOf : Path tree → Path tree → Bool
  | .last _, .last _ => true
  | .cons branch₁ subpath₁, .cons branch₂ subpath₂ =>
    if h : branch₁ = branch₂ 
    then subpath₁.isSiblingOf (h ▸ subpath₂) 
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
  | .root        => Path.last extension
  | .branch path => path.extend extension

def Path.Rooted.isChildOf : Path.Rooted tree → Path.Rooted tree → Bool
  | .branch (.last _), .root          => true
  | .branch child,     .branch parent => child.isChildOf parent
  | _,                 _              => false

theorem Path.Rooted.isChildOf_cons : isChildOf (.branch child) (.branch parent) → child.isChildOf parent :=
  fun _ => by simp_all [isChildOf]

def Path.Rooted.last (child : Path.Rooted tree) {parent} (h : child.isChildOf parent) : tree[parent].branches :=
  match child, parent with
  | .branch (.last last), .root     => last
  | .branch path₁,        .branch _ => path₁.last' (isChildOf_cons h)
    
theorem Path.Rooted.extend_parent_child_last_eq_child {child parent : Path.Rooted tree} (h : child.isChildOf parent) :
  parent.extend (child.last h) = child := by
  cases parent 
  case root =>
    cases child
    case root => simp [isChildOf] at h
    case branch path =>
      simp [extend]
      cases path
      case last => simp [last]
      case cons => simp [isChildOf] at h
  case branch path =>
      simp [extend]
      cases child <;> simp [isChildOf] at h
      case branch path' => simp [last, Path.extend_parent_child_last'_eq_child h]

def Path.Rooted.isSiblingOf : Path.Rooted tree → Path.Rooted tree → Bool 
  | .root,         .root         => true
  | .branch path₁, .branch path₂ => path₁.isSiblingOf path₂
  | _,             _             => false

end Tree