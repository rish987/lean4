/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Batteries.Util.Panic

namespace Batteries

/-- Union-find node type -/
structure UFNode where
  /-- Parent of node -/
  parent : Nat
  /-- Rank of node -/
  rank : Nat

namespace UnionFind

/-- Parent of a union-find node, defaults to self when the node is a root -/
def parentD (arr : Array UFNode) (i : Nat) : Nat :=
  if h : i < arr.size then arr[i].parent else i

/-- Rank of a union-find node, defaults to 0 when the node is a root -/
def rankD (arr : Array UFNode) (i : Nat) : Nat :=
  if h : i < arr.size then arr[i].rank else 0

theorem parentD_eq {arr : Array UFNode} {i} (h) :
    parentD arr i = arr[i].parent := dif_pos _

theorem rankD_eq {arr : Array UFNode} {i} (h) : rankD arr i = arr[i].rank := dif_pos _

theorem parentD_of_not_lt : ¬i < arr.size → parentD arr i = i := (dif_neg ·)

theorem lt_of_parentD : parentD arr i ≠ i → i < arr.size :=
  Decidable.not_imp_comm.1 parentD_of_not_lt

end UnionFind

open UnionFind

/-- ### Union-find data structure

The `UnionFind` structure is an implementation of disjoint-set data structure
that uses path compression to make the primary operations run in amortized
nearly linear time. The nodes of a `UnionFind` structure `s` are natural
numbers smaller than `s.size`. The structure associates with a canonical
representative from its equivalence class. The structure can be extended
using the `push` operation and equivalence classes can be updated using the
`union` operation.

The main operations for `UnionFind` are:

* `empty`/`mkEmpty` are used to create a new empty structure.
* `size` returns the size of the data structure.
* `push` adds a new node to a structure, unlinked to any other node.
* `union` links two nodes of the data structure, joining their equivalence
  classes, and performs path compression.
* `find` returns the canonical representative of a node and updates the data
  structure using path compression.
* `root` returns the canonical representative of a node without altering the
  data structure.
* `checkEquiv` checks whether two nodes have the same canonical representative
  and updates the structure using path compression.

Most use cases should prefer `find` over `root` to benefit from the speedup from path-compression.

The main operations use `Fin s.size` to represent nodes of the union-find structure.
Some alternatives are provided:

* `unionN`, `findN`, `rootN`, `checkEquivN` use `Fin n` with a proof that `n = s.size`.
* `union!`, `find!`, `root!`, `checkEquiv!` use `Nat` and panic when the indices are out of bounds.
* `findD`, `rootD`, `checkEquivD` use `Nat` and treat out of bound indices as isolated nodes.

The noncomputable relation `UnionFind.Equiv` is provided to use the equivalence relation from a
`UnionFind` structure in the context of proofs.
-/
structure UnionFind where
  /-- Array of union-find nodes -/
  arr : Array UFNode
  /-- Validity for parent nodes -/
  parentD_lt : ∀ {i}, i < arr.size → parentD arr i < arr.size
  /-- Validity for rank -/
  rankD_lt : ∀ {i}, parentD arr i ≠ i → rankD arr i < rankD arr (parentD arr i)

namespace UnionFind

/-- Size of union-find structure. -/
@[inline] abbrev size (self : UnionFind) := self.arr.size

/-- Create an empty union-find structure with specific capacity -/
def mkEmpty (c : Nat) : UnionFind where
  arr := Array.mkEmpty c
  parentD_lt := nofun
  rankD_lt := nofun

/-- Empty union-find structure -/
def empty := mkEmpty 0

instance : EmptyCollection UnionFind := ⟨.empty⟩

/-- Parent of union-find node -/
abbrev parent (self : UnionFind) (i : Nat) : Nat := parentD self.arr i

theorem parent'_lt (self : UnionFind) (i : Nat) (h) : self.arr[i].parent < self.size := by
  simp [← parentD_eq, parentD_lt, Fin.is_lt, Array.length_toList, h]

theorem parent_lt (self : UnionFind) (i : Nat) : self.parent i < self.size ↔ i < self.size := by
  simp only [parentD]; split <;> simp only [*, parent'_lt]

/-- Rank of union-find node -/
abbrev rank (self : UnionFind) (i : Nat) : Nat := rankD self.arr i

theorem rank_lt {self : UnionFind} {i : Nat} : self.parent i ≠ i →
    self.rank i < self.rank (self.parent i) := by simpa only [rank] using self.rankD_lt

theorem rank'_lt (self : UnionFind) (i h) : self.arr[i].parent ≠ i →
    self.rank i < self.rank (self.arr[i]).parent := by
  simpa only [← parentD_eq] using self.rankD_lt

/-- Maximum rank of nodes in a union-find structure -/
noncomputable def rankMax (self : UnionFind) := self.arr.foldr (max ·.rank) 0 + 1

theorem rank'_lt_rankMax (self : UnionFind) (i : Nat) (h) : (self.arr[i]).rank < self.rankMax := by
  let rec go : ∀ {l} {x : UFNode}, x ∈ l → x.rank ≤ List.foldr (max ·.rank) 0 l
    | a::l, _, List.Mem.head _ => by dsimp; apply Nat.le_max_left
    | a::l, _, .tail _ h => by dsimp; exact Nat.le_trans (go h) (Nat.le_max_right ..)
  simp only [Array.get_eq_getElem, rankMax, ← Array.foldr_toList]
  exact Nat.lt_succ.2 <| go (self.arr.toList.getElem_mem _)

theorem push_rankD (arr : Array UFNode) : rankD (arr.push ⟨arr.size, 0⟩) i = rankD arr i := by
  simp only [rankD, Array.size_push, Array.get_eq_getElem, Array.getElem_push, dite_eq_ite]
  split <;> split <;> first | simp | cases ‹¬_› (Nat.lt_succ_of_lt ‹_›)

/-- Add a new node to a union-find structure, unlinked with any other nodes -/
def push (self : UnionFind) : UnionFind where
  arr := self.arr.push ⟨self.arr.size, 0⟩
  parentD_lt {i} := sorry
  rankD_lt := by sorry

-- /-- Root of a union-find node. -/
-- def root (self : UnionFind) (x : Fin self.size) : Fin self.size :=
--   let y := self.arr[x.1].parent
--   if h : y = x then
--     x
--   else
--     have := Nat.sub_lt_sub_left (self.lt_rankMax x) (self.rank'_lt _ _ h)
--     self.root ⟨y, self.parent'_lt x _⟩
-- termination_by self.rankMax - self.rank x

-- @[inherit_doc root]
-- def rootN (self : UnionFind) (x : Fin n) (h : n = self.size) : Fin n :=
--   match n, h with | _, rfl => self.root x
--
-- /-- Root of a union-find node. Panics if index is out of bounds. -/
-- def root! (self : UnionFind) (x : Nat) : Nat :=
--   if h : x < self.size then self.root ⟨x, h⟩ else panicWith x "index out of bounds"
--
-- /-- Root of a union-find node. Returns input if index is out of bounds. -/
-- def rootD (self : UnionFind) (x : Nat) : Nat :=
--   if h : x < self.size then self.root ⟨x, h⟩ else x

theorem push_parentD (arr : Array UFNode) : parentD (arr.push ⟨arr.size, 0⟩) i = parentD arr i := by
  simp only [parentD, Array.size_push, Array.get_eq_getElem, Array.getElem_push, dite_eq_ite]
  split <;> split <;> try simp
  · exact Nat.le_antisymm (Nat.ge_of_not_lt ‹_›) (Nat.le_of_lt_succ ‹_›)
  · cases ‹¬_› (Nat.lt_succ_of_lt ‹_›)

/-- Auxiliary data structure for find operation -/
structure FindAux (n : Nat) where
  /-- Array of nodes -/
  s : Array UFNode
  /-- Index of root node -/
  root : Fin n
  /-- Size requirement -/
  size_eq : s.size = n

/-- Auxiliary function for find operation -/
def findAux (self : UnionFind) (x : Fin self.size) : FindAux self.size :=
  let y := self.arr[x.1].parent
  if h : y = x then
    ⟨self.arr, x, rfl⟩
  else
    have : self.rankMax - self.rank self.arr[↑x].parent < self.rankMax - self.rank ↑x := sorry
    let ⟨arr₁, root, H⟩ := self.findAux ⟨y, self.parent'_lt _ x.2⟩
    ⟨arr₁.modify x fun s => { s with parent := root }, root, by simp [H]⟩
termination_by self.rankMax - self.rank x

/-- Find root of a union-find node, updating the structure using path compression. -/
def find (self : UnionFind) (x : Fin self.size) :
    (s : UnionFind) × {_root : Fin s.size // s.size = self.size} :=
  let r := self.findAux x
  { 1.arr := r.s
    2.1.val := r.root
    1.parentD_lt := fun h => by
      simp only [Array.length_toList, FindAux.size_eq] at *
      sorry
    1.rankD_lt := fun h => by sorry
    2.1.isLt := show _ < r.s.size by rw [r.size_eq]; exact r.root.2
    2.2 := by simp [size, r.size_eq] }

@[inherit_doc find]
def findN (self : UnionFind) (x : Fin n) (h : n = self.size) : UnionFind × Fin n :=
  match n, h with | _, rfl => match self.find x with | ⟨s, r, h⟩ => (s, Fin.cast h r)

/-- Find root of a union-find node, updating the structure using path compression.
  Panics if index is out of bounds. -/
def find! (self : UnionFind) (x : Nat) : UnionFind × Nat :=
  if h : x < self.size then
    match self.find ⟨x, h⟩ with | ⟨s, r, _⟩ => (s, r)
  else
    panicWith (self, x) "index out of bounds"

/-- Find root of a union-find node, updating the structure using path compression.
  Returns inputs unchanged when index is out of bounds. -/
def findD (self : UnionFind) (x : Nat) : UnionFind × Nat :=
  if h : x < self.size then
    match self.find ⟨x, h⟩ with | ⟨s, r, _⟩ => (s, r)
  else
    (self, x)

@[simp] theorem find_size (self : UnionFind) (x : Fin self.size) :
    (self.find x).1.size = self.size := by simp [find, size, FindAux.size_eq]


/-- Link two union-find nodes -/
def linkAux (self : Array UFNode) (x y : Fin self.size) : Array UFNode :=
  if x.1 = y then
    self
  else
    let nx := self[x.1]
    let ny := self[y.1]
    if ny.rank < nx.rank then
      self.set y {ny with parent := x}
    else
      let arr₁ := self.set x {nx with parent := y}
      if nx.rank = ny.rank then
        arr₁.set y {ny with rank := ny.rank + 1} (by simp [arr₁])
      else
        arr₁

/-- Link a union-find node to a root node. -/
def link (self : UnionFind) (x y : Fin self.size) (yroot : self.parent y = y) : UnionFind where
  arr := linkAux self.arr x y
  parentD_lt h := sorry
  rankD_lt := sorry

@[inherit_doc link]
def linkN (self : UnionFind) (x y : Fin n) (yroot : self.parent y = y) (h : n = self.size) :
    UnionFind := match n, h with | _, rfl => self.link x y yroot

/-- Link a union-find node to a root node. Panics if either index is out of bounds. -/
def link! (self : UnionFind) (x y : Nat) (yroot : self.parent y = y) : UnionFind :=
  if h : x < self.size ∧ y < self.size then
    self.link ⟨x, h.1⟩ ⟨y, h.2⟩ yroot
  else
    panicWith self "index out of bounds"

/-- Link two union-find nodes, uniting their respective classes. -/
def union (self : UnionFind) (x y : Fin self.size) : UnionFind :=
  let ⟨self₁, rx, ex⟩ := self.find x
  have hy := by rw [ex]; exact y.2
  match eq : self₁.find ⟨y, hy⟩ with
  | ⟨self₂, ry, ey⟩ =>
    self₂.link ⟨rx, by rw [ey]; exact rx.2⟩ ry <| by sorry

@[inherit_doc union]
def unionN (self : UnionFind) (x y : Fin n) (h : n = self.size) : UnionFind :=
  match n, h with | _, rfl => self.union x y

/-- Link two union-find nodes, uniting their respective classes.
Panics if either index is out of bounds. -/
def union! (self : UnionFind) (x y : Nat) : UnionFind :=
  if h : x < self.size ∧ y < self.size then
    self.union ⟨x, h.1⟩ ⟨y, h.2⟩
  else
    panicWith self "index out of bounds"

/-- Check whether two union-find nodes are equivalent, updating structure using path compression. -/
def checkEquiv (self : UnionFind) (x y : Fin self.size) : UnionFind × Bool :=
  let ⟨s, ⟨r₁, _⟩, h⟩ := self.find x
  let ⟨s, ⟨r₂, _⟩, _⟩ := s.find (h ▸ y)
  (s, r₁ == r₂)

@[inherit_doc checkEquiv]
def checkEquivN (self : UnionFind) (x y : Fin n) (h : n = self.size) : UnionFind × Bool :=
  match n, h with | _, rfl => self.checkEquiv x y

/-- Check whether two union-find nodes are equivalent, updating structure using path compression.
Panics if either index is out of bounds. -/
def checkEquiv! (self : UnionFind) (x y : Nat) : UnionFind × Bool :=
  if h : x < self.size ∧ y < self.size then
    self.checkEquiv ⟨x, h.1⟩ ⟨y, h.2⟩
  else
    panicWith (self, false) "index out of bounds"

/-- Check whether two union-find nodes are equivalent with path compression,
returns `x == y` if either index is out of bounds -/
def checkEquivD (self : UnionFind) (x y : Nat) : UnionFind × Bool :=
  let (s, x) := self.findD x
  let (s, y) := s.findD y
  (s, x == y)

-- /-- Equivalence relation from a `UnionFind` structure -/
-- def Equiv (self : UnionFind) (a b : Nat) : Prop := self.rootD a = self.rootD b
