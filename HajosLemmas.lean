import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Hajós cycle decomposition conjecture: definitions and first lemmas

This file deliberately DOES NOT claim a proof of the open conjecture.
The theorems below are elementary partial results.

The target inequality is `cycles.length ≤ (Fintype.card V - 1) / 2`.
Cycles are genuine simple closed walks, represented using mathlib's
`SimpleGraph.Walk.IsCycle` predicate.  A decomposition must use each edge
exactly once (not merely cover the edges).

This source was prepared against the published mathlib4 API.
It has not been executed by a Lean kernel in this environment.
-/

namespace Hajos

universe u

variable {V : Type u}

/-- A based simple cycle in a simple graph. The base vertex is irrelevant
    mathematically, but makes it easy to use `SimpleGraph.Walk.IsCycle`. -/
abbrev SimpleCycle (G : SimpleGraph V) : Type u :=
  Σ v : V, {p : G.Walk v v // p.IsCycle}

/-- The list of *undirected* edges traversed by a cycle. -/
def SimpleCycle.edgeList {G : SimpleGraph V} (c : SimpleCycle G) : List (Sym2 V) :=
  c.2.1.edges

/-- A cycle decomposition must be edge-disjoint and cover all of `G.edgeSet`.
    The `Nodup` condition rules out repeated edges even between cycles. -/
def IsCycleDecomposition (G : SimpleGraph V) (cs : List (SimpleCycle G)) : Prop :=
  (cs.flatMap SimpleCycle.edgeList).Nodup ∧
  ∀ e : Sym2 V, e ∈ G.edgeSet ↔ e ∈ cs.flatMap SimpleCycle.edgeList

/-- `HajosBound G` is the desired conclusion for one graph. -/
def HajosBound [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ cs : List (SimpleCycle G),
    IsCycleDecomposition G cs ∧
    cs.length ≤ (Fintype.card V - 1) / 2

/-- Every degree is even. Isolated vertices are allowed. -/
noncomputable def IsEvenGraph [Fintype V] (G : SimpleGraph V) : Prop := by
  classical
  exact ∀ v : V, Even (G.degree v)

/-- Formal STATEMENT of Hajós's conjecture, NOT a theorem. -/
def HajosConjecture : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
    IsEvenGraph G → HajosBound G

/-- An edgeless graph needs zero cycles. -/
theorem edgeless_hajos [Fintype V] (G : SimpleGraph V)
    (hG : G.edgeSet = ∅) : HajosBound G := by
  refine ⟨[], ?_, by simp⟩
  constructor
  · simp
  · intro e
    simp [hG]

/-- A graph consisting of the edges of one simple cycle needs one cycle.
    The `hcycle` argument specifies that the chosen cycle covers all edges. -/
theorem single_cycle_hajos [Fintype V] (G : SimpleGraph V)
    (c : SimpleCycle G)
    (hcycle : ∀ e : Sym2 V, e ∈ G.edgeSet ↔ e ∈ c.edgeList)
    (hn : 3 ≤ Fintype.card V) : HajosBound G := by
  refine ⟨[c], ?_, ?_⟩
  · constructor
    · simpa [SimpleCycle.edgeList] using c.2.2.edges_nodup
    · intro e
      simpa [SimpleCycle.edgeList] using hcycle e
  · change 1 ≤ (Fintype.card V - 1) / 2
    omega

section Cactus

variable [DecidableEq V]

/-- Union of the vertex supports of a list of cycles. -/
def usedVertices : List (Finset V) → Finset V
  | [] => ∅
  | C :: cs => C ∪ usedVertices cs

/-- A leaf-ordered family of cycle vertex sets.
    Each cycle has at least three vertices and meets the union of later
    cycles in at most one vertex.  These are the combinatorial hypotheses
    satisfied by a suitable ordering of the cycles of a cactus graph. -/
inductive IsLeafOrdered : List (Finset V) → Prop where
  | nil : IsLeafOrdered []
  | cons (C : Finset V) (cs : List (Finset V))
      (hsize : 3 ≤ C.card)
      (hmeet : (C ∩ usedVertices cs).card ≤ 1)
      (htail : IsLeafOrdered cs) : IsLeafOrdered (C :: cs)

/-- Every nonempty leaf-ordered family of k cycles uses at least 2k+1 vertices. -/
theorem IsLeafOrdered.two_mul_length_add_one_le
    {cs : List (Finset V)} (h : IsLeafOrdered cs) :
    cs ≠ [] → 2 * cs.length + 1 ≤ (usedVertices cs).card := by
  induction h with
  | nil =>
      intro hne
      exact False.elim (hne rfl)
  | cons C cs hsize hmeet htail ih =>
      intro _
      by_cases hnil : cs = []
      · subst cs
        simpa [usedVertices] using hsize
      · have hprev : 2 * cs.length + 1 ≤ (usedVertices cs).card := ih hnil
        have hcard := Finset.card_union_add_card_inter C (usedVertices cs)
        simp only [List.length_cons, usedVertices]
        omega

/-- The exact Hajós numerical bound for any leaf-ordered cycle family. -/
theorem IsLeafOrdered.hajos_count [Fintype V]
    {cs : List (Finset V)} (h : IsLeafOrdered cs) :
    cs.length ≤ (Fintype.card V - 1) / 2 := by
  classical
  by_cases hnil : cs = []
  · subst cs
    simp
  · have hlower := h.two_mul_length_add_one_le hnil
    have hupper : (usedVertices cs).card ≤ Fintype.card V := by
      simpa using (Finset.card_le_card (Finset.subset_univ (usedVertices cs)))
    omega

/-- The vertex set visited by a (genuine) simple closed walk. -/
def SimpleCycle.vertexFinset {G : SimpleGraph V} (c : SimpleCycle G) : Finset V :=
  c.2.1.support.toFinset

/-- MAIN PARTIAL RESULT:
    A genuine edge partition into simple cycles satisfies the Hajós bound
    whenever the cycle supports can be arranged in leaf order.

    This implication does not assume that every Eulerian graph has a leaf
    ordering. Proving such a claim would be incorrect in general. -/
theorem leaf_ordered_decomposition_hajos [Fintype V]
    (G : SimpleGraph V) (cs : List (SimpleCycle G))
    (hdec : IsCycleDecomposition G cs)
    (horder : IsLeafOrdered (cs.map SimpleCycle.vertexFinset)) :
    HajosBound G := by
  refine ⟨cs, hdec, ?_⟩
  simpa only [List.length_map] using horder.hajos_count

end Cactus

/-- Local degree-counting bound: if every cycle contributes at most two
    incident edges at a vertex, k cycles contribute at most 2k edges. -/
theorem local_degree_bound {α : Type*} (I : Finset α) (degreeInCycle : α → ℕ)
    (h : ∀ i ∈ I, degreeInCycle i ≤ 2) :
    (∑ i ∈ I, degreeInCycle i) ≤ 2 * I.card := by
  calc
    (∑ i ∈ I, degreeInCycle i) ≤ ∑ _i ∈ I, (2 : ℕ) :=
      Finset.sum_le_sum h
    _ = 2 * I.card := by simp [Nat.mul_comm]

end Hajos

/-!
# Actual Walk/IsCycle surgery: local semantic lemmas

Target: Lean 4.24.0 / mathlib v4.24.0.
STATUS: SOURCE DRAFT, NOT COMPILED OR KERNEL-CHECKED in this environment.

These statements use mathlib's real Walk.IsPath and Walk.IsCycle predicates.
They do not claim the entire decomposition lifting/contraction theorem.
Remaining obligations include rotating arbitrary cycles to the marked edge,
transport across the deleted-vertex subtype, and assembling the edge partition.
-/
namespace Hajos.WalkSurgery

universe u
variable {V : Type u} {G H : SimpleGraph V}

/-- An edge incident to an absent vertex cannot occur in a walk. -/
theorem edge_absent_of_vertex_absent {a b x y : V} (p : G.Walk a b)
    (hx : x ∉ p.support) : s(x, y) ∉ p.edges := by
  intro he
  exact hx (p.fst_mem_support_of_mem_edges he)

/-- Close a simple path using a fresh vertex and two edges.
The distinct-endpoints assumption rules out the invalid two-edge walk. -/
theorem close_path_isCycle {a b z : V} (p : G.Walk a b)
    (hp : p.IsPath) (hz : z ∉ p.support) (hab : a ≠ b)
    (hza : G.Adj z a) (hbz : G.Adj b z) :
    (SimpleGraph.Walk.cons hza (p.concat hbz)).IsCycle := by
  apply (SimpleGraph.Walk.cons_isCycle_iff (p.concat hbz) hza).mpr
  refine ⟨hp.concat hz hbz, ?_⟩
  have hnot : s(z, a) ∉ p.edges := edge_absent_of_vertex_absent p hz
  have hne : s(z, a) ≠ s(b, z) := by
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hab (h.2.trans h.1)
    · exact hab h.2
  intro he
  have hmem : s(z, a) ∈ p.edges ∨ s(z, a) = s(b, z) := by
    simpa only [SimpleGraph.Walk.edges_concat, List.concat_eq_append,
      List.mem_append, List.mem_singleton] using he
  exact hmem.elim hnot hne

/-- Exact edge-list identity for the preceding construction. -/
theorem close_path_edges {a b z : V} (p : G.Walk a b)
    (hza : G.Adj z a) (hbz : G.Adj b z) :
    (SimpleGraph.Walk.cons hza (p.concat hbz)).edges =
      s(z, a) :: (p.edges ++ [s(b, z)]) := by
  simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_concat,
    List.concat_eq_append]

/-- Change the ambient graph of a walk, assuming each USED edge survives.
Unlike a graph homomorphism, this does not require all edges of H to survive. -/
def changeGraph {a b : V} : (p : H.Walk a b) →
    (∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y) → G.Walk a b
  | .nil, _ => .nil
  | .cons _ q, keep =>
      .cons (keep (by simp))
        (changeGraph q (fun {x y} he => keep (by
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr he)))

@[simp]
theorem changeGraph_support {a b : V} (p : H.Walk a b) :
    ∀ (keep : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y),
      (changeGraph p keep).support = p.support := by
  induction p with
  | nil => intro keep; rfl
  | cons h q ih =>
      intro keep
      simp only [changeGraph, SimpleGraph.Walk.support_cons]
      have keep_q : ∀ {x y : V}, s(x, y) ∈ q.edges → G.Adj x y := by
        intro x y he
        exact keep (by
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr he)
      rw [ih keep_q]

@[simp]
theorem changeGraph_edges {a b : V} (p : H.Walk a b) :
    ∀ (keep : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y),
      (changeGraph p keep).edges = p.edges := by
  induction p with
  | nil => intro keep; rfl
  | cons h q ih =>
      intro keep
      simp only [changeGraph, SimpleGraph.Walk.edges_cons]
      have keep_q : ∀ {x y : V}, s(x, y) ∈ q.edges → G.Adj x y := by
        intro x y he
        exact keep (by
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr he)
      rw [ih keep_q]

theorem changeGraph_isPath {a b : V} (p : H.Walk a b)
    (keep : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y)
    (hp : p.IsPath) : (changeGraph p keep).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  simpa only [changeGraph_support] using hp.support_nodup

/-- A marked cycle is already based at a -> b. Delete that edge, transport
its remaining path, and close it through z. This is a genuine IsCycle result,
not a numerical assumption about an unconstructed cycle. -/
theorem subdivide_based_cycle {a b z : V} (hab : H.Adj a b)
    (p : H.Walk b a) (hc : (SimpleGraph.Walk.cons hab p).IsCycle)
    (hz : z ∉ p.support)
    (keep : ∀ {x y : V}, s(x, y) ∈ p.edges → G.Adj x y)
    (hzb : G.Adj z b) (haz : G.Adj a z) :
    (SimpleGraph.Walk.cons hzb ((changeGraph p keep).concat haz)).IsCycle := by
  have hp : p.IsPath :=
    ((SimpleGraph.Walk.cons_isCycle_iff p hab).mp hc).1
  have hba : b ≠ a := (H.ne_of_adj hab).symm
  apply close_path_isCycle (changeGraph p keep)
    (changeGraph_isPath p keep hp) _ hba hzb haz
  simpa only [changeGraph_support] using hz

/-- The local contraction counterpart. Nonadjacency in G guarantees the
shortcut does not already occur in the retained path. -/
theorem contract_path_isCycle {a b : V} (p : G.Walk b a)
    (hp : p.IsPath) (hab : H.Adj a b) (hmissing : ¬ G.Adj a b)
    (keep : ∀ {x y : V}, s(x, y) ∈ p.edges → H.Adj x y) :
    (SimpleGraph.Walk.cons hab (changeGraph p keep)).IsCycle := by
  apply (SimpleGraph.Walk.cons_isCycle_iff (changeGraph p keep) hab).mpr
  refine ⟨changeGraph_isPath p keep hp, ?_⟩
  intro he
  have he' : s(a, b) ∈ p.edges := by
    simpa only [changeGraph_edges] using he
  exact hmissing (p.adj_of_mem_edges he')

#print axioms close_path_isCycle
#print axioms subdivide_based_cycle
#print axioms contract_path_isCycle

end Hajos.WalkSurgery
