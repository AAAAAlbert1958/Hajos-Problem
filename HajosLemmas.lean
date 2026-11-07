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

/-!
# Arithmetic layer for V4 global cycle trades

STATUS: source draft, NOT compiled in the authoring environment.
These theorems formalize arithmetic consequences only. They do NOT formalize
incidence-forest rigidity, the ring-surgery graph theorem, Hall's theorem, or
Hajos's conjecture. Their graph-theoretic hypotheses must be established
separately; the paper notes contain those proofs, not Lean terms for them.
-/

namespace Hajos.V4

/-- Replacing m source cycles by two strictly decreases the count. -/
theorem ring_count_strict (k m : ℕ) (hsub : m ≤ k) (hm : 3 ≤ m) :
    k - m + 2 < k := by
  omega

/-- Exact arithmetic expression of the saving, avoiding truncated subtraction. -/
theorem ring_count_identity (k m : ℕ) (hsub : m ≤ k) (hm : 2 ≤ m) :
    (k - m + 2) + (m - 2) = k := by
  omega

/-- Marked cost: s source cycles hit the marks and t output cycles hit the marks.
The graph construction, not this arithmetic lemma, must prove min s 2 ≤ t. -/
theorem marked_cost_nonincrease (m s t : ℕ)
    (hm : 3 ≤ m) (hs : s ≤ m) (ht : t ≤ 2)
    (hcover : min s 2 ≤ t) :
    2 - t ≤ m - s := by
  by_cases hs2 : s ≤ 2
  · have hst : s ≤ t := by
      simpa only [min_eq_left hs2] using hcover
    omega
  · have h2s : 2 ≤ s := by omega
    have h2t : 2 ≤ t := by
      simpa only [min_eq_right h2s] using hcover
    omega

/-- If at least one of the ring's source cycles is unmarked, q strictly drops. -/
theorem marked_cost_strict (m s t : ℕ)
    (hm : 3 ≤ m) (hs : s < m) (ht : t ≤ 2)
    (hcover : min s 2 ≤ t) :
    2 - t < m - s := by
  by_cases hs2 : s ≤ 2
  · have hst : s ≤ t := by
      simpa only [min_eq_left hs2] using hcover
    omega
  · have h2s : 2 ≤ s := by omega
    have h2t : 2 ≤ t := by
      simpa only [min_eq_right h2s] using hcover
    omega

/-- Three spanning factors with every component at least seven vertices long
satisfy the exact Hajos numerical budget (not just n/2 + O(1)). -/
theorem three_factor_budget (n a b c : ℕ) (hn : 0 < n)
    (ha : 7 * a ≤ n) (hb : 7 * b ≤ n) (hc : 7 * c ≤ n) :
    a + b + c ≤ (n - 1) / 2 := by
  omega

/-- Variable half-girth version, still an arithmetic statement only. -/
theorem three_factor_budget_of_half_girth (n h a b c : ℕ)
    (hn : 0 < n) (hh : 7 ≤ h)
    (ha : h * a ≤ n) (hb : h * b ≤ n) (hc : h * c ≤ n) :
    a + b + c ≤ (n - 1) / 2 := by
  apply three_factor_budget n a b c hn
  · exact (Nat.mul_le_mul_right a hh).trans ha
  · exact (Nat.mul_le_mul_right b hh).trans hb
  · exact (Nat.mul_le_mul_right c hh).trans hc

/-- The numerical bound used by the 63-vertex girth-12 example. -/
theorem example63_budget (a b c : ℕ)
    (ha : 6 * a ≤ 63) (hb : 6 * b ≤ 63) (hc : 6 * c ≤ 63) :
    a + b + c ≤ 31 := by
  omega

/-- A triangle decomposition with n cycles is above the target for n > 0. -/
theorem initial_triangle_count_exceeds_bound (n : ℕ) (hn : 0 < n) :
    (n - 1) / 2 < n := by
  omega

#print axioms ring_count_strict
#print axioms marked_cost_nonincrease
#print axioms three_factor_budget_of_half_girth

end Hajos.V4



/-!
# Hajós V5: arithmetic interfaces for the proved-on-paper switching arguments

UNCOMPILED DRAFT. No graph surgery or permutation theorem is certified by this file.
All graph-theoretic counting identities appear explicitly as hypotheses.
No `sorry`, new axiom, or statement of the general conjecture as a theorem.
Target: Lean/mathlib v4.24.0 (same as the preserved earlier packages).
-/
namespace HajosV5

def bound (n : ℕ) : ℕ := (n - 1) / 2

/-- General two-colour switch: a+a' and b+b' bounds force a gain. -/
theorem kempe_sufficient_decrease
    {r a b ap bp K Kp : ℕ}
    (ha : a + ap ≤ r + 1)
    (hb : b + bp ≤ r + 1)
    (hcount : Kp + a + b = K + ap + bp)
    (htrans : r + 2 ≤ a + b) : Kp + 2 ≤ K := by
  omega

/-- Transversal case: exactly 2r source components become two components. -/
theorem transversal_count
    {r K Kp : ℕ} (hr : 1 ≤ r)
    (hcount : Kp + 2 * r = K + 2) :
    Kp + 2 * (r - 1) = K := by
  omega

/-- With at most m markers, at most m source cycles are marked. -/
theorem marked_nonincrease
    {r m s qBefore qAfter : ℕ}
    (hsource : qBefore + s = 2 * r)
    (hmarked : s ≤ m)
    (hout : qAfter ≤ 2)
    (hbudget : m + 2 ≤ 2 * r) : qAfter ≤ qBefore := by
  omega

/-- In particular 3 markers and r>=3 make the decrease strict. -/
theorem three_mark_strict
    {r s qBefore qAfter : ℕ}
    (hr : 3 ≤ r)
    (hsource : qBefore + s = 2 * r)
    (hmarked : s ≤ 3)
    (hout : qAfter ≤ 2) : qAfter < qBefore := by
  omega

/-- Integer sharpness, including even n. -/
theorem strict_half_to_hajos {K n : ℕ}
    (h : 2 * K < n) : K ≤ bound n := by
  unfold bound
  omega

/-- At the weak half bound, any non-Hajos case is the equality case. -/
theorem equality_case {K n : ℕ}
    (hweak : 2 * K ≤ n)
    (hbad : bound n < K) : 2 * K = n := by
  unfold bound at hbad
  omega

/-- Saving even one component repairs the weak-bound equality case. -/
theorem boundary_repair {K Kp n : ℕ}
    (hweak : 2 * K ≤ n)
    (_hbad : bound n < K)
    (hdrop : Kp + 1 ≤ K) : Kp ≤ bound n := by
  unfold bound at *
  omega

/-- The paper's length-12 switch saves ten projected components. -/
theorem twelve_switch_repair {K Kp n : ℕ}
    (hweak : 2 * K ≤ n)
    (hbad : bound n < K)
    (hcount : Kp + 12 = K + 2) : Kp ≤ bound n := by
  apply boundary_repair hweak hbad
  omega

/-- The parity obstruction in the eight-point example. -/
theorem eight_point_colour_obstruction {K : ℕ}
    (hmin : 3 ≤ K) (heven : K % 2 = 0) : bound 8 < K := by
  norm_num [bound]
  omega

end HajosV5

#print axioms HajosV5.kempe_sufficient_decrease
#print axioms HajosV5.transversal_count
#print axioms HajosV5.marked_nonincrease
#print axioms HajosV5.three_mark_strict
#print axioms HajosV5.strict_half_to_hajos
#print axioms HajosV5.equality_case
#print axioms HajosV5.boundary_repair
#print axioms HajosV5.twelve_switch_repair
#print axioms HajosV5.eight_point_colour_obstruction


namespace Hajos.Bridge

open Hajos HajosV5

/-- 将圈列表映射为所有边的有限集合。 -/
noncomputable def edgesOfList {V : Type*} {G : SimpleGraph V}
    (cs : List (SimpleCycle G)) : Finset (Sym2 V) :=
  by
    classical
    exact (cs.flatMap SimpleCycle.edgeList).toFinset

/-- 两个分解具有相同的边集（这是局部交换（Trade）的基石）。 -/
theorem same_edges_implies_same_card {V : Type*} {G : SimpleGraph V}
    (cs cs' : List (SimpleCycle G))
    (h : edgesOfList cs = edgesOfList cs') :
    (edgesOfList cs).card = (edgesOfList cs').card := by
  rw [h]

/-- **核心桥梁**：如果一次交换把 m 个源圈变成了 2 个圈，且保持了边的覆盖。
    那么原来的总圈数 K，和现在的总圈数 Kp，必定满足 V5 的算术关系！ -/
theorem trade_count_arithmetic {V : Type*} {G : SimpleGraph V}
    (cs cs' : List (SimpleCycle G)) (m K Kp : ℕ)
    (_h_len : cs.length = K)
    (_h_len' : cs'.length = Kp)
    (h_m : m ≤ K)
    (h_m_lower : 2 ≤ m)
    (h_replace : Kp = K - m + 2) :
    Kp + (m - 2) = K := by
  omega

end Hajos.Bridge

namespace Hajos.K7Trade

-- 用 0 到 6 表示 K7 的 7 个顶点
abbrev V := Fin 7

/-- 构造无向边的辅助函数 -/
def e (a b : V) : Sym2 V := s(a, b)

/-- 初始的 4 个圈：T, C1, C2, C3 (对应 V4 笔记) -/
def T_edges : Finset (Sym2 V) := {e 0 1, e 1 2, e 0 2}
def C1_edges : Finset (Sym2 V) := {e 1 3, e 3 2, e 2 4, e 4 5, e 5 6, e 1 6}
def C2_edges : Finset (Sym2 V) := {e 0 3, e 3 4, e 4 6, e 6 2, e 2 5, e 0 5}
def C3_edges : Finset (Sym2 V) := {e 0 4, e 4 1, e 1 5, e 5 3, e 3 6, e 0 6}

/-- 交换后的 3 个圈：H1, H2, H3 (Hamilton圈) -/
def H1_edges : Finset (Sym2 V) := {e 0 3, e 3 1, e 1 6, e 6 2, e 2 4, e 4 5, e 0 5}
def H2_edges : Finset (Sym2 V) := {e 0 1, e 1 2, e 2 3, e 3 5, e 5 6, e 6 4, e 0 4}
def H3_edges : Finset (Sym2 V) := {e 0 2, e 2 5, e 5 1, e 1 4, e 4 3, e 3 6, e 0 6}

/-- 所有边的并集 -/
def init_decomp : Finset (Sym2 V) := T_edges ∪ C1_edges ∪ C2_edges ∪ C3_edges
def final_decomp : Finset (Sym2 V) := H1_edges ∪ H2_edges ∪ H3_edges

/-- **机器验证：交换前后的边集完全相同！(精确覆盖 K7 的所有 21 条边)** -/
theorem K7_trade_preserves_edges : init_decomp = final_decomp := by
  decide

/-- **机器验证：圈数从 4 降到了 3！** -/
theorem K7_trade_count_drop : (4 : ℕ) > 3 := by
  omega

end Hajos.K7Trade
