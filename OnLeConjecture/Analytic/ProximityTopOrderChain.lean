/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticPointBasis
public import OnLeConjecture.Analytic.FreeChainStraightening
public import OnLeConjecture.Numerical.ProximityReduction
import Mathlib.Tactic

/-!
# The top-order chain from matched analytic and proximity data

The proximity certificate has the same root and multiplicities as the
analytic point basis. Every immediate predecessor is a proximity parent,
and all proximity parents precede the child in the recorded generation.
Nestedness of the two parents at satellite points is stated explicitly.

These data construct the chain of all points with root multiplicity.
Neither the chain nor its cardinality is an input. The nonsatellite
conclusion is a statement about proximity parents. Compatible analytic
coordinates for free charts are a separate input to the straightening
theorems at the end of the file.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A numerical proximity certificate matched to the recorded analytic
germs, their immediate predecessors, and their generations. -/
structure AnalyticProximityData {N : ℕ} (c : AnalyticPointBasis N) where
  proximity : Numerical.ProximityCertificate (Fin N)
  root_eq : proximity.root = c.root
  multiplicity_eq : proximity.multiplicity = c.multiplicity
  predecessor_mem : ∀ q, q ≠ c.root → c.predecessor q ∈ proximity.parents q
  generation_decreases : ∀ {q p}, proximity.ParentRelation q p →
    c.generation p < c.generation q
  nested_parents : ∀ q, (proximity.parents q).card = 2 →
    ∃ p r, proximity.ParentRelation q p ∧ proximity.ParentRelation q r ∧
      proximity.ParentRelation p r

/-- An indexed chain containing exactly the root-order points.
Injectivity and the equality between its length and the top-order count
are theorems, not fields. -/
structure AnalyticTopOrderChain {N : ℕ} (c : AnalyticPointBasis N) where
  length : ℕ
  length_pos : 0 < length
  point : ℕ → Fin N
  point_zero : point 0 = c.root
  chain : ∀ j, j + 1 < length → c.ParentRelation (point (j + 1)) (point j)
  order : ∀ j < length, c.multiplicity (point j) = c.multiplicity c.root
  covers : ∀ q, c.multiplicity q = c.multiplicity c.root → ∃ j < length, point j = q

namespace AnalyticPointBasis

variable {N : ℕ} (c : AnalyticPointBasis N)

theorem predecessor_top_order {q p : Fin N} (hq : c.multiplicity q = c.multiplicity c.root)
    (hparent : c.ParentRelation q p) : c.multiplicity p = c.multiplicity c.root := by
  apply le_antisymm (c.multiplicity_le_root p)
  rw [← hq]
  exact c.multiplicity_le_of_parent hparent

/-- An ancestral path to a top-order point consists entirely of
top-order points, and admits an explicit consecutive indexing. -/
theorem exists_indexed_top_order_path (q : Fin N) (hq : c.multiplicity q = c.multiplicity c.root) :
    ∃ (L : ℕ) (point : ℕ → Fin N), point 0 = c.root ∧ point L = q ∧
      (∀ j < L, c.ParentRelation (point (j + 1)) (point j)) ∧
      ∀ j ≤ L, c.multiplicity (point j) = c.multiplicity c.root := by
  have hpath := c.root_ancestor q
  revert hq
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro _
      exact ⟨0, fun _ ↦ c.root, rfl, rfl, by simp, fun _ _ ↦ rfl⟩
  | @head q p hparent _hpath ih =>
      intro hq
      obtain ⟨L, point, hzero, hlast, hchain, horder⟩ :=
        ih (c.predecessor_top_order hq hparent)
      let next : ℕ → Fin N := fun j ↦ if j ≤ L then point j else q
      refine ⟨L + 1, next, ?_, ?_, ?_, ?_⟩
      · simpa only [next, if_pos (Nat.zero_le L)] using hzero
      · simp [next]
      · intro j hj
        by_cases hjL : j < L
        · simpa only [next, if_pos (by omega : j ≤ L),
            if_pos (by omega : j + 1 ≤ L)] using hchain j hjL
        · have heq : j = L := by omega
          subst j
          simpa only [next, if_pos (le_refl L), if_neg (by omega : ¬L + 1 ≤ L), hlast]
            using hparent
      · intro j hj
        by_cases hjL : j ≤ L
        · simpa only [next, if_pos hjL] using horder j hjL
        · simpa only [next, if_neg hjL] using hq

end AnalyticPointBasis

namespace AnalyticProximityData

variable {N : ℕ} {c : AnalyticPointBasis N} (d : AnalyticProximityData c)

theorem analytic_parent_is_proximity_parent {q p : Fin N} (h : c.ParentRelation q p) :
    d.proximity.ParentRelation q p := by
  rw [← h.2]
  exact d.predecessor_mem q h.1

include d in
theorem top_child_unique {p q r : Fin N}
    (hqParent : c.ParentRelation q p) (hrParent : c.ParentRelation r p)
    (hq : c.multiplicity q = c.multiplicity c.root)
    (hr : c.multiplicity r = c.multiplicity c.root) : q = r := by
  apply d.proximity.top_multiplicity_child_unique
    (d.proximity.root_reachable_of_generation c.generation d.generation_decreases)
  · simpa only [d.multiplicity_eq, d.root_eq] using c.multiplicity_pos c.root
  · exact d.analytic_parent_is_proximity_parent hqParent
  · exact d.analytic_parent_is_proximity_parent hrParent
  · simpa only [d.multiplicity_eq, d.root_eq] using hq
  · simpa only [d.multiplicity_eq, d.root_eq] using hr

include d in
/-- A top-order child exhausts its parent's proximity inequality.
Since every recorded analytic germ has positive order, there can be no
other immediate child of that parent, even of smaller order. -/
theorem child_unique_of_top_child {p q r : Fin N}
    (hqParent : c.ParentRelation q p) (hrParent : c.ParentRelation r p)
    (hq : c.multiplicity q = c.multiplicity c.root) : q = r := by
  classical
  by_contra hqr
  let successors : Finset (Fin N) :=
    Finset.univ.filter fun z ↦ p ∈ d.proximity.parents z
  have hpair : c.multiplicity q + c.multiplicity r ≤
      ∑ z ∈ successors, c.multiplicity z := by
    calc
      c.multiplicity q + c.multiplicity r =
          ∑ z ∈ ({q, r} : Finset (Fin N)), c.multiplicity z := by simp [hqr]
      _ ≤ ∑ z ∈ successors, c.multiplicity z := by
        apply Finset.sum_le_sum_of_subset
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            d.analytic_parent_is_proximity_parent hqParent⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            d.analytic_parent_is_proximity_parent hrParent⟩
  have hbound : (∑ z ∈ successors, c.multiplicity z) ≤ c.multiplicity p := by
    simpa only [successors, d.multiplicity_eq] using d.proximity.proximity_inequality p
  have hp := c.multiplicity_le_root p
  have hr := c.multiplicity_pos r
  omega

/-- Every nonroot top-order point has exactly its immediate predecessor
as proximity parent. The exclusion of satellites is derived from the
nested-parent property and the proximity inequality. -/
theorem top_parents_eq_singleton_predecessor (q : Fin N) (hq : q ≠ c.root)
    (htop : c.multiplicity q = c.multiplicity c.root) :
    d.proximity.parents q = {c.predecessor q} := by
  have hnot := d.proximity.top_multiplicity_not_mem_satellitePoints_of_nested_parents
    c.generation d.generation_decreases d.nested_parents
    (by simpa only [d.multiplicity_eq, d.root_eq] using c.multiplicity_pos c.root)
    (q := q) (by simpa only [d.multiplicity_eq, d.root_eq] using htop)
  have hcard : (d.proximity.parents q).card = 1 := by
    rcases d.proximity.nonroot_parent_card q (by simpa only [d.root_eq] using hq) with h | h
    · exact h
    · exact (hnot (by simp [Numerical.ProximityCertificate.satellitePoints, h])).elim
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have heq : c.predecessor q = p := by
    have hmem := d.predecessor_mem q hq
    simpa only [hp, Finset.mem_singleton] using hmem
  simpa only [heq] using hp

include d in
private theorem covers_of_maximal_top_path
    (L : ℕ) (point : ℕ → Fin N) (hzero : point 0 = c.root)
    (hchain : ∀ j < L, c.ParentRelation (point (j + 1)) (point j))
    (horder : ∀ j ≤ L, c.multiplicity (point j) = c.multiplicity c.root)
    (hmax : ∀ q, c.multiplicity q = c.multiplicity c.root →
      c.generation q ≤ c.generation (point L)) :
    ∀ q, c.multiplicity q = c.multiplicity c.root → ∃ j ≤ L, point j = q := by
  intro q
  have hpath := c.root_ancestor q
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ ↦ ⟨0, Nat.zero_le L, hzero⟩
  | @head q p hparent _hpath ih =>
      intro hq
      obtain ⟨j, hj, hp⟩ := ih (c.predecessor_top_order hq hparent)
      by_cases hjlt : j < L
      · have hparent' : c.ParentRelation q (point j) := by rwa [hp]
        exact ⟨j + 1, by omega,
          (d.top_child_unique hparent' (hchain j hjlt) hq (horder _ (by omega))).symm⟩
      · have hjL : j = L := by omega
        have hgt := c.generation_decreases q hparent.1
        rw [hparent.2, ← hp, hjL] at hgt
        have hle := hmax q hq
        omega

include d in
/-- Choose a top-order point with largest generation, take its root
path, and use uniqueness of top-order children to prove that this path
contains every top-order point. -/
theorem exists_topOrderChain : Nonempty (AnalyticTopOrderChain c) := by
  classical
  let top : Finset (Fin N) := Finset.univ.filter fun q ↦ c.multiplicity q = c.multiplicity c.root
  have hnonempty : top.Nonempty := ⟨c.root, by simp [top]⟩
  obtain ⟨q, hqtop, hmax⟩ := top.exists_max_image c.generation hnonempty
  have hq : c.multiplicity q = c.multiplicity c.root := (Finset.mem_filter.mp hqtop).2
  obtain ⟨L, point, hzero, hlast, hchain, horder⟩ := c.exists_indexed_top_order_path q hq
  have hcover := d.covers_of_maximal_top_path L point hzero hchain horder
    (fun p hp ↦ by rw [hlast]; exact hmax p (by simp [top, hp]))
  refine ⟨⟨L + 1, by omega, point, hzero,
    (fun j hj ↦ hchain j (by omega)), (fun j hj ↦ horder j (by omega)), ?_⟩⟩
  intro p hp
  obtain ⟨j, hj, heq⟩ := hcover p hp
  exact ⟨j, by omega, heq⟩

/-- One choice of the chain whose existence was proved from proximity.
No chain data are additional arguments to this construction. -/
@[expose] noncomputable def topOrderChain : AnalyticTopOrderChain c :=
  Classical.choice d.exists_topOrderChain

end AnalyticProximityData

namespace AnalyticTopOrderChain

variable {N : ℕ} {c : AnalyticPointBasis N} (S : AnalyticTopOrderChain c)

theorem point_injective : Function.Injective (fun i : Fin S.length ↦ S.point i) := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero S.length_pos.ne'
  have hgen : StrictMono (fun i : Fin (a + 1) ↦ c.generation (S.point i)) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hparent := S.chain i (by omega)
    have hlt := c.generation_decreases _ hparent.1
    rw [hparent.2] at hlt
    exact hlt
  intro i j hij
  have heq : (⟨i, by omega⟩ : Fin (a + 1)) = ⟨j, by omega⟩ :=
    hgen.injective (congrArg c.generation hij)
  exact Fin.ext (congrArg (fun k : Fin (a + 1) ↦ k.val) heq)

theorem range_point : Set.range (fun i : Fin S.length ↦ S.point i) =
    {q | c.multiplicity q = c.multiplicity c.root} := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    exact S.order i i.isLt
  · intro hq
    obtain ⟨j, hj, heq⟩ := S.covers q hq
    exact ⟨⟨j, hj⟩, heq⟩

/-- The number of root-order entries is the constructed chain length. -/
theorem valueCount_eq_length :
    Numerical.MultiplicityCounts.valueCount c.multiplicity (c.multiplicity c.root) = S.length := by
  classical
  have hset : Finset.univ.filter (fun q ↦ c.multiplicity q = c.multiplicity c.root) =
      Finset.univ.image (fun i : Fin S.length ↦ S.point i) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hq
      obtain ⟨j, hj, heq⟩ := S.covers q hq
      exact ⟨⟨j, hj⟩, heq⟩
    · rintro ⟨i, rfl⟩
      exact S.order i i.isLt
  rw [Numerical.MultiplicityCounts.valueCount, hset,
    Finset.card_image_of_injective _ S.point_injective]
  simp

theorem successor_parents_eq_singleton
    (d : AnalyticProximityData c) (j : ℕ) (hj : j + 1 < S.length) :
    d.proximity.parents (S.point (j + 1)) = {S.point j} := by
  have hparent := S.chain j hj
  rw [d.top_parents_eq_singleton_predecessor _ hparent.1 (S.order _ hj), hparent.2]

theorem child_eq_next_before_terminal
    (d : AnalyticProximityData c) (j : ℕ) (hj : j + 1 < S.length)
    (q : Fin N) (hq : c.ParentRelation q (S.point j)) : q = S.point (j + 1) :=
  (d.child_unique_of_top_child (S.chain j hj) hq (S.order _ hj)).symm

/-- The supplied compatibility is required only on edges whose child
has root order and exactly one proximity parent. Nonsatellite status alone, as an
abstract finite relation, does not identify analytic coordinate germs. -/
theorem free_chart_step
    (d : AnalyticProximityData c)
    (hfreeCoordinates : ∀ q, q ≠ c.root →
      c.multiplicity q = c.multiplicity c.root →
      d.proximity.parents q = {c.predecessor q} →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) =
        c.germ (c.predecessor q))
    (j : ℕ) (hj : j + 1 < S.length) :
    (pointBlowupChartGerm (c.chartCenter (S.point (j + 1)))).pullbackRingHom
      (c.germ (S.point j)) = coordinate (1 : Fin 2) ^ c.multiplicity c.root *
        c.germ (S.point (j + 1)) := by
  have hparent := S.chain j hj
  have h := c.transform_identity (S.point (j + 1)) hparent.1
  rw [hfreeCoordinates _ hparent.1 (S.order _ hj)
    (d.top_parents_eq_singleton_predecessor _ hparent.1 (S.order _ hj)),
    hparent.2, S.order j (by omega)] at h
  exact h

/-- Centers of the actual consecutive free charts on the extracted chain. -/
@[expose] noncomputable def chartCenters (j : ℕ) : ℂ := c.chartCenter (S.point (j + 1))

/-- The germ at each chain point after the proved remaining-tail shear. -/
@[expose] noncomputable def straightenedGerm (j : ℕ) : Germ 2 :=
  straightenedFreeChain S.chartCenters (S.length - 1) (fun k ↦ c.germ (S.point k)) j

theorem straightenedGerm_root : S.straightenedGerm 0 =
    (freeChainStraighteningEquiv S.chartCenters (S.length - 1)).forward.pullbackRingHom
      (c.germ c.root) := by
  simp only [straightenedGerm, straightenedFreeChain_root, S.point_zero]

theorem straightenedGerm_final : S.straightenedGerm (S.length - 1) =
    c.germ (S.point (S.length - 1)) := by
  exact straightenedFreeChain_final _ _ _

theorem straightenedGerm_exact_order (j : ℕ) (hj : j < S.length) :
    S.straightenedGerm j ∈ maximalIdeal 2 ^ c.multiplicity c.root ∧
      S.straightenedGerm j ∉ maximalIdeal 2 ^ (c.multiplicity c.root + 1) := by
  have heq := S.order j hj
  constructor
  · apply (straightenedFreeChain_mem_pow_iff _ _ _ _ _).mpr
    simpa only [heq] using c.germ_mem (S.point j)
  · apply (straightenedFreeChain_mem_pow_iff _ _ _ _ _).not.mpr
    simpa only [heq] using c.germ_not_mem_succ (S.point j)

/-- Straightening of the extracted chain gives actual zero-center
identities, not a separately stipulated normalized chain. -/
theorem straightenedGerm_step
    (d : AnalyticProximityData c)
    (hfreeCoordinates : ∀ q, q ≠ c.root →
      c.multiplicity q = c.multiplicity c.root →
      d.proximity.parents q = {c.predecessor q} →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) =
        c.germ (c.predecessor q))
    (j : ℕ) (hj : j + 1 < S.length) :
    (pointBlowupChartGerm 0).pullbackRingHom (S.straightenedGerm j) =
      coordinate (1 : Fin 2) ^ c.multiplicity c.root * S.straightenedGerm (j + 1) := by
  exact straightenedFreeChain_step S.chartCenters (S.length - 1)
    (fun k ↦ c.germ (S.point k)) j (c.multiplicity c.root) (by omega)
    (S.free_chart_step d hfreeCoordinates j hj)

/-- The number of top-order points supplies the coefficient bound once
the root is prepared in the analytically constructed straightening
coordinates. The free chain, its zero-center normalization, and its
length are no longer additional assumptions. -/
theorem coefficient_mem_pow_of_straightened_preparation
    (d : AnalyticProximityData c)
    (hfreeCoordinates : ∀ q, q ≠ c.root →
      c.multiplicity q = c.multiplicity c.root →
      d.proximity.parents q = {c.predecessor q} →
      (c.sourceCoordinates q).forward.pullbackRingHom (c.germ (c.predecessor q)) =
        c.germ (c.predecessor q))
    (P : Polynomial (Germ 1)) (u : Germ 2) (hu : IsUnit u)
    (hprepared : (freeChainStraighteningEquiv S.chartCenters (S.length - 1)).forward.pullbackRingHom
      (c.germ c.root) = firstCoordinatePolynomialEvaluation P * u)
    (i : ℕ) (hi : i ≤ c.multiplicity c.root) :
    P.coeff i ∈ maximalIdeal 1 ^
      (Numerical.MultiplicityCounts.valueCount c.multiplicity (c.multiplicity c.root) *
        (c.multiplicity c.root - i)) := by
  rw [S.valueCount_eq_length]
  have hlen : S.length - 1 + 1 = S.length := Nat.sub_add_cancel S.length_pos
  have h := coefficient_mem_pow_of_prepared_freeChain (S.length - 1)
    (c.multiplicity c.root) P S.straightenedGerm u hu
    (S.straightenedGerm_root.trans hprepared)
    (fun j hj ↦ S.straightenedGerm_step d hfreeCoordinates j (by omega))
    (S.straightenedGerm_exact_order _ (by have := S.length_pos; omega)).1 i hi
  simpa only [hlen] using h

end AnalyticTopOrderChain

end OnLeConjecture.Analytic
