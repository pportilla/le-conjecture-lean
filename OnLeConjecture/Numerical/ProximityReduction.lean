/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.PointBasisCountIdentities
public import OnLeConjecture.Numerical.PointBasis
public import OnLeConjecture.Numerical.SmallPointBasisCounts
public import OnLeConjecture.Numerical.RootBound
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Order

/-!
# Reduction bounds from proximity data

This module derives the two point basis bounds directly from a proximity
certificate when every point is connected to the root by the parent relation.
It then constructs the numerical reduction certificate used in the order
bound.
-/

public section

namespace OnLeConjecture.Numerical

open scoped BigOperators

namespace ProximityCertificate

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The parent relation points from a point to one of the points to which it
is proximate. -/
@[expose]
def ParentRelation (c : ProximityCertificate α) (q p : α) : Prop :=
  p ∈ c.parents q

/-- An entry is at most the entry of each of its parents. -/
theorem multiplicity_le_of_parent
    (c : ProximityCertificate α) {q p : α}
    (hparent : c.ParentRelation q p) :
    c.multiplicity q ≤ c.multiplicity p := by
  have hleSuccessor : c.multiplicity q ≤ c.successorMultiplicity p := by
    rw [successorMultiplicity]
    apply Finset.single_le_sum
      (fun r _hr ↦ Nat.zero_le (c.multiplicity r))
    change p ∈ c.parents q at hparent
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hparent⟩
  exact hleSuccessor.trans (c.proximity_inequality p)

/-- A generation function that decreases along every parent relation proves
that every point reaches the root. -/
theorem root_reachable_of_generation
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p →
      generation p < generation q) :
    ∀ q, Relation.ReflTransGen c.ParentRelation q c.root := by
  intro q
  generalize hn : generation q = n
  induction n using Nat.strong_induction_on generalizing q with
  | h n ih =>
      by_cases hroot : q = c.root
      · subst q
        exact Relation.ReflTransGen.refl
      · have hparents : (c.parents q).Nonempty := by
          rcases c.nonroot_parent_card q hroot with hone | htwo
          · exact Finset.card_pos.mp (by omega)
          · exact Finset.card_pos.mp (by omega)
        obtain ⟨p, hp⟩ := hparents
        have hpRelation : c.ParentRelation q p := hp
        have hpLower : generation p < n := by
          rw [← hn]
          exact hdecrease hpRelation
        exact Relation.ReflTransGen.head hpRelation
          (ih (generation p) hpLower p rfl)

/-- If a point reaches the root through parent relations, its entry is at
most the root entry. -/
theorem multiplicity_le_root_of_reflTransGen
    (c : ProximityCertificate α) {q : α}
    (hpath : Relation.ReflTransGen c.ParentRelation q c.root) :
    c.multiplicity q ≤ c.multiplicity c.root := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | @head q p hparent _hpath ih =>
      exact (c.multiplicity_le_of_parent hparent).trans ih

/-- Root reachability supplies the usual bound of every point basis entry by
the root entry. -/
theorem multiplicity_le_root
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root) (q : α) :
    c.multiplicity q ≤ c.multiplicity c.root :=
  c.multiplicity_le_root_of_reflTransGen (hconnected q)

/-- A parent of a point whose entry equals the root entry has the same
entry. -/
theorem parent_multiplicity_eq_root_of_child_eq_root
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    {q p : α} (hq : c.multiplicity q = c.multiplicity c.root)
    (hparent : c.ParentRelation q p) :
    c.multiplicity p = c.multiplicity c.root := by
  apply le_antisymm
  · exact c.multiplicity_le_root hconnected p
  · rw [← hq]
    exact c.multiplicity_le_of_parent hparent

/-- A point has at most one child whose entry equals the positive root
entry. -/
theorem top_multiplicity_child_unique
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    (hrootPositive : 0 < c.multiplicity c.root)
    {p q r : α}
    (hqParent : c.ParentRelation q p)
    (hrParent : c.ParentRelation r p)
    (hq : c.multiplicity q = c.multiplicity c.root)
    (hr : c.multiplicity r = c.multiplicity c.root) :
    q = r := by
  by_contra hqr
  let successors : Finset α :=
    Finset.univ.filter fun s ↦ p ∈ c.parents s
  have hqMem : q ∈ successors := by
    simp only [successors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqParent
  have hrMem : r ∈ successors := by
    simp only [successors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrParent
  have hpair : 2 * c.multiplicity c.root ≤
      ∑ s ∈ successors, c.multiplicity s := by
    calc
      2 * c.multiplicity c.root =
          c.multiplicity q + c.multiplicity r := by
        rw [hq, hr]
        omega
      _ = ∑ s ∈ ({q, r} : Finset α), c.multiplicity s := by
        simp [hqr]
      _ ≤ ∑ s ∈ successors, c.multiplicity s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs
          simp only [Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact hqMem
          · exact hrMem
        · intro s _hs _hnot
          exact Nat.zero_le (c.multiplicity s)
  have hsuccessor :
      (∑ s ∈ successors, c.multiplicity s) ≤ c.multiplicity p := by
    simpa only [successors, successorMultiplicity] using
      c.proximity_inequality p
  have hpRoot : c.multiplicity p ≤ c.multiplicity c.root :=
    c.multiplicity_le_root hconnected p
  omega

/-- If the two parents of every satellite point are nested in the parent
relation, a point with root multiplicity cannot be satellite. -/
theorem top_multiplicity_not_mem_satellitePoints_of_nested_parents
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p →
      generation p < generation q)
    (hnested : ∀ q, (c.parents q).card = 2 →
      ∃ p r, c.ParentRelation q p ∧ c.ParentRelation q r ∧
        c.ParentRelation p r)
    (hrootPositive : 0 < c.multiplicity c.root)
    {q : α} (hq : c.multiplicity q = c.multiplicity c.root) :
    q ∉ c.satellitePoints := by
  intro hsatellite
  have hcard : (c.parents q).card = 2 := by
    change q ∈ Finset.univ.filter
      (fun r ↦ (c.parents r).card = 2) at hsatellite
    exact (Finset.mem_filter.mp hsatellite).2
  obtain ⟨p, r, hqp, hqr, hpr⟩ := hnested q hcard
  let hconnected := c.root_reachable_of_generation generation hdecrease
  have hp : c.multiplicity p = c.multiplicity c.root :=
    c.parent_multiplicity_eq_root_of_child_eq_root hconnected hq hqp
  have hqpEq : q = p :=
    c.top_multiplicity_child_unique hconnected hrootPositive
      hqr hpr hq hp
  have hstrict := hdecrease hqp
  rw [hqpEq] at hstrict
  omega

/-- The root entry is at most the total point basis sum. -/
theorem root_multiplicity_le_totalMultiplicity
    (c : ProximityCertificate α) :
    c.multiplicity c.root ≤ c.totalMultiplicity := by
  rw [totalMultiplicity]
  exact Finset.single_le_sum
    (fun q _hq ↦ Nat.zero_le (c.multiplicity q))
    (Finset.mem_univ c.root)

/-- The square sum contains the square of the root entry. -/
theorem root_multiplicity_sq_le_squareMultiplicity
    (c : ProximityCertificate α) :
    c.multiplicity c.root ^ 2 ≤ c.squareMultiplicity := by
  change c.multiplicity c.root ^ 2 ≤
    ∑ q, c.multiplicity q ^ 2
  exact Finset.single_le_sum
    (fun q _hq ↦ Nat.zero_le (c.multiplicity q ^ 2))
    (Finset.mem_univ c.root)

/-- A root entry at least two and the global estimate force the transverse
parameter to be at least two. -/
theorem two_le_parameter_of_global_estimate
    (c : ProximityCertificate α) (m : ℕ)
    (htwo : 2 ≤ c.multiplicity c.root)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m) :
    2 ≤ m := by
  have hfour : 4 ≤ c.multiplicity c.root ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul htwo htwo
  have hrootSquare := c.root_multiplicity_sq_le_squareMultiplicity
  have hrootTotal := c.root_multiplicity_le_totalMultiplicity
  omega

/-- If every point reaches the root, the square sum is at most the root entry
times the total sum. -/
theorem squareMultiplicity_le_root_mul_totalMultiplicity
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root) :
    c.squareMultiplicity ≤
      c.multiplicity c.root * c.totalMultiplicity := by
  change (∑ q, c.multiplicity q ^ 2) ≤
    c.multiplicity c.root * ∑ q, c.multiplicity q
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _hq
  rw [pow_two]
  exact Nat.mul_le_mul_right _ (c.multiplicity_le_root hconnected q)

/-- Connected proximity data indexed by `Fin N` determine the point basis
certificate used by the case reductions. -/
@[expose]
def toPointBasisCertificate {N : ℕ}
    (c : ProximityCertificate (Fin N))
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root) :
    PointBasisCertificate N where
  multiplicity := c.multiplicity
  root := c.root
  d := c.multiplicity c.root
  root_multiplicity := rfl
  multiplicity_le_root := c.multiplicity_le_root hconnected

theorem toPointBasisCertificate_S {N : ℕ}
    (c : ProximityCertificate (Fin N))
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root) :
    (c.toPointBasisCertificate hconnected).S = c.totalMultiplicity := by
  rfl

theorem toPointBasisCertificate_M {N : ℕ}
    (c : ProximityCertificate (Fin N))
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root) :
    (c.toPointBasisCertificate hconnected).M = c.squareMultiplicity := by
  rfl

theorem toPointBasisCertificate_multiplicityCount {N : ℕ}
    (c : ProximityCertificate (Fin N))
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root) (r : ℕ) :
    (c.toPointBasisCertificate hconnected).multiplicityCount r =
      c.multiplicityCount r := by
  simp only [PointBasisCertificate.multiplicityCount,
    ProximityCertificate.multiplicityCount, MultiplicityCounts.valueCount,
    toPointBasisCertificate]
  apply congrArg Finset.card
  ext p
  rfl

/-- Proximity data connected to the root and the geometric estimates produce
the numerical certificate used by the reduction theorem. -/
def reductionCertificate
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    (m n : ℕ)
    (htwo : 2 ≤ c.multiplicity c.root)
    (hbranch : 1 ≤ c.branchCount)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hn : c.multiplicity c.root ≤ n)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    ReductionCertificate where
  d := c.multiplicity c.root
  M := c.squareMultiplicity
  S := c.totalMultiplicity
  m := m
  n := n
  b := c.branchCount
  two_le_d := htwo
  d_le_S := c.root_multiplicity_le_totalMultiplicity
  b_positive := hbranch
  M_le_dS := c.squareMultiplicity_le_root_mul_totalMultiplicity hconnected
  m_at_least_two := c.two_le_parameter_of_global_estimate m htwo hglobal
  global_estimate := hglobal
  d_le_n := hn
  polar_estimate := hpolar

/-- The reduction estimates on connected proximity data force the root entry
to be at most four. -/
theorem root_multiplicity_le_four_of_estimates
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    (m n : ℕ)
    (htwo : 2 ≤ c.multiplicity c.root)
    (hbranch : 1 ≤ c.branchCount)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hn : c.multiplicity c.root ≤ n)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    c.multiplicity c.root ≤ 4 := by
  exact (c.reductionCertificate hconnected m n htwo hbranch hglobal hn
    hpolar).d_le_four

/-- Under the same hypotheses, the root entry is two, three, or four. -/
theorem root_multiplicity_eq_two_or_three_or_four_of_estimates
    (c : ProximityCertificate α)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    (m n : ℕ)
    (htwo : 2 ≤ c.multiplicity c.root)
    (hbranch : 1 ≤ c.branchCount)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hn : c.multiplicity c.root ≤ n)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    c.multiplicity c.root = 2 ∨
      c.multiplicity c.root = 3 ∨ c.multiplicity c.root = 4 := by
  exact ReductionCertificate.d_eq_two_or_three_or_four
    (c.reductionCertificate hconnected m n htwo hbranch hglobal hn
      hpolar)

/-- A decreasing generation function supplies the connectivity needed by the
root bound. -/
theorem root_multiplicity_eq_two_or_three_or_four_of_generation
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p →
      generation p < generation q)
    (m n : ℕ)
    (htwo : 2 ≤ c.multiplicity c.root)
    (hbranch : 1 ≤ c.branchCount)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hn : c.multiplicity c.root ≤ n)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    c.multiplicity c.root = 2 ∨
      c.multiplicity c.root = 3 ∨ c.multiplicity c.root = 4 := by
  exact c.root_multiplicity_eq_two_or_three_or_four_of_estimates
    (c.root_reachable_of_generation generation hdecrease)
    m n htwo hbranch hglobal hn hpolar

end ProximityCertificate

end OnLeConjecture.Numerical
