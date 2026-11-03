/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Proximity combinatorics for a point basis

This module proves the finite sum identity behind the branch count formula
for a point basis. Every point other than the root is proximate to one or two
earlier points. A point with two parents is called satellite. The sum of the
excesses equals the root multiplicity minus the sum of the multiplicities at
the satellite points.
-/

public section

namespace OnLeConjecture.Numerical

open scoped BigOperators

/-- Finite proximity data with the proximity inequalities satisfied by a
point basis. The finset `parents q` lists the points to which `q` is
proximate. -/
structure ProximityCertificate (α : Type*) [Fintype α] [DecidableEq α] where
  multiplicity : α → ℕ
  root : α
  parents : α → Finset α
  root_has_no_parent : parents root = ∅
  nonroot_parent_card : ∀ q, q ≠ root →
    (parents q).card = 1 ∨ (parents q).card = 2
  proximity_inequality : ∀ p,
    (∑ q with p ∈ parents q, multiplicity q) ≤ multiplicity p

namespace ProximityCertificate

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The points which are proximate to two earlier points. -/
@[expose]
def satellitePoints (c : ProximityCertificate α) : Finset α :=
  Finset.univ.filter fun q ↦ (c.parents q).card = 2

/-- The sum of all entries of the point basis. -/
@[expose]
def totalMultiplicity (c : ProximityCertificate α) : ℕ :=
  ∑ q, c.multiplicity q

/-- The sum of the entries at satellite points. -/
@[expose]
def satelliteMultiplicity (c : ProximityCertificate α) : ℕ :=
  ∑ q ∈ c.satellitePoints, c.multiplicity q

/-- The contribution to the proximity inequality at a point. -/
@[expose]
def successorMultiplicity (c : ProximityCertificate α) (p : α) : ℕ :=
  ∑ q with p ∈ c.parents q, c.multiplicity q

/-- The excess of the point basis at a point. -/
@[expose]
def excess (c : ProximityCertificate α) (p : α) : ℕ :=
  c.multiplicity p - c.successorMultiplicity p

/-- The sum of all excesses. For a consistent cluster this is the number of
branches of a general member. -/
@[expose]
def branchCount (c : ProximityCertificate α) : ℕ :=
  ∑ p, c.excess p

theorem root_not_mem_satellitePoints (c : ProximityCertificate α) :
    c.root ∉ c.satellitePoints := by
  simp [satellitePoints, c.root_has_no_parent]

private theorem multiplicity_mul_parent_card
    (c : ProximityCertificate α) (q : α) :
    c.multiplicity q * (c.parents q).card =
      (if q = c.root then 0 else c.multiplicity q) +
        (if q ∈ c.satellitePoints then c.multiplicity q else 0) := by
  by_cases hroot : q = c.root
  · subst q
    simp [c.root_has_no_parent, c.root_not_mem_satellitePoints]
  · rcases c.nonroot_parent_card q hroot with hone | htwo
    · have hnotSatellite : q ∉ c.satellitePoints := by
        simp [satellitePoints, hone]
      simp [hroot, hone, hnotSatellite]
    · have hsatellite : q ∈ c.satellitePoints := by
        simp [satellitePoints, htwo]
      simp [hroot, htwo, hsatellite, mul_two]

omit [Fintype α] [DecidableEq α] in
private theorem finset_sum_commute
    (s t : Finset α) (f : α → α → ℕ) :
    (∑ a ∈ s, ∑ b ∈ t, f a b) =
      ∑ b ∈ t, ∑ a ∈ s, f a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      rw [ih]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_insert ha]

/-- Counting the proximity incidences by their source or by their target
gives the same sum. -/
theorem sum_successorMultiplicity (c : ProximityCertificate α) :
    ∑ p, c.successorMultiplicity p =
      ∑ q, c.multiplicity q * (c.parents q).card := by
  classical
  calc
    ∑ p, c.successorMultiplicity p =
        ∑ p, ∑ q, if p ∈ c.parents q then c.multiplicity q else 0 := by
      simp only [successorMultiplicity, Finset.sum_filter]
    _ = ∑ q, ∑ p,
        if p ∈ c.parents q then c.multiplicity q else 0 := by
      exact finset_sum_commute Finset.univ Finset.univ fun p q ↦
        if p ∈ c.parents q then c.multiplicity q else 0
    _ = ∑ q, c.multiplicity q * (c.parents q).card := by
      apply Finset.sum_congr rfl
      intro q _hq
      simp [mul_comm]

/-- The total proximity contribution is the sum of the nonroot entries plus
one further copy of every satellite entry. -/
theorem sum_successorMultiplicity_eq
    (c : ProximityCertificate α) :
    ∑ p, c.successorMultiplicity p =
      (∑ q, if q = c.root then 0 else c.multiplicity q) +
        c.satelliteMultiplicity := by
  rw [c.sum_successorMultiplicity]
  calc
    ∑ q, c.multiplicity q * (c.parents q).card =
        ∑ q, ((if q = c.root then 0 else c.multiplicity q) +
          (if q ∈ c.satellitePoints then c.multiplicity q else 0)) := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact c.multiplicity_mul_parent_card q
    _ = (∑ q, if q = c.root then 0 else c.multiplicity q) +
        ∑ q, if q ∈ c.satellitePoints then c.multiplicity q else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ q, if q = c.root then 0 else c.multiplicity q) +
        c.satelliteMultiplicity := by
      simp [satelliteMultiplicity]

private theorem totalMultiplicity_eq_root_add_nonroot
    (c : ProximityCertificate α) :
    c.totalMultiplicity = c.multiplicity c.root +
      ∑ q, if q = c.root then 0 else c.multiplicity q := by
  classical
  calc
    c.totalMultiplicity = ∑ q,
        ((if q = c.root then c.multiplicity q else 0) +
          (if q = c.root then 0 else c.multiplicity q)) := by
      rw [totalMultiplicity]
      apply Finset.sum_congr rfl
      intro q _hq
      by_cases hq : q = c.root <;> simp [hq]
    _ = (∑ q, if q = c.root then c.multiplicity q else 0) +
        ∑ q, if q = c.root then 0 else c.multiplicity q := by
      rw [Finset.sum_add_distrib]
    _ = c.multiplicity c.root +
        ∑ q, if q = c.root then 0 else c.multiplicity q := by
      rw [Fintype.sum_ite_eq']

private theorem branchCount_cast (c : ProximityCertificate α) :
    (c.branchCount : ℤ) =
      (c.totalMultiplicity : ℤ) -
        (∑ p, c.successorMultiplicity p : ℕ) := by
  rw [branchCount, totalMultiplicity]
  push_cast
  calc
    ∑ x, ↑(c.excess x) =
        ∑ x, ((c.multiplicity x : ℤ) - c.successorMultiplicity x) := by
      apply Finset.sum_congr rfl
      intro p _hp
      have hle : c.successorMultiplicity p ≤ c.multiplicity p :=
        c.proximity_inequality p
      exact Int.ofNat_sub hle
    _ = ∑ x, (c.multiplicity x : ℤ) -
        ∑ x, (c.successorMultiplicity x : ℤ) := by
      rw [Finset.sum_sub_distrib]

/-- The branch count plus the satellite multiplicity equals the root
multiplicity. -/
theorem branchCount_add_satelliteMultiplicity
    (c : ProximityCertificate α) :
    c.branchCount + c.satelliteMultiplicity = c.multiplicity c.root := by
  have hbranch := c.branchCount_cast
  have hsuccessor := c.sum_successorMultiplicity_eq
  have htotal := c.totalMultiplicity_eq_root_add_nonroot
  have hsuccessorInteger :
      ((∑ p, c.successorMultiplicity p : ℕ) : ℤ) =
        (∑ q, if q = c.root then 0 else c.multiplicity q : ℕ) +
          c.satelliteMultiplicity := by
    exact_mod_cast hsuccessor
  have htotalInteger : (c.totalMultiplicity : ℤ) =
      c.multiplicity c.root +
        (∑ q, if q = c.root then 0 else c.multiplicity q : ℕ) := by
    exact_mod_cast htotal
  have hinteger :
      ((c.branchCount + c.satelliteMultiplicity : ℕ) : ℤ) =
        c.multiplicity c.root := by
    push_cast
    rw [hbranch, hsuccessorInteger, htotalInteger]
    ring
  exact_mod_cast hinteger

/-- If the root entry is three, the satellite multiplicity is at most three
and determines the branch count. -/
theorem branchCount_eq_three_sub_satelliteMultiplicity
    (c : ProximityCertificate α)
    (hroot : c.multiplicity c.root = 3) :
    c.branchCount = 3 - c.satelliteMultiplicity := by
  have hsum := c.branchCount_add_satelliteMultiplicity
  rw [hroot] at hsum
  omega

/-- If the root entry is three and the branch count is positive, the
satellite multiplicity is at most two. -/
theorem satelliteMultiplicity_le_two_of_root_three
    (c : ProximityCertificate α)
    (hroot : c.multiplicity c.root = 3)
    (hbranches : 1 ≤ c.branchCount) :
    c.satelliteMultiplicity ≤ 2 := by
  have hsum := c.branchCount_add_satelliteMultiplicity
  omega

end ProximityCertificate

end OnLeConjecture.Numerical
