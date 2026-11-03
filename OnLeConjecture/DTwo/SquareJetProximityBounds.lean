/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Numerical.ProximityReduction
public import OnLeConjecture.Numerical.PointBasisCountIdentities
public import Mathlib.Tactic.Push
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Two entry-one points forced by a satellite in the square branch

If the origin is the unique entry-two point and the proximity branch
count is one, a satellite point and one of its nonroot parents are two
distinct entry-one points. The generation function rules out self-parents.
The identification of the proximity branch count with analytic branches
remains an input of the resolution theorem.
-/

public section

namespace OnLeConjecture.DTwo

open Numerical
open scoped BigOperators

/-- A branch count one with root entry two forces an entry-one satellite,
without any assumption on the number of entry-two points. -/
theorem one_entry_of_root_two_and_one_branch
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p) (hbranch : c.branchCount = 1) :
    1 ≤ c.multiplicityCount 1 := by
  classical
  have hsat : c.satelliteMultiplicity = 1 := by
    have h := c.branchCount_add_satelliteMultiplicity
    rw [hroot, hbranch] at h
    omega
  have hnonempty : c.satellitePoints.Nonempty := by
    by_contra hn
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [ProximityCertificate.satelliteMultiplicity, hempty, Finset.sum_empty] at hsat
    omega
  obtain ⟨q, hq⟩ := hnonempty
  have hle : c.multiplicity q ≤ c.satelliteMultiplicity :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq
  have hqone : c.multiplicity q = 1 := by have hpos := hpositive q; omega
  exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqone⟩⟩

theorem two_one_entries_of_unique_two_and_one_branch
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hcount : MultiplicityCounts.valueCount c.multiplicity 2 = 1)
    (hbranch : c.branchCount = 1) :
    2 ≤ MultiplicityCounts.valueCount c.multiplicity 1 := by
  classical
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hrootmem : c.root ∈ Finset.univ.filter (fun p => c.multiplicity p = 2) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hroot]
  have hother (p : α) (hp : p ≠ c.root) : c.multiplicity p = 1 := by
    have hle : c.multiplicity p ≤ 2 := by
      simpa only [hroot] using c.multiplicity_le_root hconnected p
    have hne : c.multiplicity p ≠ 2 := by
      intro htwo
      have hpmem : p ∈ Finset.univ.filter (fun q => c.multiplicity q = 2) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, htwo]
      apply hp
      exact Finset.card_le_one.mp (le_of_eq hcount) p hpmem c.root hrootmem
    have hpos := hpositive p
    omega
  have hsat : c.satelliteMultiplicity = 1 := by
    have h := c.branchCount_add_satelliteMultiplicity
    rw [hroot, hbranch] at h
    omega
  have hnonempty : c.satellitePoints.Nonempty := by
    by_contra hn
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [ProximityCertificate.satelliteMultiplicity, hempty, Finset.sum_empty] at hsat
    omega
  obtain ⟨q, hq⟩ := hnonempty
  have hqroot : q ≠ c.root := fun heq => c.root_not_mem_satellitePoints (heq ▸ hq)
  have hqcard : (c.parents q).card = 2 := (Finset.mem_filter.mp hq).2
  have hparent : ∃ p ∈ c.parents q, p ≠ c.root := by
    by_contra hn
    push Not at hn
    have hsubset : c.parents q ⊆ {c.root} := by
      intro p hp
      exact Finset.mem_singleton.mpr (hn p hp)
    have hle := Finset.card_le_card hsubset
    simp only [Finset.card_singleton, hqcard] at hle
    omega
  obtain ⟨p, hp, hproot⟩ := hparent
  have hpq : p ≠ q := by
    have hlt := hdecrease hp
    intro heq
    rw [heq] at hlt
    omega
  have hsubset : {p, q} ⊆ Finset.univ.filter (fun z => c.multiplicity z = 1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother z hproot⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother z hqroot⟩
  have hle := Finset.card_le_card hsubset
  simpa only [Finset.card_pair hpq, MultiplicityCounts.valueCount] using hle

/-- The square-jet genus relation and genuine proximity data force total
multiplicity at least four, including the single entry-two case. -/
theorem square_jet_totalMultiplicity_ge_four
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (k : ℕ) (hk : 3 ≤ k) (hbranch : 0 < c.branchCount)
    (hgenus : 2 * c.multiplicityCount 2 + 2 = k + c.branchCount) :
    4 ≤ c.totalMultiplicity := by
  classical
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hbounded (p : α) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsum := c.totalMultiplicity_eq_two_mul_count_two_add_count_one hpositive hbounded
  have hcountPos : 0 < c.multiplicityCount 2 := by
    apply Finset.card_pos.mpr
    exact ⟨c.root, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot⟩⟩
  by_cases hcount : c.multiplicityCount 2 = 1
  · have hb : c.branchCount = 1 := by omega
    have hones := two_one_entries_of_unique_two_and_one_branch
      c generation hdecrease hroot hpositive hcount hb
    change 2 ≤ c.multiplicityCount 1 at hones
    omega
  · omega

/-- The polar and knot inequalities exclude critical intersection four or
higher. All sums are those of the supplied proximity certificate. -/
theorem square_jet_maximal_critical_intersection_le_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (k : ℕ) (hk : 3 ≤ k) (hbranch : 0 < c.branchCount)
    (hgenus : 2 * c.multiplicityCount 2 + 2 = k + c.branchCount)
    (t I : ℕ) (htransverse : c.totalMultiplicity ≤ t)
    (hpolar : I * (t - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    I ≤ 3 := by
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hbounded (p : α) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsum := c.totalMultiplicity_eq_two_mul_count_two_add_count_one hpositive hbounded
  have hsquares := c.squareMultiplicity_eq_four_mul_count_two_add_count_one hpositive hbounded
  have hfour := square_jet_totalMultiplicity_ge_four
    c generation hdecrease hroot hpositive k hk hbranch hgenus
  have hsquareBound : c.squareMultiplicity ≤ 2 * c.totalMultiplicity := by omega
  by_contra hn
  have hI : 4 ≤ I := by omega
  have hprod : 4 * (t - 1) ≤ I * (t - 1) := Nat.mul_le_mul_right (t - 1) hI
  omega

/-- For exponent three and one branch, intersection three contradicts
the two entry-one points forced by proximity. -/
theorem square_jet_exponent_three_critical_intersection_ne_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (generation : α → ℕ)
    (hdecrease : ∀ {q p}, c.ParentRelation q p → generation p < generation q)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbranch : c.branchCount = 1)
    (hgenus : 2 * c.multiplicityCount 2 + 2 = 3 + c.branchCount)
    (t I : ℕ) (htransverse : c.totalMultiplicity ≤ t)
    (hpolar : I * (t - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    I ≠ 3 := by
  have hcount : c.multiplicityCount 2 = 1 := by omega
  have hones := two_one_entries_of_unique_two_and_one_branch
    c generation hdecrease hroot hpositive hcount hbranch
  change 2 ≤ c.multiplicityCount 1 at hones
  have hconnected := c.root_reachable_of_generation generation hdecrease
  have hbounded (p : α) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsum := c.totalMultiplicity_eq_two_mul_count_two_add_count_one hpositive hbounded
  have hsquares := c.squareMultiplicity_eq_four_mul_count_two_add_count_one hpositive hbounded
  intro hI
  rw [hI] at hpolar
  omega

/-- The genus relation and positive branch count put the prepared
exponent below the total multiplicity. No parity restriction is needed. -/
theorem quadratic_exponent_le_totalMultiplicity
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α)
    (hconnected : ∀ q, Relation.ReflTransGen c.ParentRelation q c.root)
    (hroot : c.multiplicity c.root = 2)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (k : ℕ) (hbranch : 0 < c.branchCount)
    (hgenus : 2 * c.multiplicityCount 2 + 2 = k + c.branchCount) :
    k ≤ c.totalMultiplicity := by
  have hbounded (p : α) : c.multiplicity p ≤ 2 := by
    simpa only [hroot] using c.multiplicity_le_root hconnected p
  have hsum := c.totalMultiplicity_eq_two_mul_count_two_add_count_one hpositive hbounded
  have hbranchsum := c.branchCount_add_satelliteMultiplicity
  rw [hroot] at hbranchsum
  by_cases hb : c.branchCount = 1
  · have hones := one_entry_of_root_two_and_one_branch c hroot hpositive hb
    omega
  · omega

end OnLeConjecture.DTwo
