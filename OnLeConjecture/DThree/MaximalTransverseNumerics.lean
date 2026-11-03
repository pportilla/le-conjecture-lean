/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.Numerical
public import OnLeConjecture.Numerical.ProximityReduction
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# The maximal transverse intersection in order three

This module combines the point basis counts with the global and polar
estimates. The resulting arithmetic proves that the maximal transverse
intersection number is three once the free point contribution in the
possible value four case is supplied.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Numerical

/-- If the root entry and the branch count are both three, positivity of
the point basis forces the satellite set to be empty. -/
theorem ProximityCertificate.satellitePoints_eq_empty_of_root_three_branch_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : OnLeConjecture.Numerical.ProximityCertificate α)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbranch : c.branchCount = 3) :
    c.satellitePoints = ∅ := by
  have hsum := c.branchCount_add_satelliteMultiplicity
  rw [hroot, hbranch] at hsum
  have hsigma : c.satelliteMultiplicity = 0 := by omega
  apply Finset.eq_empty_of_forall_notMem
  intro p hp
  have hpLe : c.multiplicity p ≤ c.satelliteMultiplicity := by
    rw [ProximityCertificate.satelliteMultiplicity]
    exact Finset.single_le_sum
      (fun q _hq ↦ Nat.zero_le (c.multiplicity q)) hp
  have hpPositive := hpositive p
  omega

/-- The global and polar estimates rule out a maximal transverse
intersection number at least five. -/
theorem transverse_intersection_lt_five
    (M S b m n : ℕ)
    (hM : M ≤ 3 * S)
    (hS : 3 ≤ S)
    (hb : 1 ≤ b)
    (hm : 1 ≤ m)
    (hglobal : M + S ≤ 3 * m)
    (hpolar : n * (m - 1) + S + b ≤ 2 * M) :
    n < 5 := by
  by_contra hnot
  have hn : 5 ≤ n := by omega
  have hMInt : (M : ℤ) ≤ 3 * S := by exact_mod_cast hM
  have hSInt : (3 : ℤ) ≤ S := by exact_mod_cast hS
  have hbInt : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hmInt : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hglobalInt : (M : ℤ) + S ≤ 3 * m := by
    exact_mod_cast hglobal
  have hnInt : (5 : ℤ) ≤ n := by exact_mod_cast hn
  have hpolarCast :
      ((n * (m - 1) + S + b : ℕ) : ℤ) ≤ ((2 * M : ℕ) : ℤ) := by
    exact_mod_cast hpolar
  have hpolarInt :
      (n : ℤ) * ((m : ℤ) - 1) ≤ 2 * M - S - b := by
    push_cast [Nat.cast_sub hm] at hpolarCast
    linarith
  exact intersection_at_least_five_impossible
    M S b m n hMInt hSInt hbInt hmInt hglobalInt hnInt hpolarInt

/-- In the possible value four case, the point basis counts and the free
point contribution contradict the global and polar estimates. -/
theorem transverse_intersection_ne_four
    (M S b m n A₃ A₂ A₁ sigma : ℕ)
    (hA₃ : 1 ≤ A₃)
    (hM : M = 9 * A₃ + 4 * A₂ + A₁)
    (hS : S = 3 * A₃ + 2 * A₂ + A₁)
    (hbranch : b + sigma = 3)
    (hglobal : M + S ≤ 3 * m)
    (hpolar : n * (m - 1) + S + b ≤ 2 * M)
    (hfree : 5 + 3 * sigma ≤ 6 * A₂ + 5 * A₁) :
    n ≠ 4 := by
  intro hn
  subst n
  have hm : 1 ≤ m := by
    by_contra hnot
    have hmZero : m = 0 := by omega
    rw [hmZero] at hglobal
    have hSZero : S = 0 := by omega
    have hcountZero : 3 * A₃ + 2 * A₂ + A₁ = 0 :=
      hS.symm.trans hSZero
    omega
  have hglobalInt : (M : ℤ) + S ≤ 3 * m := by
    exact_mod_cast hglobal
  have hpolarCast :
      (((4 * (m - 1) + S + b : ℕ) : ℤ)) ≤
        ((2 * M : ℕ) : ℤ) := by
    exact_mod_cast hpolar
  have hpolarInt :
      4 * ((m : ℤ) - 1) ≤ 2 * M - S - b := by
    push_cast [Nat.cast_sub hm] at hpolarCast
    linarith
  have hraw :
      (0 : ℤ) ≤ 2 * M - 7 * S - 3 * b + 12 := by
    linarith
  have hMInt : (M : ℤ) = 9 * A₃ + 4 * A₂ + A₁ := by
    exact_mod_cast hM
  have hSInt : (S : ℤ) = 3 * A₃ + 2 * A₂ + A₁ := by
    exact_mod_cast hS
  have hbranchInt : (b : ℤ) + sigma = 3 := by
    exact_mod_cast hbranch
  have hcount :
      (0 : ℤ) ≤ -3 * ((A₃ : ℤ) - 1) - 6 * A₂ - 5 * A₁ +
        3 * sigma := by
    rw [hMInt, hSInt] at hraw
    linarith
  have hA₃Int : (1 : ℤ) ≤ A₃ := by exact_mod_cast hA₃
  have hfreeInt :
      (5 : ℤ) + 3 * sigma ≤ 6 * A₂ + 5 * A₁ := by
    exact_mod_cast hfree
  exact intersection_four_count_impossible
    A₃ A₂ A₁ sigma hA₃Int hcount hfreeInt

/-- The point basis counts, the global estimate, the polar estimate, and
the free point contribution force the maximal transverse intersection
number to equal three. -/
theorem transverse_intersection_eq_three
    (M S b m n A₃ A₂ A₁ sigma : ℕ)
    (hA₃ : 1 ≤ A₃)
    (hM : M = 9 * A₃ + 4 * A₂ + A₁)
    (hS : S = 3 * A₃ + 2 * A₂ + A₁)
    (hbranch : b + sigma = 3)
    (hMle : M ≤ 3 * S)
    (hSlower : 3 ≤ S)
    (hb : 1 ≤ b)
    (hm : 1 ≤ m)
    (hn : 3 ≤ n)
    (hglobal : M + S ≤ 3 * m)
    (hpolar : n * (m - 1) + S + b ≤ 2 * M)
    (hfree : 5 + 3 * sigma ≤ 6 * A₂ + 5 * A₁) :
    n = 3 := by
  have hnlt : n < 5 := transverse_intersection_lt_five
    M S b m n hMle hSlower hb hm hglobal hpolar
  have hnFour : n ≠ 4 := transverse_intersection_ne_four
    M S b m n A₃ A₂ A₁ sigma hA₃ hM hS hbranch hglobal hpolar hfree
  omega

/-- A free entry one point outside the satellite set, together with root
entry three and positive branch count, supplies the count inequality used
to exclude transverse intersection number four. -/
theorem proximity_free_point_count_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbranchPositive : 1 ≤ c.branchCount)
    (freePoint : α)
    (hfreeMultiplicity : c.multiplicity freePoint = 1)
    (hfreeNotSatellite : freePoint ∉ c.satellitePoints) :
    5 + 3 * c.satelliteMultiplicity ≤
      6 * c.multiplicityCount 2 + 5 * c.multiplicityCount 1 := by
  classical
  let weight : α → ℕ := fun p ↦
    if c.multiplicity p = 2 then 6
    else if c.multiplicity p = 1 then 5 else 0
  have hsigma : c.satelliteMultiplicity ≤ 2 :=
    c.satelliteMultiplicity_le_two_of_root_three
      hroot hbranchPositive
  have hsatelliteBound (p : α) (hp : p ∈ c.satellitePoints) :
      c.multiplicity p ≤ 2 := by
    have hpLe : c.multiplicity p ≤ c.satelliteMultiplicity := by
      rw [ProximityCertificate.satelliteMultiplicity]
      exact Finset.single_le_sum
        (fun q _hq ↦ Nat.zero_le (c.multiplicity q)) hp
    omega
  have hsatelliteWeight (p : α) (hp : p ∈ c.satellitePoints) :
      3 * c.multiplicity p ≤ weight p := by
    have hpPositive := hpositive p
    have hpBound := hsatelliteBound p hp
    have hpCases : c.multiplicity p = 1 ∨ c.multiplicity p = 2 := by
      omega
    rcases hpCases with hpOne | hpTwo
    · simp [weight, hpOne]
    · simp [weight, hpTwo]
  have hsatelliteSum :
      3 * c.satelliteMultiplicity ≤
        ∑ p ∈ c.satellitePoints, weight p := by
    rw [ProximityCertificate.satelliteMultiplicity, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact hsatelliteWeight p hp
  have hinsertLe :
      ∑ p ∈ insert freePoint c.satellitePoints, weight p ≤
        ∑ p, weight p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro p _hp _hnot
      exact Nat.zero_le (weight p)
  have hall :
      (∑ p, weight p) =
        6 * c.multiplicityCount 2 + 5 * c.multiplicityCount 1 := by
    have htwo :
        (∑ p, if c.multiplicity p = 2 then 6 else 0) =
          6 * c.multiplicityCount 2 := by
      rw [← Finset.sum_filter]
      simp [ProximityCertificate.multiplicityCount,
        MultiplicityCounts.valueCount, Nat.mul_comm]
    have hone :
        (∑ p, if c.multiplicity p = 1 then 5 else 0) =
          5 * c.multiplicityCount 1 := by
      rw [← Finset.sum_filter]
      simp [ProximityCertificate.multiplicityCount,
        MultiplicityCounts.valueCount, Nat.mul_comm]
    calc
      (∑ p, weight p) =
          ∑ p, ((if c.multiplicity p = 2 then 6 else 0) +
            (if c.multiplicity p = 1 then 5 else 0)) := by
        apply Finset.sum_congr rfl
        intro p _hp
        by_cases hpTwo : c.multiplicity p = 2
        · simp [weight, hpTwo]
        · simp [weight, hpTwo]
      _ = 6 * c.multiplicityCount 2 +
          5 * c.multiplicityCount 1 := by
        rw [Finset.sum_add_distrib]
        rw [htwo, hone]
  calc
    5 + 3 * c.satelliteMultiplicity =
        weight freePoint + 3 * c.satelliteMultiplicity := by
      simp [weight, hfreeMultiplicity]
    _ ≤ weight freePoint +
        ∑ p ∈ c.satellitePoints, weight p :=
      Nat.add_le_add_left hsatelliteSum _
    _ = ∑ p ∈ insert freePoint c.satellitePoints, weight p := by
      rw [Finset.sum_insert hfreeNotSatellite]
    _ ≤ ∑ p, weight p := hinsertLe
    _ = 6 * c.multiplicityCount 2 +
        5 * c.multiplicityCount 1 := hall

/-- A proximity certificate with root entry three supplies the counts in
the maximal transverse intersection argument. -/
theorem ProximityCertificate.transverse_intersection_eq_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (m n : ℕ)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 3)
    (hbranchPositive : 1 ≤ c.branchCount)
    (freePoint : α)
    (hfreeMultiplicity : c.multiplicity freePoint = 1)
    (hfreeNotSatellite : freePoint ∉ c.satellitePoints)
    (hm : 1 ≤ m)
    (hn : 3 ≤ n)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    n = 3 := by
  have hA₃ : 1 ≤ c.multiplicityCount 3 := by
    rw [ProximityCertificate.multiplicityCount,
      MultiplicityCounts.valueCount]
    apply Finset.one_le_card.mpr
    refine ⟨c.root, ?_⟩
    simp [hroot]
  have hM :=
    c.squareMultiplicity_eq_nine_mul_count_three_add_four_mul_count_two_add_count_one
      hpositive hbounded
  have hS :=
    c.totalMultiplicity_eq_three_mul_count_three_add_two_mul_count_two_add_count_one
      hpositive hbounded
  have hMle : c.squareMultiplicity ≤ 3 * c.totalMultiplicity := by
    change (∑ p, c.multiplicity p ^ 2) ≤
      3 * ∑ p, c.multiplicity p
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    rw [pow_two]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_left (c.multiplicity p) (hbounded p)
  have hbranch := c.branchCount_add_satelliteMultiplicity
  rw [hroot] at hbranch
  have hfree := proximity_free_point_count_bound c hroot hpositive
    hbranchPositive freePoint hfreeMultiplicity hfreeNotSatellite
  exact OnLeConjecture.DThree.transverse_intersection_eq_three
    c.squareMultiplicity c.totalMultiplicity c.branchCount m n
      (c.multiplicityCount 3) (c.multiplicityCount 2)
      (c.multiplicityCount 1) c.satelliteMultiplicity
      hA₃ hM hS hbranch hMle
      (by
        rw [hS]
        omega)
      hbranchPositive hm hn hglobal hpolar hfree

/-- The Noether path formula supplies the free point needed in the possible
intersection number four case. Hence the global and polar estimates force
the intersection number to equal three. -/
theorem ProximityCertificate.transverse_intersection_eq_three_of_noether_path
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (m n : ℕ) (path : Finset α)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 3)
    (hbranchPositive : 1 ≤ c.branchCount)
    (hpathFree : ∀ p ∈ path, p ∉ c.satellitePoints)
    (hnoether : n = c.multiplicity c.root +
      ∑ p ∈ path, c.multiplicity p)
    (hm : 1 ≤ m)
    (hn : 3 ≤ n)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    n = 3 := by
  have hMle : c.squareMultiplicity ≤ 3 * c.totalMultiplicity := by
    change (∑ p, c.multiplicity p ^ 2) ≤
      3 * ∑ p, c.multiplicity p
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    rw [pow_two]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_left (c.multiplicity p) (hbounded p)
  have hSlower : 3 ≤ c.totalMultiplicity := by
    rw [← hroot]
    exact Finset.single_le_sum
      (fun p _hp ↦ Nat.zero_le (c.multiplicity p))
      (Finset.mem_univ c.root)
  have hnlt : n < 5 := transverse_intersection_lt_five
    c.squareMultiplicity c.totalMultiplicity c.branchCount m n
      hMle hSlower hbranchPositive hm hglobal hpolar
  have hnFour : n ≠ 4 := by
    intro hnFour
    have hpathSum : ∑ p ∈ path, c.multiplicity p = 1 := by
      rw [hroot] at hnoether
      omega
    have hpathNonempty : path.Nonempty := by
      by_contra hpathEmpty
      rw [Finset.not_nonempty_iff_eq_empty.mp hpathEmpty] at hpathSum
      simp at hpathSum
    obtain ⟨freePoint, hfreePoint⟩ := hpathNonempty
    have hfreeMultiplicity : c.multiplicity freePoint = 1 := by
      have hfreeLe : c.multiplicity freePoint ≤
          ∑ p ∈ path, c.multiplicity p := by
        exact Finset.single_le_sum
          (fun p _hp ↦ Nat.zero_le (c.multiplicity p)) hfreePoint
      have hfreePositive := hpositive freePoint
      omega
    have hresult :=
      OnLeConjecture.DThree.ProximityCertificate.transverse_intersection_eq_three
        c m n hroot
      hpositive hbounded hbranchPositive freePoint hfreeMultiplicity
      (hpathFree freePoint hfreePoint) hm hn hglobal hpolar
    omega
  omega

/-- Under the Noether path formula, the maximal transverse intersection is
three and the path contains no base point. -/
theorem ProximityCertificate.transverse_intersection_eq_three_and_path_empty
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (m n : ℕ) (path : Finset α)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 3)
    (hbranchPositive : 1 ≤ c.branchCount)
    (hpathFree : ∀ p ∈ path, p ∉ c.satellitePoints)
    (hnoether : n = c.multiplicity c.root +
      ∑ p ∈ path, c.multiplicity p)
    (hm : 1 ≤ m)
    (hn : 3 ≤ n)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    n = 3 ∧ path = ∅ := by
  have hnThree :=
    OnLeConjecture.DThree.ProximityCertificate.transverse_intersection_eq_three_of_noether_path
        c m n path hroot hpositive hbounded hbranchPositive hpathFree
        hnoether hm hn hglobal hpolar
  refine ⟨hnThree, ?_⟩
  have hpathSum : ∑ p ∈ path, c.multiplicity p = 0 := by
    rw [hroot, hnThree] at hnoether
    omega
  by_contra hpathNonempty
  have hpath : path.Nonempty := Finset.nonempty_iff_ne_empty.mpr hpathNonempty
  obtain ⟨p, hp⟩ := hpath
  have hpLe : c.multiplicity p ≤
      ∑ q ∈ path, c.multiplicity q := by
    exact Finset.single_le_sum
      (fun q _hq ↦ Nat.zero_le (c.multiplicity q)) hp
  have hpPositive := hpositive p
  omega

/-- If the intersection number also bounds three times the branch
multiplicity, then the branch multiplicity is one. -/
theorem ProximityCertificate.maximal_transverse_branch_numerics
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (m n branchMultiplicity : ℕ)
    (path : Finset α)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hbounded : ∀ p, c.multiplicity p ≤ 3)
    (hbranchPositive : 1 ≤ c.branchCount)
    (hpathFree : ∀ p ∈ path, p ∉ c.satellitePoints)
    (hnoether : n = c.multiplicity c.root +
      ∑ p ∈ path, c.multiplicity p)
    (hm : 1 ≤ m)
    (hn : 3 ≤ n)
    (hbranchMultiplicity : 1 ≤ branchMultiplicity)
    (hintersectionLower : 3 * branchMultiplicity ≤ n)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    n = 3 ∧ branchMultiplicity = 1 ∧ path = ∅ := by
  have hresult :=
    OnLeConjecture.DThree.ProximityCertificate.transverse_intersection_eq_three_and_path_empty
        c m n path hroot hpositive hbounded hbranchPositive hpathFree
        hnoether hm hn hglobal hpolar
  rcases hresult with ⟨hnThree, hpathEmpty⟩
  refine ⟨hnThree, ?_, hpathEmpty⟩
  omega

/-- Root connectivity derives the entry bound needed in the maximal
transverse branch argument. -/
theorem ProximityCertificate.maximal_transverse_branch_numerics_of_connected
    {α : Type*} [Fintype α] [DecidableEq α]
    (c : ProximityCertificate α) (m n branchMultiplicity : ℕ)
    (path : Finset α)
    (hroot : c.multiplicity c.root = 3)
    (hpositive : ∀ p, 1 ≤ c.multiplicity p)
    (hconnected : ∀ q,
      Relation.ReflTransGen c.ParentRelation q c.root)
    (hbranchPositive : 1 ≤ c.branchCount)
    (hpathFree : ∀ p ∈ path, p ∉ c.satellitePoints)
    (hnoether : n = c.multiplicity c.root +
      ∑ p ∈ path, c.multiplicity p)
    (hn : 3 ≤ n)
    (hbranchMultiplicity : 1 ≤ branchMultiplicity)
    (hintersectionLower : 3 * branchMultiplicity ≤ n)
    (hglobal : c.squareMultiplicity + c.totalMultiplicity ≤ 3 * m)
    (hpolar : n * (m - 1) + c.totalMultiplicity + c.branchCount ≤
      2 * c.squareMultiplicity) :
    n = 3 ∧ branchMultiplicity = 1 ∧ path = ∅ := by
  have hbounded : ∀ p, c.multiplicity p ≤ 3 := by
    intro p
    rw [← hroot]
    exact c.multiplicity_le_root hconnected p
  have hm : 1 ≤ m := by
    have htwo : 2 ≤ c.multiplicity c.root := by omega
    have hmTwo := c.two_le_parameter_of_global_estimate m htwo hglobal
    omega
  exact
    OnLeConjecture.DThree.ProximityCertificate.maximal_transverse_branch_numerics
      c m n branchMultiplicity path hroot hpositive hbounded
      hbranchPositive hpathFree hnoether hm hn hbranchMultiplicity
      hintersectionLower hglobal hpolar

end OnLeConjecture.DThree
