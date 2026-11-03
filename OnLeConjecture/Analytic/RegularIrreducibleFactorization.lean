/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BlowupBranchCount
public import OnLeConjecture.Analytic.WeightedOrderCancellation
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Transverse regularity of analytic factors

If first-axis order equals ordinary order for an analytic equation, the
same equality holds for every nonzero divisor. Weighted-order cancellation
and one-variable additivity prove this assertion. Unique factorization then
constructs a finite family of transverse irreducible equations for every
nonzero squarefree regular equation.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators
open UniqueFactorizationMonoid

theorem exists_exact_maximalIdeal_order_of_ne_zero
    (f : Germ 2) (hf : f ≠ 0) :
    ∃ m : ℕ, f ∈ maximalIdeal 2 ^ m ∧ f ∉ maximalIdeal 2 ^ (m + 1) := by
  classical
  have hex : ∃ k : ℕ, f ∉ maximalIdeal 2 ^ (k + 1) := by
    by_contra hn
    push Not at hn
    apply hf
    apply eq_zero_of_mem_maximalIdeal_pow_all
    intro k
    cases k with
    | zero => simp
    | succ k => exact hn k
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  by_cases hz : Nat.find hex = 0
  · simp [hz]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hmin := Nat.find_min hex (show k < Nat.find hex by omega)
    rw [hk]
    exact not_not.mp hmin

/-- Every nonzero factor of a transverse regular equation is itself
transverse regular at its ordinary order. -/
theorem exists_exact_regular_order_of_dvd
    (m : ℕ) (f g : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m)
    (hg : g ≠ 0) (hdvd : g ∣ f) :
    ∃ k : ℕ, g ∈ maximalIdeal 2 ^ k ∧
      IsRegularInFirstCoordinateOfOrder g k := by
  obtain ⟨q, hfactor⟩ := hdvd
  obtain ⟨k, hgk, hgknext⟩ := exists_exact_maximalIdeal_order_of_ne_zero g hg
  have hkm : k ≤ m := by
    by_contra hnot
    have hfnext := not_mem_succ_maximalIdeal_pow_of_first_regular m f hregular
    apply hfnext
    rw [hfactor]
    exact (Ideal.pow_le_pow_right (show m + 1 ≤ k by omega))
      ((maximalIdeal 2 ^ k).mul_mem_right q hgk)
  obtain ⟨P, hP, htail⟩ := exists_weightedHomogeneous_coordinatePolynomial_mod_succ
    1 k (by decide) g (by simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hgk)
  have hPne : P ≠ 0 := by
    intro hz
    apply hgknext
    simpa only [hz, map_zero, sub_zero, weightedOrderIdeal_one_eq_maximalIdeal_pow] using htail
  have hq : q ∈ maximalIdeal 2 ^ (m - k) := by
    have hprod : g * q ∈ weightedOrderIdeal 1 (k + (m - k)) := by
      rw [Nat.add_sub_of_le hkm, weightedOrderIdeal_one_eq_maximalIdeal_pow, ← hfactor]
      exact hf
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using
      mem_weightedOrderIdeal_of_mul_mem 1 k (m - k) (by decide) P hP hPne g q htail hprod
  let a := vanishingOrder (lineRestriction (firstCoordinateVector 1) g)
  let b := vanishingOrder (lineRestriction (firstCoordinateVector 1) q)
  have hab : a + b = (m : ℕ∞) := by
    have h := hregular
    change vanishingOrder (lineRestriction (firstCoordinateVector 1) f) = (m : ℕ∞) at h
    rw [hfactor, map_mul, vanishingOrder_mul] at h
    exact h
  have haBound : a ≤ (m : ℕ∞) := by
    rw [← hab]
    exact le_self_add
  have hbBound : b ≤ (m : ℕ∞) := by
    rw [← hab]
    exact le_add_self
  have haTop : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) haBound
  have hbTop : b ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hbBound
  have haEq := ENat.natCast_toNat haTop
  have hbEq := ENat.natCast_toNat hbTop
  have hsum : a.toNat + b.toNat = m := by
    have h := congrArg ENat.toNat hab
    simpa only [ENat.toNat_add haTop hbTop, ENat.toNat_natCast] using h
  have hak : (k : ℕ∞) ≤ a :=
    mem_maximalIdeal_one_pow_iff.mp
      ((lineGerm (firstCoordinateVector 1)).pullback_mem_maximalIdeal_pow hgk)
  have hbk : ((m - k : ℕ) : ℕ∞) ≤ b :=
    mem_maximalIdeal_one_pow_iff.mp
      ((lineGerm (firstCoordinateVector 1)).pullback_mem_maximalIdeal_pow hq)
  rw [← haEq] at hak
  rw [← hbEq] at hbk
  have hakNat : k ≤ a.toNat := by exact_mod_cast hak
  have hbkNat : m - k ≤ b.toNat := by exact_mod_cast hbk
  have haNat : a.toNat = k := by omega
  refine ⟨k, hgk, ?_⟩
  change a = (k : ℕ∞)
  rw [← haEq, haNat]

/-- Unique factorization constructs distinct transverse analytic branches.
Their ordinary orders sum to the order of the original reduced equation. -/
theorem exists_regular_irreducible_factorization_of_squarefree
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f) :
    ∃ (s : Finset (Germ 2)) (ord : s → ℕ) (U : Germ 2),
      IsUnit U ∧ f = U * ∏ i : s, (i : Germ 2) ∧ (∑ i : s, ord i) = m ∧
      (∀ i : s, 0 < ord i ∧ Irreducible (i : Germ 2) ∧
        (i : Germ 2) ∈ maximalIdeal 2 ^ ord i ∧
        IsRegularInFirstCoordinateOfOrder (i : Germ 2) (ord i)) ∧
      ∀ i j : s, i ≠ j → ¬ Associated (i : Germ 2) (j : Germ 2) := by
  classical
  let : StrongNormalizationMonoid (Germ 2) := UniqueFactorizationMonoid.strongNormalizationMonoid
  have hfne : f ≠ 0 := by
    intro hz
    have h := hregular
    change vanishingOrder (lineRestriction (firstCoordinateVector 1) f) = (m : ℕ∞) at h
    rw [hz, map_zero, vanishingOrder_zero] at h
    exact ENat.natCast_ne_top m h.symm
  let s : Finset (Germ 2) := (normalizedFactors f).toFinset
  have hmem (i : s) : (i : Germ 2) ∈ normalizedFactors f :=
    Multiset.mem_toFinset.mp i.property
  have hirr (i : s) : Irreducible (i : Germ 2) :=
    irreducible_of_normalized_factor _ (hmem i)
  choose ord horder hreg using fun i : s ↦
    exists_exact_regular_order_of_dvd m f i hf hregular (hirr i).ne_zero
      (dvd_of_mem_normalizedFactors (hmem i))
  have hnodup : (normalizedFactors f).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hfne).mp hsq
  have hprod : (∏ i : s, (i : Germ 2)) = (normalizedFactors f).prod := by
    rw [Finset.prod_coe_sort s (fun x ↦ x)]
    change (s.val.map id).prod = _
    rw [Multiset.map_id]
    change (normalizedFactors f).toFinset.val.prod = _
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  obtain ⟨U, hU⟩ := prod_normalizedFactors hfne
  have hfactor : f = (U : Germ 2) * ∏ i : s, (i : Germ 2) := by
    rw [hprod, mul_comm]
    exact hU.symm
  have hsum : (∑ i : s, ord i) = m := by
    have hproductRegular := isRegularInFirstCoordinateOfOrder_prod Finset.univ
      ord (fun i : s ↦ (i : Germ 2)) (fun i _ ↦ hreg i)
    have hfirst : IsRegularInFirstCoordinateOfOrder (∏ i : s, (i : Germ 2)) m := by
      apply (isRegularInFirstCoordinateOfOrder_unit_mul_iff (U : Germ 2) _ U.isUnit).mp
      rwa [← hfactor]
    have hcast : ((∑ i : s, ord i : ℕ) : ℕ∞) = (m : ℕ∞) :=
      hproductRegular.symm.trans hfirst
    exact_mod_cast hcast
  refine ⟨s, ord, U, U.isUnit, hfactor, hsum, ?_, ?_⟩
  · intro i
    refine ⟨?_, hirr i, horder i, hreg i⟩
    by_contra hpos
    have hz : ord i = 0 := by omega
    have h := hreg i
    rw [hz] at h
    have hunit : IsUnit (i : Germ 2) := by
      simpa using isUnit_firstCoordinateTailIterate_of_regular h
    exact (hirr i).not_isUnit hunit
  · intro i j hij hass
    apply hij
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hmem i) (hmem j) hass)

end OnLeConjecture.Analytic.Germ
