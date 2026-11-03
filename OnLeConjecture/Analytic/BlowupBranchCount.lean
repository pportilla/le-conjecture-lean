/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IrreducibleBlowupBranch
public import OnLeConjecture.Analytic.StrictBlowupFiniteIntersection
public import OnLeConjecture.PlaneCurve.BranchCountAdditivity

/-!
# Branch counts across the first blowup

For a finite product of transverse regular irreducible equations, the
unique center of every factor is constructed analytically. Distinct
factors with finite intersection still have finite intersection after
blowup. Consequently the sum of the strict-transform branch counts equals
the original branch count. The complementary transform is a unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

theorem prod_mem_maximalIdeal_pow_sum
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (f : ι → Germ 2)
    (hf : ∀ i ∈ s, f i ∈ maximalIdeal 2 ^ m i) :
    (∏ i ∈ s, f i) ∈ maximalIdeal 2 ^ (∑ i ∈ s, m i) := by
  simpa only [Finset.prod_pow_eq_pow_sum] using Ideal.prod_mem_prod hf

/-- Dividing the product by the sum of the exceptional orders gives
the product of the individual analytic strict transforms. -/
theorem pointBlowupTransform_prod
    {ι : Type*} (s : Finset ι) (c : ℂ) (m : ι → ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m i) :
    pointBlowupTransform c (∑ i ∈ s, m i) (∏ i ∈ s, f i)
      (prod_mem_maximalIdeal_pow_sum s m f (fun i _ ↦ hf i)) =
      ∏ i ∈ s, pointBlowupTransform c (m i) (f i) (hf i) := by
  apply pointBlowupTransform_unique c _ _ _ _ (pointBlowupTransform_factor _ _ _ _)
  rw [map_prod]
  simp_rw [pointBlowupTransform_factor c _ _ (hf _)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem isRegularInFirstCoordinateOfOrder_prod
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (f : ι → Germ 2)
    (hf : ∀ i ∈ s, IsRegularInFirstCoordinateOfOrder (f i) (m i)) :
    IsRegularInFirstCoordinateOfOrder (∏ i ∈ s, f i) (∑ i ∈ s, m i) := by
  unfold IsRegularInFirstCoordinateOfOrder at *
  rw [map_prod, vanishingOrder_finset_prod]
  simp only [Nat.cast_sum]
  exact Finset.sum_congr rfl hf

/-- The local branch counts of a product add at every finite center.
Finiteness of the transformed intersections is proved, not postulated. -/
theorem pointBlowupTransform_prod_branchCount
    {ι : Type*} (s : Finset ι) (c : ℂ) (m : ι → ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m i)
    (hregular : ∀ i ∈ s, IsRegularInFirstCoordinateOfOrder (f i) (m i))
    (hfinite : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → PlaneCurve.HasFiniteIntersection (f i) (f j)) :
    PlaneCurve.irreducibleBranchCount
      (pointBlowupTransform c (∑ i ∈ s, m i) (∏ i ∈ s, f i)
        (prod_mem_maximalIdeal_pow_sum s m f (fun i _ ↦ hf i))) =
      ∑ i ∈ s, PlaneCurve.irreducibleBranchCount (pointBlowupTransform c (m i) (f i) (hf i)) := by
  rw [pointBlowupTransform_prod s c m f hf]
  apply PlaneCurve.irreducibleBranchCount_prod_of_pairwise_finite
  intro i hi j hj hij
  exact hasFiniteIntersection_pointBlowupTransforms c (m i) (m j) (f i) (f j)
    (hf i) (hf j) (not_mem_succ_maximalIdeal_pow_of_first_regular _ _ (hregular i hi))
    (hfinite i hi j hj hij)

/-- For a supplied finite collection of transverse irreducible equations,
the finite exceptional centers and the branch-count equality are outputs.
No branch correspondence or separation of their transforms is an input. -/
theorem exists_pointBlowupTransform_branchCount_sum_of_irreducible_factors
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (f : ι → Germ 2)
    (hm : ∀ i, 0 < m i) (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m i)
    (hirr : ∀ i, Irreducible (f i))
    (hregular : ∀ i, IsRegularInFirstCoordinateOfOrder (f i) (m i))
    (hfinite : ∀ i j, i ≠ j → PlaneCurve.HasFiniteIntersection (f i) (f j)) :
    ∃ s : Finset ℂ,
      (∀ ζ, ζ ∈ s ↔ ¬ IsUnit
        (pointBlowupTransform ζ (∑ i, m i) (∏ i, f i)
          (prod_mem_maximalIdeal_pow_sum Finset.univ m f (fun i _ ↦ hf i)))) ∧
      PlaneCurve.irreducibleBranchCount (∏ i, f i) =
        ∑ ζ ∈ s, PlaneCurve.irreducibleBranchCount
          (pointBlowupTransform ζ (∑ i, m i) (∏ i, f i)
            (prod_mem_maximalIdeal_pow_sum Finset.univ m f (fun i _ ↦ hf i))) ∧
      IsUnit (pointBlowupTransform 0 (∑ i, m i)
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (∏ i, f i))
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow
          (prod_mem_maximalIdeal_pow_sum Finset.univ m f (fun i _ ↦ hf i)))) := by
  classical
  choose center hcenter hother hinfinity using fun i ↦
    exists_unique_irreducible_pointBlowupTransform_of_regular
      (m i) (hm i) (f i) (hf i) (hirr i) (hregular i)
  let s : Finset ℂ := Finset.univ.image center
  have hcount (ζ : ℂ) (i : ι) :
      PlaneCurve.irreducibleBranchCount (pointBlowupTransform ζ (m i) (f i) (hf i)) =
        if ζ = center i then 1 else 0 := by
    split_ifs with hζ
    · subst ζ
      exact PlaneCurve.irreducibleBranchCount_eq_one_of_irreducible _ (hcenter i)
    · exact PlaneCurve.irreducibleBranchCount_eq_zero_of_isUnit _ (hother i ζ hζ)
  have hcountProduct (ζ : ℂ) :
      PlaneCurve.irreducibleBranchCount
        (pointBlowupTransform ζ (∑ i, m i) (∏ i, f i)
          (prod_mem_maximalIdeal_pow_sum Finset.univ m f (fun i _ ↦ hf i))) =
        ∑ i, if ζ = center i then 1 else 0 := by
    rw [pointBlowupTransform_prod_branchCount Finset.univ ζ m f hf
      (fun i _ ↦ hregular i) (fun i _ j _ hij ↦ hfinite i j hij)]
    exact Finset.sum_congr rfl (fun i _ ↦ hcount ζ i)
  refine ⟨s, ?_, ?_, ?_⟩
  · intro ζ
    rw [pointBlowupTransform_prod Finset.univ ζ m f hf, IsUnit.prod_univ_iff]
    constructor
    · intro hζ hall
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hζ
      subst ζ
      exact (hcenter i).not_isUnit (hall i)
    · intro hζ
      by_contra hout
      apply hζ
      intro i
      apply hother i ζ
      intro hi
      exact hout (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
  · rw [PlaneCurve.irreducibleBranchCount_prod_of_pairwise_finite Finset.univ f
      (fun i _ j _ hij ↦ hfinite i j hij)]
    simp_rw [hcountProduct]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq']
    simp only [s, Finset.mem_image, Finset.mem_univ, true_and,
      exists_apply_eq_apply, ↓reduceIte]
    exact PlaneCurve.irreducibleBranchCount_eq_one_of_irreducible _ (hirr i)
  · exact complementaryBlowupTransform_isUnit_of_regular _ _ _
      (isRegularInFirstCoordinateOfOrder_prod Finset.univ m f (fun i _ ↦ hregular i))
      (pointBlowupTransform_factor _ _ _ _)

end OnLeConjecture.Analytic.Germ
