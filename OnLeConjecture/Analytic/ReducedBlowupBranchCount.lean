/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RegularIrreducibleFactorization
public import OnLeConjecture.PlaneCurve.IrreducibleFiniteIntersection

/-!
# Branch-count decomposition for a reduced transverse equation

Only the original analytic equation, its ordinary order, squarefreeness,
and transverse first-axis regularity are inputs. Unique factorization and
the analytic branch theorem construct its exceptional centers and prove
the branch-count sum. Every strict transform is reduced, and the
complementary transform is a unit.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open scoped BigOperators

/-- Associated equations of the same exceptional order have associated
analytic strict transforms. -/
theorem pointBlowupTransform_associated
    (c : ℂ) (m : ℕ) (f g : Germ 2)
    (hf : f ∈ maximalIdeal 2 ^ m) (hg : g ∈ maximalIdeal 2 ^ m)
    (hass : Associated f g) :
    Associated (pointBlowupTransform c m f hf) (pointBlowupTransform c m g hg) := by
  obtain ⟨U, hU⟩ := hass
  have heq : pointBlowupTransform c m g hg =
      pointBlowupTransform c m f hf * (pointBlowupChartGerm c).pullbackRingHom U := by
    apply pointBlowupTransform_unique c m g _ _ (pointBlowupTransform_factor _ _ _ _)
    rw [← hU, map_mul, pointBlowupTransform_factor c m f hf, mul_assoc]
  rw [heq]
  exact (associated_mul_unit_left _ _ (U.isUnit.map _)).symm

/-- The original branch count is the sum of the actual strict-transform
branch counts at all exceptional centers. The center set, reducedness of
the transforms, and absence of a complementary branch are conclusions. -/
theorem exists_pointBlowupTransform_branchCount_sum_of_squarefree_regular
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f) :
    ∃ s : Finset ℂ,
      (∀ ζ, ζ ∈ s ↔ ¬ IsUnit (pointBlowupTransform ζ m f hf)) ∧
      PlaneCurve.irreducibleBranchCount f =
        ∑ ζ ∈ s, PlaneCurve.irreducibleBranchCount (pointBlowupTransform ζ m f hf) ∧
      (∀ ζ, Squarefree (pointBlowupTransform ζ m f hf)) ∧
      IsUnit (pointBlowupTransform 0 m
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow hf)) := by
  classical
  obtain ⟨factors, ord, U, hU, hfactor, hsum, hbranches, hdistinct⟩ :=
    exists_regular_irreducible_factorization_of_squarefree m f hf hregular hsq
  let F : factors → Germ 2 := fun i ↦ i
  have hF (i : factors) : F i ∈ maximalIdeal 2 ^ ord i := (hbranches i).2.2.1
  have hreg (i : factors) : IsRegularInFirstCoordinateOfOrder (F i) (ord i) :=
    (hbranches i).2.2.2
  have hfinite (i j : factors) (hij : i ≠ j) : PlaneCurve.HasFiniteIntersection (F i) (F j) :=
    PlaneCurve.hasFiniteIntersection_of_irreducible_not_associated _ _
      (hbranches i).2.1 (hbranches j).2.1 (hdistinct i j hij)
  obtain ⟨s, hs, hcount, _⟩ :=
    exists_pointBlowupTransform_branchCount_sum_of_irreducible_factors ord F
      (fun i ↦ (hbranches i).1) hF (fun i ↦ (hbranches i).2.1) hreg hfinite
  have hproductOrder : (∏ i, F i) ∈ maximalIdeal 2 ^ m := by
    rw [← hsum]
    exact prod_mem_maximalIdeal_pow_sum Finset.univ ord F (fun i _ ↦ hF i)
  have hass : Associated f (∏ i, F i) := by
    rw [hfactor]
    exact associated_unit_mul_left _ _ hU
  have hlocal (ζ : ℂ) : Associated (pointBlowupTransform ζ m f hf)
      (pointBlowupTransform ζ (∑ i, ord i) (∏ i, F i)
        (prod_mem_maximalIdeal_pow_sum Finset.univ ord F (fun i _ ↦ hF i))) := by
    simpa only [hsum] using
      pointBlowupTransform_associated ζ m f (∏ i, F i) hf hproductOrder hass
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro ζ
    rw [(hlocal ζ).isUnit_iff]
    exact hs ζ
  · rw [PlaneCurve.irreducibleBranchCount_eq_of_associated hass, hcount]
    exact Finset.sum_congr rfl (fun ζ _ ↦
      (PlaneCurve.irreducibleBranchCount_eq_of_associated (hlocal ζ)).symm)
  · intro ζ
    apply (hlocal ζ).squarefree_iff.mpr
    rw [pointBlowupTransform_prod Finset.univ ζ ord F hF]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply PlaneCurve.isRelPrime_of_hasFiniteIntersection
      exact hasFiniteIntersection_pointBlowupTransforms ζ (ord i) (ord j) (F i) (F j)
        (hF i) (hF j) (not_mem_succ_maximalIdeal_pow_of_first_regular _ _ (hreg i))
        (hfinite i j hij)
    · intro i _
      obtain ⟨c, hc, hother, _⟩ :=
        exists_unique_irreducible_pointBlowupTransform_of_regular (ord i) (hbranches i).1
          (F i) (hF i) (hbranches i).2.1 (hreg i)
      by_cases hζ : ζ = c
      · subst ζ
        exact hc.squarefree
      · exact (hother ζ hζ).squarefree
  · exact complementaryBlowupTransform_isUnit_of_regular m f _ hregular
      (pointBlowupTransform_factor _ _ _ _)

/-- A finite chart list need only cover all nonunit strict transforms.
Additional recorded centers contribute zero branches. -/
theorem pointBlowupTransform_branchCount_sum_of_finite_cover
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f)
    (s : Finset ℂ)
    (hcover : ∀ ζ, ¬ IsUnit (pointBlowupTransform ζ m f hf) → ζ ∈ s) :
    PlaneCurve.irreducibleBranchCount f =
      ∑ ζ ∈ s, PlaneCurve.irreducibleBranchCount (pointBlowupTransform ζ m f hf) := by
  classical
  obtain ⟨t, ht, hcount, _, _⟩ :=
    exists_pointBlowupTransform_branchCount_sum_of_squarefree_regular m f hf hregular hsq
  rw [hcount]
  apply Finset.sum_subset
  · intro ζ hζ
    exact hcover ζ ((ht ζ).mp hζ)
  · intro ζ _ hζ
    have hunit : IsUnit (pointBlowupTransform ζ m f hf) := by
      by_contra hnot
      exact hζ ((ht ζ).mpr hnot)
    exact PlaneCurve.irreducibleBranchCount_eq_zero_of_isUnit _ hunit

/-- A separated, complete finite list of exceptional centers may index
the branch sum. Completeness refers to actual nonunit transforms. -/
theorem pointBlowupTransform_branchCount_sum_of_indexed_cover
    {ι : Type*} (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hregular : IsRegularInFirstCoordinateOfOrder f m) (hsq : Squarefree f)
    (s : Finset ι) (center : ι → ℂ) (hinj : Set.InjOn center s)
    (hcover : ∀ ζ, ¬ IsUnit (pointBlowupTransform ζ m f hf) →
      ∃ i ∈ s, center i = ζ) :
    PlaneCurve.irreducibleBranchCount f =
      ∑ i ∈ s, PlaneCurve.irreducibleBranchCount (pointBlowupTransform (center i) m f hf) := by
  classical
  rw [pointBlowupTransform_branchCount_sum_of_finite_cover m f hf hregular hsq
    (s.image center) (fun ζ hζ ↦ Finset.mem_image.mpr (hcover ζ hζ))]
  exact Finset.sum_image hinj

end OnLeConjecture.Analytic.Germ
