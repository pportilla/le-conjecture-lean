/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SectionBranchImage
public import OnLeConjecture.Analytic.ProductDivisorIntersectionBound
public import Mathlib.Algebra.Squarefree.Basic

/-!
# The reduced image equation of a plane section

The branch equations and parametrizations below are constructed from a
squarefree first component of an injective plane-to-space germ. Distinct
branches remain distinct in the image. Their product defines the reduced
plane image, and preserves the intersection pairing with every equation.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace OnLeConjecture.PlaneCurve

open Analytic Analytic.Germ

/-- Finiteness of a product intersection is equivalent to finiteness for
each factor, including the empty product. -/
theorem hasFiniteIntersection_finset_prod_left_iff {ι : Type*}
    (s : Finset ι) (F : ι → Germ 2) (q : Germ 2) :
    HasFiniteIntersection (∏ i ∈ s, F i) q ↔ ∀ i ∈ s, HasFiniteIntersection (F i) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.notMem_empty, false_implies, implies_true, iff_true]
      apply (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le _ _).mpr
      refine ⟨0, ?_⟩
      have htop : pairIdeal 1 q = ⊤ :=
        (pairIdeal 1 q).eq_top_of_isUnit_mem (Ideal.subset_span (by simp)) isUnit_one
      rw [htop]
      exact le_top
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, hasFiniteIntersection_mul_left_iff, ih]
      simp only [Finset.mem_insert, forall_eq_or_imp]

end OnLeConjecture.PlaneCurve

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve UniqueFactorizationMonoid

/-- Factor equations and normalizations for a coordinate section and its plane image. -/
structure SectionImageFactorization (g : PointedMapGerm 2 3) where
  branches : Finset (Germ 2)
  sourceAssociated : Associated (∏ i : branches, (i : Germ 2)) (g.1.component 0)
  sourceIrreducible : ∀ i : branches, Irreducible (i : Germ 2)
  sourceNonassociated : ∀ i j : branches, i ≠ j → ¬ Associated (i : Germ 2) (j : Germ 2)
  parametrization : branches → PointedMapGerm 1 2
  parametrizationInjective : ∀ i, (parametrization i).HasInjectiveRepresentative
  sourceAnnihilates : ∀ i, (parametrization i).pullbackRingHom (i : Germ 2) = 0
  equation : branches → Germ 2
  imageIrreducible : ∀ i, Irreducible (equation i)
  imageAnnihilates : ∀ i, (g.sectionBranch (parametrization i)).pullbackRingHom (equation i) = 0

namespace PointedMapGerm

/-- A reduced coordinate section of an injective map supplies its own
finite source and image branch equations and normalizations. -/
theorem exists_sectionImageFactorization (g : PointedMapGerm 2 3)
    (hg : g.HasInjectiveRepresentative) (hsq : Squarefree (g.1.component 0)) :
    Nonempty (SectionImageFactorization g) := by
  classical
  let : StrongNormalizationMonoid (Germ 2) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let v := g.1.component 0
  let s : Finset (Germ 2) := (normalizedFactors v).toFinset
  have hmem (i : s) : (i : Germ 2) ∈ normalizedFactors v := Multiset.mem_toFinset.mp i.property
  have hirr (i : s) : Irreducible (i : Germ 2) := irreducible_of_normalized_factor _ (hmem i)
  have hdiv (i : s) : (i : Germ 2) ∣ g.1.component 0 := dvd_of_mem_normalizedFactors (hmem i)
  have hprod : (∏ i : s, (i : Germ 2)) = (normalizedFactors v).prod := by
    rw [Finset.prod_coe_sort s (fun x => x)]
    change (s.val.map id).prod = _
    rw [Multiset.map_id]
    change (normalizedFactors v).toFinset.val.prod = _
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr
      ((squarefree_iff_nodup_normalizedFactors hsq.ne_zero).mp hsq)]
  choose γ w hγ hγf hγker hβ hw hβw hβker hincl hpair using
    fun i : s => g.exists_sectionBranch_equation_and_intersections hg i (hirr i) (hdiv i)
  refine ⟨⟨s, ?_, hirr, ?_, γ, hγ, hγf, w, hw, hβw⟩⟩
  · rw [hprod]
    exact prod_normalizedFactors hsq.ne_zero
  · intro i j hij hass
    exact hij (Subtype.ext (mem_normalizedFactors_eq_of_associated (hmem i) (hmem j) hass))

end PointedMapGerm

namespace SectionImageFactorization

variable {g : PointedMapGerm 2 3} (D : SectionImageFactorization g)

/-- The product equation in the target coordinate plane. -/
def imageEquation : Germ 2 := ∏ i, D.equation i

theorem source_dvd (i : D.branches) : (i : Germ 2) ∣ g.1.component 0 :=
  (D.sourceAssociated.dvd_iff_dvd_right).mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

theorem section_zero (i : D.branches) :
    (D.parametrization i).pullbackRingHom (g.1.component 0) = 0 :=
  (parametrization_pullback_eq_zero_iff_dvd i (D.sourceIrreducible i) (D.parametrization i)
    (D.sourceAnnihilates i)
    ((D.parametrization i).exists_nonzero_coordinate_pullback_of_injective_curve
      (D.parametrizationInjective i)) _).mpr (D.source_dvd i)

theorem image_injective (hg : g.HasInjectiveRepresentative) (i : D.branches) :
    (g.sectionBranch (D.parametrization i)).HasInjectiveRepresentative :=
  g.sectionBranch_hasInjectiveRepresentative hg _ (D.parametrizationInjective i) (D.section_zero i)

theorem source_kernel (i : D.branches) :
    RingHom.ker (D.parametrization i).pullbackRingHom = Ideal.span {(i : Germ 2)} :=
  parametrization_kernel_eq_span_singleton i (D.sourceIrreducible i) _ (D.sourceAnnihilates i)
    ((D.parametrization i).exists_nonzero_coordinate_pullback_of_injective_curve
      (D.parametrizationInjective i))

theorem image_kernel (hg : g.HasInjectiveRepresentative) (i : D.branches) :
    RingHom.ker (g.sectionBranch (D.parametrization i)).pullbackRingHom =
      Ideal.span {D.equation i} :=
  parametrization_kernel_eq_span_singleton _ (D.imageIrreducible i) _ (D.imageAnnihilates i)
    ((g.sectionBranch (D.parametrization i)).exists_nonzero_coordinate_pullback_of_injective_curve
      (D.image_injective hg i))

theorem image_nonassociated (hg : g.HasInjectiveRepresentative)
    (i j : D.branches) (hij : i ≠ j) : ¬ Associated (D.equation i) (D.equation j) := by
  intro hass
  have hk : RingHom.ker (g.sectionBranch (D.parametrization i)).pullbackRingHom =
      RingHom.ker (g.sectionBranch (D.parametrization j)).pullbackRingHom := by
    rw [D.image_kernel hg i, D.image_kernel hg j]
    exact Ideal.span_singleton_eq_span_singleton.mpr hass
  have hs := g.sectionBranch_kernel_injective hg _ _ (D.section_zero i) (D.section_zero j) hk
  rw [D.source_kernel i, D.source_kernel j] at hs
  exact D.sourceNonassociated i j hij (Ideal.span_singleton_eq_span_singleton.mp hs)

theorem image_relPrime (hg : g.HasInjectiveRepresentative) (i j : D.branches) (hij : i ≠ j) :
    IsRelPrime (D.equation i) (D.equation j) := by
  apply (D.imageIrreducible i).isRelPrime_iff_not_dvd.mpr
  intro hd
  rcases (D.imageIrreducible j).dvd_iff.mp hd with hu | hass
  · exact (D.imageIrreducible i).not_isUnit hu
  · exact D.image_nonassociated hg i j hij hass.symm

theorem imageEquation_squarefree (hg : g.HasInjectiveRepresentative) :
    Squarefree D.imageEquation := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    exact D.image_relPrime hg i j hij
  · intro i _
    exact (D.imageIrreducible i).squarefree

/-- Every equation vanishing on the surface restricts to an equation of
the constructed reduced plane section. -/
theorem imageEquation_dvd_restriction_of_pullback_zero (hg : g.HasInjectiveRepresentative)
    (f : Germ 3) (hf : g.pullbackRingHom f = 0) :
    D.imageEquation ∣ hyperplaneRestriction 2 f := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro i _ j _ hij
    exact D.image_relPrime hg i j hij
  · intro i _
    rw [← Ideal.mem_span_singleton, ← D.image_kernel hg i, RingHom.mem_ker]
    have heq := congrArg (fun γ : PointedMapGerm 1 3 => γ.pullbackRingHom f)
      (g.inclusion_comp_sectionBranch (D.parametrization i) (D.section_zero i))
    simp only [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, hf, map_zero] at heq
    exact heq

/-- The plane product equation is the full equation ideal of the reduced
section image, expressed by divisibility in the source and target rings. -/
theorem imageEquation_dvd_iff (hg : g.HasInjectiveRepresentative) (q : Germ 2) :
    D.imageEquation ∣ q ↔ g.1.component 0 ∣ g.pullbackRingHom (hyperplaneExtension 2 q) := by
  have hbranch (i : D.branches) : D.equation i ∣ q ↔
      (i : Germ 2) ∣ g.pullbackRingHom (hyperplaneExtension 2 q) := by
    rw [← Ideal.mem_span_singleton, ← D.image_kernel hg i,
      ← Ideal.mem_span_singleton, ← D.source_kernel i]
    simp only [RingHom.mem_ker, PointedMapGerm.sectionBranch,
      PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    rfl
  constructor
  · intro h
    apply D.sourceAssociated.dvd_iff_dvd_left.mp
    apply Finset.prod_dvd_of_isRelPrime
    · intro i _ j _ hij
      apply (D.sourceIrreducible i).isRelPrime_iff_not_dvd.mpr
      intro hd
      rcases (D.sourceIrreducible j).dvd_iff.mp hd with hu | hass
      · exact (D.sourceIrreducible i).not_isUnit hu
      · exact D.sourceNonassociated i j hij hass.symm
    · intro i _
      exact (hbranch i).mp ((Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans h)
  · intro h
    apply Finset.prod_dvd_of_isRelPrime
    · intro i _ j _ hij
      exact D.image_relPrime hg i j hij
    · intro i _
      exact (hbranch i).mpr ((D.source_dvd i).trans h)

theorem branch_intersection_finite_iff (hg : g.HasInjectiveRepresentative)
    (i : D.branches) (q : Germ 2) :
    HasFiniteIntersection (D.equation i) q ↔
      HasFiniteIntersection (i : Germ 2) (g.pullbackRingHom (hyperplaneExtension 2 q)) := by
  rw [(g.sectionBranch (D.parametrization i)).hasFiniteIntersection_iff_pullback_ne_zero
      (D.image_injective hg i) _ (D.imageIrreducible i) (D.imageAnnihilates i),
    (D.parametrization i).hasFiniteIntersection_iff_pullback_ne_zero
      (D.parametrizationInjective i) _ (D.sourceIrreducible i) (D.sourceAnnihilates i)]
  simp only [PointedMapGerm.sectionBranch, PointedMapGerm.pullbackRingHom_comp,
    RingHom.comp_apply]
  rfl

theorem branch_intersection_eq (hg : g.HasInjectiveRepresentative)
    (i : D.branches) (q : Germ 2)
    (himage : HasFiniteIntersection (D.equation i) q)
    (hsource : HasFiniteIntersection (i : Germ 2) (g.pullbackRingHom (hyperplaneExtension 2 q))) :
    intersectionMultiplicity (D.equation i) q himage =
      intersectionMultiplicity (i : Germ 2)
      (g.pullbackRingHom (hyperplaneExtension 2 q)) hsource := by
  rw [PointedMapGerm.intersectionMultiplicity_eq_pullback_order_of_injective_curve
      (g.sectionBranch (D.parametrization i))
      (D.image_injective hg i) _ (D.imageIrreducible i) (D.imageAnnihilates i) q himage,
    (D.parametrization i).intersectionMultiplicity_eq_pullback_order_of_injective_curve
      (D.parametrizationInjective i) _ (D.sourceIrreducible i) (D.sourceAnnihilates i) _ hsource]
  simp only [PointedMapGerm.sectionBranch, PointedMapGerm.pullbackRingHom_comp,
    RingHom.comp_apply]
  rfl

/-- The constructed reduced image equation has exactly the same finite
intersections as the source section with pulled-back equations. -/
theorem intersection_finite_iff (hg : g.HasInjectiveRepresentative) (q : Germ 2) :
    HasFiniteIntersection D.imageEquation q ↔
      HasFiniteIntersection (g.1.component 0) (g.pullbackRingHom (hyperplaneExtension 2 q)) := by
  have hp := pairIdeal_eq_of_associated D.sourceAssociated
    (Associated.refl (g.pullbackRingHom (hyperplaneExtension 2 q)))
  change HasFiniteIntersection (∏ i, D.equation i) q ↔ _
  change _ ↔ Module.Finite ℂ (Germ 2 ⧸ pairIdeal (g.1.component 0)
    (g.pullbackRingHom (hyperplaneExtension 2 q)))
  rw [← hp]
  change _ ↔ HasFiniteIntersection (∏ i : D.branches, (i : Germ 2))
    (g.pullbackRingHom (hyperplaneExtension 2 q))
  rw [PlaneCurve.hasFiniteIntersection_finset_prod_left_iff,
    PlaneCurve.hasFiniteIntersection_finset_prod_left_iff]
  simp only [Finset.mem_univ, forall_const]
  exact forall_congr' fun i => D.branch_intersection_finite_iff hg i q

/-- Intersection multiplicity of the reduced plane image equals the
intersection multiplicity of the source section. -/
theorem intersection_eq (hg : g.HasInjectiveRepresentative) (q : Germ 2)
    (himage : HasFiniteIntersection D.imageEquation q)
    (hsource : HasFiniteIntersection (g.1.component 0)
      (g.pullbackRingHom (hyperplaneExtension 2 q))) :
    intersectionMultiplicity D.imageEquation q himage =
      intersectionMultiplicity (g.1.component 0)
        (g.pullbackRingHom (hyperplaneExtension 2 q)) hsource := by
  have hw (i : D.branches) : HasFiniteIntersection (D.equation i) q :=
    (PlaneCurve.hasFiniteIntersection_finset_prod_left_iff _ _ _).mp himage i (Finset.mem_univ i)
  have hv (i : D.branches) : HasFiniteIntersection (i : Germ 2)
      (g.pullbackRingHom (hyperplaneExtension 2 q)) :=
    (D.branch_intersection_finite_iff hg i q).mp (hw i)
  have hp : HasFiniteIntersection (∏ i : D.branches, (i : Germ 2))
      (g.pullbackRingHom (hyperplaneExtension 2 q)) :=
    (PlaneCurve.hasFiniteIntersection_finset_prod_left_iff _ _ _).mpr fun i _ => hv i
  change intersectionMultiplicity (∏ i, D.equation i) q himage = _
  rw [intersectionMultiplicity_finset_prod_left _ _ _ hw himage,
    ← intersectionMultiplicity_eq_of_associated D.sourceAssociated
      (Associated.refl (g.pullbackRingHom (hyperplaneExtension 2 q))) hp hsource,
    intersectionMultiplicity_finset_prod_left _ _ _ hv hp]
  exact Finset.sum_congr rfl fun i _ => D.branch_intersection_eq hg i q (hw i) (hv i)

end SectionImageFactorization
end OnLeConjecture.Analytic
