/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SectionDeltaSpecialization
public import OnLeConjecture.Analytic.GeneralTeissierPolarIdentity
public import OnLeConjecture.Analytic.ImageConductorCriticalSupport
public import OnLeConjecture.Analytic.SmoothPolarCorrection
public import OnLeConjecture.Analytic.PrincipalImageEquation
public import OnLeConjecture.Analytic.PlaneInjectiveFiniteness
public import OnLeConjecture.Analytic.GenericReducedPencil
public import OnLeConjecture.PlaneCurve.ParametricMorse
public import OnLeConjecture.Analytic.ParametricGermDivision

/-!
# The central plane section of a parametrized surface

Let `g : (ℂ², 0) → (ℂ³, 0)` be locally injective, let `v = g₀` be reduced,
and let `Φ` generate the equations of the image surface. Write `A` for the
analytic image ring and `B` for the source ring.

The first coordinate `v` is a nonzerodivisor on `B / A`, provided the
conductor contains an element meeting `v` finitely. The proof is the
Koszul argument for the pair `(x₀, C)` in `A`, where `C` is a conductor
element. It uses lying over for the finite extension `A ⊆ B` to identify
the prime factors of `Φ|_{x₀ = 0}` with the branches of the reduced section.

Consequently `Φ|_{x₀ = 0}` is associated to the reduced section equation
`w`. Combining this with Teissier's polar identities and Milnor's formula
gives

`2 δ(w) + i(v, J(v, g₂)) = 2 δ(v) + i(v, g^*(∂₁ Φ))`

whenever `v` meets `g₂` finitely.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

namespace Germ

/-- Differentiation in the first surviving coordinate commutes with
restriction to the first coordinate hyperplane of three-space. -/
theorem partialDerivative_hyperplaneRestriction_three (f : Germ 3) :
    partialDerivative (0 : Fin 2) (hyperplaneRestriction 2 f) =
      hyperplaneRestriction 2 (partialDerivative (1 : Fin 3) f) := by
  change partialDerivative (0 : Fin 2) (compPointed f (hyperplaneInclusionGerm 2)) = _
  rw [partialDerivative_compPointed_sum, Fin.sum_univ_three,
    ← PointedMapGerm.pullback_coordinate, ← PointedMapGerm.pullback_coordinate,
    ← PointedMapGerm.pullback_coordinate]
  change hyperplaneRestriction 2 (partialDerivative (0 : Fin 3) f) *
      partialDerivative (0 : Fin 2) (hyperplaneRestriction 2 (coordinate (0 : Fin 3))) +
    hyperplaneRestriction 2 (partialDerivative (1 : Fin 3) f) *
      partialDerivative (0 : Fin 2) (hyperplaneRestriction 2 (coordinate (1 : Fin 3))) +
    hyperplaneRestriction 2 (partialDerivative (2 : Fin 3) f) *
      partialDerivative (0 : Fin 2) (hyperplaneRestriction 2 (coordinate (2 : Fin 3))) = _
  have h1 : hyperplaneRestriction 2 (coordinate (1 : Fin 3)) = coordinate (0 : Fin 2) := by
    simpa using hyperplaneRestriction_coordinate_succ 2 (0 : Fin 2)
  have h2 : hyperplaneRestriction 2 (coordinate (2 : Fin 3)) = coordinate (1 : Fin 2) := by
    simpa using hyperplaneRestriction_coordinate_succ 2 (1 : Fin 2)
  rw [hyperplaneRestriction_coordinate_zero, h1, h2,
    partialDerivative_coordinate_ne (show (0 : Fin 2) ≠ 1 by decide)]
  simp only [partialDerivative_zero, partialDerivative_coordinate_same, mul_zero, mul_one,
    zero_add, add_zero]

theorem hyperplaneRestriction_extension (q : Germ 2) :
    hyperplaneRestriction 2 (hyperplaneExtension 2 q) = q :=
  DFunLike.congr_fun (hyperplaneRestriction_comp_extension 2) q

/-- No irreducible plane germ divides both coordinates. -/
theorem not_irreducible_dvd_coordinates {π : Germ 2} (hπ : Irreducible π)
    (h0 : π ∣ coordinate (0 : Fin 2)) (h1 : π ∣ coordinate (1 : Fin 2)) : False := by
  obtain ⟨P⟩ := exists_intersectionParametrization_of_irreducible π hπ
  obtain ⟨j, hj⟩ := P.nonconstant
  have hzero (h : Germ 2) (hdvd : π ∣ h) : P.map.pullbackRingHom h = 0 := by
    obtain ⟨a, rfl⟩ := hdvd
    rw [map_mul, P.curve_eq_zero, zero_mul]
  fin_cases j
  · exact hj (hzero _ h0)
  · exact hj (hzero _ h1)

end Germ

/-- Finiteness of an intersection with the section equation depends only on
the class of the second equation modulo the section equation. -/
theorem PointedMapGerm.pairIdeal_pullback_extension_restriction (g : PointedMapGerm 2 3)
    (f : Germ 3) :
    pairIdeal (g.1.component 0)
        (g.pullbackRingHom (hyperplaneExtension 2 (hyperplaneRestriction 2 f))) =
      pairIdeal (g.1.component 0) (g.pullbackRingHom f) := by
  obtain ⟨q, hq⟩ := exists_eq_hyperplaneExtension_add_coordinate_mul f
  have h := pairIdeal_sub_mul_right (g.1.component 0)
    (g.pullbackRingHom (hyperplaneExtension 2 (hyperplaneRestriction 2 f)) +
      g.1.component 0 * g.pullbackRingHom q) (g.pullbackRingHom q)
  rw [add_sub_cancel_right] at h
  rw [h]
  congr 1
  conv_rhs => rw [hq]
  rw [map_add, map_mul, PointedMapGerm.pullback_coordinate]

namespace SectionImageFactorization

variable {g : PointedMapGerm 2 3} (D : SectionImageFactorization g)

/-- The reduced section equation is not a unit. -/
theorem imageEquation_not_isUnit : ¬ IsUnit D.imageEquation := by
  intro hu
  have hv := D.squarefree_component_zero
  have hvm : g.1.component 0 ∈ maximalIdeal 2 := by
    rw [← PointedMapGerm.pullback_coordinate]
    exact g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal 0)
  have hvu : ¬ IsUnit (g.1.component 0) := fun h =>
    (isUnit_iff_valueRingHom_ne_zero.mp h) (mem_maximalIdeal_iff.mp hvm)
  have hpos := irreducibleBranchCount_pos_of_nonzero_nonunit _ hv.ne_zero hvu
  rw [D.irreducibleBranchCount_component_zero] at hpos
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
  exact (D.imageIrreducible i).not_isUnit
    (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) hu)

/-- Every irreducible factor of the hyperplane restriction of a generator of
the surface equations divides the reduced section equation. The proof uses
lying over for the finite extension given by the pullback. -/
theorem irreducible_dvd_imageEquation_of_dvd_restriction (hg : g.HasInjectiveRepresentative)
    (Φ : Germ 3) (hker : RingHom.ker g.pullbackRingHom = Ideal.span {Φ})
    (π : Germ 2) (hπ : Irreducible π) (hπΦ : π ∣ hyperplaneRestriction 2 Φ) :
    π ∣ D.imageEquation := by
  classical
  have hf := g.injective_isFiniteAtOrigin_two hg
  have hint : g.pullbackRingHom.IsIntegral := by
    have h1 : g.pullbackToImageRing.IsIntegral :=
      RingHom.isIntegral_of_surjective _ g.pullbackToImageRing_surjective
    have h2 : g.ImageRing.subtype.IsIntegral := by
      have : Module.Finite g.ImageRing (Germ 2) := hf
      intro b
      exact Algebra.IsIntegral.isIntegral (R := g.ImageRing) b
    exact RingHom.IsIntegral.trans _ _ h1 h2
  let := g.pullbackRingHom.toAlgebra
  have : Algebra.IsIntegral (Germ 3) (Germ 2) := ⟨hint⟩
  let P : Ideal (Germ 3) := Ideal.comap (hyperplaneRestriction 2) (Ideal.span {π})
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ.prime
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hmemP (y : Germ 3) : y ∈ P ↔ π ∣ hyperplaneRestriction 2 y := by
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
  have hkerP : Ideal.comap (algebraMap (Germ 3) (Germ 2)) ⊥ ≤ P := by
    intro y hy
    have hy' : y ∈ RingHom.ker g.pullbackRingHom := by
      rw [Ideal.mem_comap, Ideal.mem_bot] at hy
      exact hy
    rw [hker, Ideal.mem_span_singleton] at hy'
    rw [hmemP]
    exact hπΦ.trans (map_dvd _ hy')
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P ⊥ hkerP
  have hQmem (y : Germ 3) : g.pullbackRingHom y ∈ Q ↔ π ∣ hyperplaneRestriction 2 y := by
    rw [← hmemP, ← hQP, Ideal.mem_comap]
    rfl
  have hv : g.1.component 0 ∈ Q := by
    rw [← PointedMapGerm.pullback_coordinate, hQmem, hyperplaneRestriction_coordinate_zero]
    exact dvd_zero π
  have hπQ : g.pullbackRingHom (hyperplaneExtension 2 π) ∈ Q := by
    rw [hQmem, hyperplaneRestriction_extension]
  obtain ⟨i, -, hiQ⟩ : ∃ i ∈ (Finset.univ : Finset D.branches), (i : Germ 2) ∈ Q := by
    apply Ideal.IsPrime.prod_mem_iff.mp
    obtain ⟨u, hu⟩ := D.sourceAssociated
    have hprod : (∏ i : D.branches, (i : Germ 2)) = g.1.component 0 * ↑u⁻¹ := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [hprod]
    exact Q.mul_mem_right _ hv
  have hdiv : (i : Germ 2) ∣ g.pullbackRingHom (hyperplaneExtension 2 π) := by
    by_contra hnd
    have hfin := hasFiniteIntersection_of_irreducible_not_dvd _ _ (D.sourceIrreducible i) hnd
    obtain ⟨k, hk⟩ := (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le _ _).mp hfin
    have hpair : pairIdeal (i : Germ 2) (g.pullbackRingHom (hyperplaneExtension 2 π)) ≤ Q := by
      rw [pairIdeal_eq_span, Ideal.span_le]
      intro z hz
      rcases hz with rfl | rfl
      · exact hiQ
      · exact hπQ
    have hmQ : maximalIdeal 2 ≤ Q := Ideal.IsPrime.le_of_pow_le (hk.trans hpair)
    have hcoord (j : Fin 2) : π ∣ coordinate j := by
      have hmem := (hQmem (coordinate j.succ)).mp
        (hmQ (g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal j.succ)))
      rwa [hyperplaneRestriction_coordinate_succ] at hmem
    exact not_irreducible_dvd_coordinates hπ (hcoord 0) (hcoord 1)
  have hker_i : π ∈ RingHom.ker (g.sectionBranch (D.parametrization i)).pullbackRingHom := by
    obtain ⟨a, ha⟩ := hdiv
    have hzero := congrArg (D.parametrization i).pullbackRingHom ha
    rw [map_mul, D.sourceAnnihilates i, zero_mul] at hzero
    rw [RingHom.mem_ker]
    simp only [PointedMapGerm.sectionBranch, PointedMapGerm.pullbackRingHom_comp,
      RingHom.comp_apply]
    exact hzero
  rw [D.image_kernel hg i, Ideal.mem_span_singleton] at hker_i
  rcases hπ.dvd_iff.mp hker_i with hu | hass
  · exact ((D.imageIrreducible i).not_isUnit hu).elim
  · exact hass.dvd.trans (Finset.dvd_prod_of_mem D.equation (Finset.mem_univ i))

/-- The reduced section equation meets the restriction of a target germ
finitely exactly when the section meets the pullback of that germ finitely. -/
theorem hasFiniteIntersection_restriction_iff (hg : g.HasInjectiveRepresentative) (f : Germ 3) :
    HasFiniteIntersection D.imageEquation (hyperplaneRestriction 2 f) ↔
      HasFiniteIntersection (g.1.component 0) (g.pullbackRingHom f) := by
  rw [D.intersection_finite_iff hg]
  unfold HasFiniteIntersection
  rw [g.pairIdeal_pullback_extension_restriction f]

include D in
/-- The section coordinate is a nonzerodivisor modulo the image ring when
the conductor contains an element meeting the section finitely. -/
theorem mem_imageRing_of_component_zero_mul_mem (hg : g.HasInjectiveRepresentative)
    (Φ : Germ 3) (hker : RingHom.ker g.pullbackRingHom = Ideal.span {Φ})
    (c : Germ 2) (hc : c ∈ g.imageConductor)
    (hvc : HasFiniteIntersection (g.1.component 0) c)
    (b : Germ 2) (hb : g.1.component 0 * b ∈ g.ImageRing) : b ∈ g.ImageRing := by
  classical
  obtain ⟨A₁, hA₁⟩ := hb
  obtain ⟨A₂, hA₂⟩ := hc b
  obtain ⟨C, hC⟩ := g.imageConductor_mem_imageRing hc
  have hx0 : g.pullbackRingHom (coordinate (0 : Fin 3)) = g.1.component 0 :=
    PointedMapGerm.pullback_coordinate g 0
  have hkermem : C * A₁ - coordinate (0 : Fin 3) * A₂ ∈ RingHom.ker g.pullbackRingHom := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hA₁, hA₂, hC, hx0]
    ring
  rw [hker, Ideal.mem_span_singleton'] at hkermem
  obtain ⟨L, hL⟩ := hkermem
  have hres := congrArg (hyperplaneRestriction 2) hL
  rw [map_mul, map_sub, map_mul, map_mul, hyperplaneRestriction_coordinate_zero, zero_mul,
    sub_zero] at hres
  have hCfin : HasFiniteIntersection D.imageEquation (hyperplaneRestriction 2 C) := by
    rw [D.hasFiniteIntersection_restriction_iff hg, hC]
    exact hvc
  have hC0 : hyperplaneRestriction 2 C ≠ 0 := by
    intro h0
    rw [h0] at hCfin
    exact D.imageEquation_not_isUnit (isUnit_of_hasFiniteIntersection_zero_right _ hCfin)
  have hcop : IsRelPrime (hyperplaneRestriction 2 Φ) (hyperplaneRestriction 2 C) := by
    intro d hdΦ hdC
    by_contra hdu
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hC0 (zero_dvd_iff.mp hdC)
    obtain ⟨z, hz, hzd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
    have hzw := D.irreducible_dvd_imageEquation_of_dvd_restriction hg Φ hker z hz (hzd.trans hdΦ)
    exact hz.not_isUnit (hCfin.isUnit_of_common_divisor z hzw (hzd.trans hdC))
  have hdivA : hyperplaneRestriction 2 Φ ∣ hyperplaneRestriction 2 A₁ :=
    hcop.dvd_of_dvd_mul_left ⟨hyperplaneRestriction 2 L, by rw [← hres, mul_comm]⟩
  obtain ⟨a, ha⟩ := hdivA
  have hmem : A₁ - Φ * hyperplaneExtension 2 a ∈ RingHom.ker (hyperplaneRestriction 2) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hyperplaneRestriction_extension, ha, sub_self]
  rw [ker_hyperplaneRestriction_eq_span_coordinate_zero, Ideal.mem_span_singleton'] at hmem
  obtain ⟨A', hA'⟩ := hmem
  have hΦ0 : g.pullbackRingHom Φ = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.subset_span rfl
  have hA₁' : A₁ = Φ * hyperplaneExtension 2 a + A' * coordinate (0 : Fin 3) := by
    rw [hA']
    ring
  have hvb : g.1.component 0 * b = g.1.component 0 * g.pullbackRingHom A' := by
    rw [← hA₁, hA₁', map_add, map_mul, map_mul, hΦ0, hx0]
    ring
  have hb' := mul_left_cancel₀ D.squarefree_component_zero.ne_zero hvb
  exact ⟨A', hb'.symm⟩

/-- The restriction of the surface equation to the section hyperplane is
associated to the reduced section equation. -/
theorem associated_restriction_imageEquation (hg : g.HasInjectiveRepresentative)
    (Φ : Germ 3) (hker : RingHom.ker g.pullbackRingHom = Ideal.span {Φ})
    (c : Germ 2) (hc : c ∈ g.imageConductor)
    (hvc : HasFiniteIntersection (g.1.component 0) c) :
    Associated (hyperplaneRestriction 2 Φ) D.imageEquation := by
  have hΦ0 : g.pullbackRingHom Φ = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.subset_span rfl
  have h1 := D.imageEquation_dvd_restriction_of_pullback_zero hg Φ hΦ0
  obtain ⟨k, hk⟩ := (D.imageEquation_dvd_iff hg D.imageEquation).mp dvd_rfl
  obtain ⟨K, hK⟩ := D.mem_imageRing_of_component_zero_mul_mem hg Φ hker c hc hvc k
    ⟨_, hk⟩
  have hmem : hyperplaneExtension 2 D.imageEquation - coordinate (0 : Fin 3) * K ∈
      RingHom.ker g.pullbackRingHom := by
    rw [RingHom.mem_ker, map_sub, map_mul, PointedMapGerm.pullback_coordinate, hK, hk, sub_self]
  rw [hker, Ideal.mem_span_singleton'] at hmem
  obtain ⟨L, hL⟩ := hmem
  have hres := congrArg (hyperplaneRestriction 2) hL
  rw [map_mul, map_sub, map_mul, hyperplaneRestriction_coordinate_zero, zero_mul, sub_zero,
    hyperplaneRestriction_extension] at hres
  exact associated_of_dvd_dvd ⟨hyperplaneRestriction 2 L, by rw [← hres, mul_comm]⟩ h1

/-- With the restricted surface equation associated to the reduced section,
the first polar of the section is computed by the pulled back surface
polar. -/
theorem polar_intersection_eq (hg : g.HasInjectiveRepresentative) (Φ : Germ 3)
    (hassoc : Associated (hyperplaneRestriction 2 Φ) D.imageEquation)
    (hfin : HasFiniteIntersection D.imageEquation
      (partialDerivative (0 : Fin 2) D.imageEquation)) :
    ∃ hP : HasFiniteIntersection (g.1.component 0)
        (g.pullbackRingHom (partialDerivative (1 : Fin 3) Φ)),
      intersectionMultiplicity D.imageEquation (partialDerivative (0 : Fin 2) D.imageEquation)
          hfin =
        intersectionMultiplicity (g.1.component 0)
          (g.pullbackRingHom (partialDerivative (1 : Fin 3) Φ)) hP := by
  obtain ⟨u, hu⟩ := hassoc
  set w := D.imageEquation
  have hderiv : partialDerivative (0 : Fin 2) w =
      hyperplaneRestriction 2 (partialDerivative (1 : Fin 3) Φ) * ↑u +
        w * (↑u⁻¹ * partialDerivative (0 : Fin 2) (↑u : Germ 2)) := by
    rw [← hu, partialDerivative_mul, partialDerivative_hyperplaneRestriction_three]
    have hinv : (↑u * ↑u⁻¹ : Germ 2) = 1 := Units.mul_inv u
    linear_combination -(hyperplaneRestriction 2 Φ * partialDerivative (0 : Fin 2) (↑u : Germ 2)) *
      hinv
  have hpair : pairIdeal w (partialDerivative (0 : Fin 2) w) =
      pairIdeal w (hyperplaneRestriction 2 (partialDerivative (1 : Fin 3) Φ)) := by
    rw [← pairIdeal_sub_mul_right w (partialDerivative (0 : Fin 2) w)
      (↑u⁻¹ * partialDerivative (0 : Fin 2) (↑u : Germ 2)), hderiv, add_sub_cancel_right]
    exact pairIdeal_eq_of_associated (Associated.refl w) ⟨u⁻¹, by
      rw [mul_assoc, Units.mul_inv, mul_one]⟩
  have hfin' : HasFiniteIntersection w
      (hyperplaneRestriction 2 (partialDerivative (1 : Fin 3) Φ)) :=
    hfin.of_pairIdeal_eq hpair
  have hP := (D.hasFiniteIntersection_restriction_iff hg _).mp hfin'
  refine ⟨hP, ?_⟩
  rw [intersectionMultiplicity_eq_of_pairIdeal_eq hfin hfin' hpair]
  have hsource : HasFiniteIntersection (g.1.component 0)
      (g.pullbackRingHom (hyperplaneExtension 2
        (hyperplaneRestriction 2 (partialDerivative (1 : Fin 3) Φ)))) := by
    unfold HasFiniteIntersection
    rw [g.pairIdeal_pullback_extension_restriction]
    exact hP
  rw [D.intersection_eq hg _ hfin' hsource]
  exact intersectionMultiplicity_eq_of_pairIdeal_eq hsource hP
    (g.pairIdeal_pullback_extension_restriction _)

/-- Powers of the section polar meet the section finitely. -/
theorem hasFiniteIntersection_pow_right {f h : Germ 2} (hfh : HasFiniteIntersection f h)
    (n : ℕ) : HasFiniteIntersection f (h ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero]
      apply (hasFiniteIntersection_iff_exists_maximalIdeal_pow_le f 1).mpr
      refine ⟨0, ?_⟩
      rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      exact Ideal.subset_span (by simp)
  | succ n ih =>
      rw [pow_succ]
      exact (hasFiniteIntersection_mul_right_iff _ _ _).mpr ⟨ih, hfh⟩

/-- **Central polar identity.** Let `g` be a locally injective plane germ in
three-space with reduced section `v = g₀` meeting `g₂` finitely, and let
`Φ` generate its surface equations. Then
`2 δ(w) + i(v, J(v, g₂)) = 2 δ(v) + i(v, g^*(∂₁ Φ))`, where `w` is the
reduced section equation. -/
theorem two_mul_deltaInvariant_add_polar_eq (hg : g.HasInjectiveRepresentative)
    (Φ : Germ 3) (hker : RingHom.ker g.pullbackRingHom = Ideal.span {Φ})
    (haxis : HasFiniteIntersection (g.1.component 0) (g.1.component 2)) :
    ∃ (hJ : HasFiniteIntersection (g.1.component 0)
        (jacobian (g.1.component 0) (g.1.component 2)))
      (hP : HasFiniteIntersection (g.1.component 0)
        (g.pullbackRingHom (partialDerivative (1 : Fin 3) Φ))),
      2 * deltaInvariant D.imageEquation + intersectionMultiplicity _ _ hJ =
        2 * deltaInvariant (g.1.component 0) + intersectionMultiplicity _ _ hP := by
  classical
  have hsq := D.squarefree_component_zero
  have hcomp (j : Fin 3) : g.1.component j ∈ maximalIdeal 2 := by
    rw [← PointedMapGerm.pullback_coordinate]
    exact g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal j)
  obtain ⟨hpolar, -, hTv⟩ := exists_polar_intersection_identity (g.1.component 0)
    (g.1.component 2) (hcomp 0) (hcomp 2) hsq haxis
  have hJ : HasFiniteIntersection (g.1.component 0)
      (jacobian (g.1.component 0) (g.1.component 2)) := hpolar
  have hf := g.injective_isFiniteAtOrigin_two hg
  obtain ⟨N, hN⟩ := g.coordinateMinorIdeal_le_radical_imageConductor hf hg
    (g.coordinate_jacobian_mem_coordinateMinorIdeal 0 2)
  have hassoc := D.associated_restriction_imageEquation hg Φ hker _ hN
    (hasFiniteIntersection_pow_right hJ N)
  have hwu := D.imageEquation_not_isUnit
  have hwm : D.imageEquation ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    by_contra hne
    exact hwu (isUnit_of_valueRingHom_ne_zero hne)
  have hwsq := D.imageEquation_squarefree hg
  have hext : g.pullbackRingHom (hyperplaneExtension 2 (coordinate (1 : Fin 2))) =
      g.1.component 2 := by
    rw [hyperplaneExtension_coordinate]
    exact PointedMapGerm.pullback_coordinate g 2
  have hsource : HasFiniteIntersection (g.1.component 0)
      (g.pullbackRingHom (hyperplaneExtension 2 (coordinate (1 : Fin 2)))) := by
    rw [hext]
    exact haxis
  have haxisw : HasFiniteIntersection D.imageEquation (coordinate (1 : Fin 2)) :=
    (D.intersection_finite_iff hg _).mpr hsource
  obtain ⟨hpw, -, hTw⟩ := exists_first_partial_polar_identity D.imageEquation hwm hwsq haxisw
  obtain ⟨hP, hPeq⟩ := D.polar_intersection_eq hg Φ hassoc hpw
  have haxeq : intersectionMultiplicity D.imageEquation (coordinate (1 : Fin 2)) haxisw =
      intersectionMultiplicity (g.1.component 0) (g.1.component 2) haxis := by
    rw [D.intersection_eq hg _ haxisw hsource]
    exact intersectionMultiplicity_eq_of_pairIdeal_eq hsource haxis (by rw [hext])
  have hpolareq : polarIntersectionMultiplicity (g.1.component 0) (g.1.component 2) hpolar =
      intersectionMultiplicity _ _ hJ := rfl
  have hMw := two_mul_deltaInvariant hwsq
  have hMv := two_mul_deltaInvariant hsq
  have hvu : ¬ IsUnit (g.1.component 0) := fun h =>
    (isUnit_iff_valueRingHom_ne_zero.mp h) (mem_maximalIdeal_iff.mp (hcomp 0))
  have hAw := milnorBranchDefect_add_one _ hwsq.ne_zero hwu
  have hAv := milnorBranchDefect_add_one _ hsq.ne_zero hvu
  have hr := (D.finiteDimensional_and_deltaInvariant_imageEquation hg).2.2
  refine ⟨hJ, hP, ?_⟩
  omega

end SectionImageFactorization

end OnLeConjecture.Analytic
