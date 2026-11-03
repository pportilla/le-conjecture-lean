/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicHypersurfaceCollisionFactorization
public import OnLeConjecture.Analytic.SingleAxisSupportContradiction

/-!
# Collision on a component of the reducible first-plane hypersurface

When the first plane equation is equivalent to `U Xi = 0`, its `Xi = 0`
component retains the scaling parameter. The odd third difference has
positive order on the special axis, which contradicts local injectivity.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic.CyclicCover

open OnLeConjecture.Analytic.Germ

@[expose] noncomputable def secondZeroSection : PointedMapGerm 2 3 :=
  PointedMapGerm.ofFunction (fun q : Source 2 => ![q 0, 0, q 1])
    (by
      apply AnalyticAt.pi
      intro i
      fin_cases i
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0
      · exact analyticAt_const
      · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticAt 0)
    (by ext i; fin_cases i <;> rfl)

@[simp] theorem secondZeroSection_pullback_second :
    secondZeroSection.pullbackRingHom (coordinate (1 : Fin 3)) = 0 := by
  apply Subtype.ext
  rfl

@[simp] theorem secondZeroSection_pullback_last :
    secondZeroSection.pullbackRingHom (coordinate (2 : Fin 3)) =
      coordinate (1 : Fin 2) := by
  apply Subtype.ext
  rfl

theorem secondZeroSection_axis_eq_cover_one (F : Germ 3) :
    lineRestriction (![1, 0] : Source 2) (secondZeroSection.pullbackRingHom F) =
      lineRestriction (![1, 0] : Source 2) ((coverGerm 1 (by decide)).pullbackRingHom F) := by
  obtain ⟨f, hf, rfl⟩ := exists_ofFunction F
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro q
  change f (![(lineMap (![1, 0] : Source 2) q) 0, 0,
    (lineMap (![1, 0] : Source 2) q) 1]) =
      f (coverFunction 1 (lineMap (![1, 0] : Source 2) q))
  simp [lineMap_apply, coverFunction]

theorem secondZeroSection_transported_pullback_forward
    (e : PointedEquivGerm 3) (F : Germ 3) :
    (e.inverse.comp secondZeroSection).pullbackRingHom (e.forward.pullbackRingHom F) =
      secondZeroSection.pullbackRingHom F := by
  rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    show e.inverse.pullbackRingHom (e.forward.pullbackRingHom F) = F from
      e.pullbackRingEquiv.symm_apply_apply F]

/-- The reducible hypersurface alternative cannot occur for an injective
prepared map with an odd third initial coordinate. -/
theorem false_of_reducible_hypersurface_scaled_injectivity
    (G : Source 2 → Source 3)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p N : ℕ) (hk : 0 < k) (hp : 0 < p) (hN : Odd N)
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 1)
    (degrees : Fin 3 → ℕ) (R : Source 3 → Source 3) (hR : AnalyticAt ℂ R 0)
    (hscale : ∀ᶠ q in 𝓝 (0 : Source 3), ∀ i,
      G (cyclicScaledFirstSource k p q) i - G (cyclicScaledSecondSource k p b q) i =
        q 2 ^ degrees i * R q i)
    (H D h u a : Germ 3) (hu : IsUnit u) (ha : IsUnit a)
    (hR0 : ofFunction (fun q => R q 0) (analyticAt_pi_iff.mp hR 0) = H)
    (hR1 : ofFunction (fun q => R q 1) (analyticAt_pi_iff.mp hR 1) = 0)
    (hR2 : ofFunction (fun q => R q 2) (analyticAt_pi_iff.mp hR 2) = D)
    (e : PointedEquivGerm 3)
    (he0 : e.forward.pullbackRingHom (coordinate (0 : Fin 3)) = coordinate 0 - coordinate 1)
    (he1 : e.forward.pullbackRingHom (coordinate (1 : Fin 3)) =
      (coordinate 0 + coordinate 1 + h) * u)
    (he2 : e.forward.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate 2)
    (heq : e.forward.pullbackRingHom (coordinate 0 * coordinate 1) = a * H)
    (hh : coordinate (2 : Fin 3) ∣ h)
    (hD : coordinate (2 : Fin 3) ∣
      D - (coordinate (0 : Fin 3) ^ N - coordinate (1 : Fin 3) ^ N)) : False := by
  let φ := e.inverse.comp secondZeroSection
  obtain ⟨Φ, hΦ, hΦ0, hφ⟩ := φ.exists_ofFunction
  have hcompose : AnalyticAt ℂ (fun z => R (Φ z)) (0 : Source 2) := by
    apply AnalyticAt.comp (x := (0 : Source 2)) _ hΦ
    simpa only [hΦ0] using hR
  have hΦH : φ.pullbackRingHom H = 0 := by
    have h := congrArg φ.pullbackRingHom heq
    rw [secondZeroSection_transported_pullback_forward, map_mul,
      secondZeroSection_pullback_second, mul_zero, map_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (ha.map φ.pullbackRingHom).ne_zero
  have hparameter : ∀ᶠ z in 𝓝 (0 : Source 2), Φ z 2 = z 1 := by
    have h : φ.pullbackRingHom (coordinate (2 : Fin 3)) = coordinate (1 : Fin 2) := by
      rw [← he2, secondZeroSection_transported_pullback_forward, secondZeroSection_pullback_last]
    rw [hφ] at h
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val h)
  have hplane : ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 0 = 0 ∧ R (Φ z) 1 = 0 := by
    have h0 := congrArg φ.pullbackRingHom hR0
    have h1 := congrArg φ.pullbackRingHom hR1
    rw [hΦH, hφ] at h0
    rw [map_zero, hφ] at h1
    exact (Filter.Germ.coe_eq.mp (congrArg Subtype.val h0)).and
      (Filter.Germ.coe_eq.mp (congrArg Subtype.val h1))
  have hF : AnalyticAt ℂ (fun z => R (Φ z) 2) 0 := analyticAt_pi_iff.mp hcompose 2
  have hrep : ofFunction (fun z => R (Φ z) 2) hF = φ.pullbackRingHom D := by
    rw [← hR2, hφ]
    rfl
  have ht : Tendsto Φ (𝓝 (0 : Source 2)) (𝓝 (0 : Source 3)) := by
    simpa only [ContinuousAt, hΦ0] using hΦ.continuousAt
  have hsep := eventually_cyclic_scaled_equal_images_implies_parameter_zero
    G hinjective k p hk hp b hb hb0
  have hsupport : ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 2 = 0 → z 1 = 0 := by
    filter_upwards [ht.eventually hsep, ht.eventually hscale, hparameter, hplane]
      with z hseparation hsc hparam hpl hthird
    have hsame : G (cyclicScaledFirstSource k p (Φ z)) =
        G (cyclicScaledSecondSource k p b (Φ z)) := by
      ext i
      apply sub_eq_zero.mp
      rw [hsc]
      have hz : R (Φ z) i = 0 := by
        fin_cases i
        · exact hpl.1
        · exact hpl.2
        · exact hthird
      rw [hz, mul_zero]
    have hzero := hseparation hsame
    rwa [hparam] at hzero
  have haxis : lineRestriction (![1, 0] : Source 2)
      (ofFunction (fun z => R (Φ z) 2) hF) =
        constRingHom 1 (2 * (1 / 2 : ℂ) ^ N) * coordinate (0 : Fin 1) ^ N := by
    rw [hrep, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
      secondZeroSection_axis_eq_cover_one]
    simpa only [transportedAxisPullback, RingHom.comp_apply, one_mul] using
      transportedAxisPullback_odd_difference
      1 N (by decide) hN e h u D hu he0 he1 he2 hh hD
  exact not_zeros_supported_on_second_axis_of_positive_first_axis_order
    (fun z => R (Φ z) 2) hF N hN.pos (2 * (1 / 2 : ℂ) ^ N)
    (odd_difference_axis_coefficient_ne_zero N) haxis hsupport

end OnLeConjecture.Analytic.CyclicCover
