/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicCoverAxisRestriction
public import OnLeConjecture.Analytic.CyclicScaledSourceSeparation
public import OnLeConjecture.Analytic.PairRepresentative

/-!
# Cyclic hypersurface factorization from analytic injectivity

The actual scaled image differences and the hypersurface coordinate
identities determine the support and axis order on the cyclic cover.
Injectivity then yields the unit factorization modulo the first plane
equation, without a separate zero-set or descent hypothesis.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic.CyclicCover

open OnLeConjecture.Analytic.Germ

theorem transportedCover_pullback_forward
    (r : ℕ) (hr : 0 < r) (e : PointedEquivGerm 3) (F : Germ 3) :
    (e.inverse.comp (coverGerm r hr)).pullbackRingHom
      (e.forward.pullbackRingHom F) = (coverGerm r hr).pullbackRingHom F := by
  rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    show e.inverse.pullbackRingHom (e.forward.pullbackRingHom F) = F from
      e.pullbackRingEquiv.symm_apply_apply F]

theorem transportedCover_pullback_equation
    (r : ℕ) (hr : 0 < r) (e : PointedEquivGerm 3) (a H : Germ 3)
    (ha : IsUnit a)
    (heq : e.forward.pullbackRingHom (relationGerm r) = a * H) :
    (e.inverse.comp (coverGerm r hr)).pullbackRingHom H = 0 := by
  have h := congrArg (e.inverse.comp (coverGerm r hr)).pullbackRingHom heq
  rw [transportedCover_pullback_forward, coverGerm_pullback_relation, map_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left
    (ha.map (e.inverse.comp (coverGerm r hr)).pullbackRingHom).ne_zero

/-- A rescaled third-coordinate difference factors as the required power
of the difference coordinate on the actual first-plane hypersurface. -/
theorem exists_unit_factor_mod_equation_of_scaled_injectivity
    (G : Source 2 → Source 3)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p r N : ℕ) (hk : 0 < k) (hp : 0 < p) (hr : 0 < r) (hN : Odd N)
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
    (heq : e.forward.pullbackRingHom (relationGerm r) = a * H)
    (hh : coordinate (2 : Fin 3) ∣ h)
    (hD : coordinate (2 : Fin 3) ∣
      D - (coordinate (0 : Fin 3) ^ N - coordinate (1 : Fin 3) ^ N)) :
    ∃ v : Germ 3, IsUnit v ∧
      D - (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) ^ N * v ∈ Ideal.span {H} := by
  let φ := e.inverse.comp (coverGerm r hr)
  obtain ⟨Φ, hΦ, hΦ0, hφ⟩ := φ.exists_ofFunction
  have hcompose : AnalyticAt ℂ (fun z => R (Φ z)) (0 : Source 2) := by
    apply AnalyticAt.comp (x := (0 : Source 2)) _ hΦ
    simpa only [hΦ0] using hR
  have hΦH : φ.pullbackRingHom H = 0 :=
    transportedCover_pullback_equation r hr e a H ha heq
  have hparameter : ∀ᶠ z in 𝓝 (0 : Source 2), Φ z 2 = z 0 * z 1 := by
    have h : φ.pullbackRingHom (coordinate (2 : Fin 3)) =
        coordinate (0 : Fin 2) * coordinate (1 : Fin 2) := by
      rw [← he2, transportedCover_pullback_forward, coverGerm_pullback_last]
    rw [hφ] at h
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val h)
  have hplane : ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 0 = 0 ∧ R (Φ z) 1 = 0 := by
    have h0 := congrArg φ.pullbackRingHom hR0
    have h1 := congrArg φ.pullbackRingHom hR1
    rw [hΦH, hφ] at h0
    rw [map_zero, hφ] at h1
    have hz0 : ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 0 = 0 :=
      Filter.Germ.coe_eq.mp (congrArg Subtype.val h0)
    have hz1 : ∀ᶠ z in 𝓝 (0 : Source 2), R (Φ z) 1 = 0 :=
      Filter.Germ.coe_eq.mp (congrArg Subtype.val h1)
    exact hz0.and hz1
  have hF : AnalyticAt ℂ (fun z => R (Φ z) 2) 0 := analyticAt_pi_iff.mp hcompose 2
  have hrep : ofFunction (fun z => R (Φ z) 2) hF = φ.pullbackRingHom D := by
    rw [← hR2, hφ]
    rfl
  have hsupport := eventually_cyclic_rescaled_third_zero_implies_axes G hinjective
    k p hk hp b hb hb0 degrees R hscale Φ hΦ hΦ0 hparameter hplane
  have haxis : lineRestriction (![1, 0] : Source 2)
      (ofFunction (fun z => R (Φ z) 2) hF) =
        constRingHom 1 (2 * (1 / 2 : ℂ) ^ N) * coordinate (0 : Fin 1) ^ (r * N) := by
    rw [hrep, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    exact transportedAxisPullback_odd_difference r N hr hN e h u D hu he0 he1 he2 hh hD
  exact exists_unit_factor_mod_equation_of_axes_support r N hr e H
    (coordinate 0 - coordinate 1) a D he0 heq (fun z => R (Φ z) 2) hF hrep
    (2 * (1 / 2 : ℂ) ^ N) (odd_difference_axis_coefficient_ne_zero N) hsupport haxis

end OnLeConjecture.Analytic.CyclicCover
