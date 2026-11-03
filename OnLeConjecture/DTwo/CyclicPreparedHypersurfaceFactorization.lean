/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicRescaledImageDifference
public import OnLeConjecture.Analytic.CyclicHypersurfaceCollisionFactorization

/-!
# Factorization of the third difference for the prepared cyclic map

The implicit branch, its exact defect order, the hypersurface coordinates,
and injectivity give the analytic unit factorization. The rescaled third
difference need only have its actual scaling identity and the prescribed
parameter-zero restriction.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def cyclicFirstPlaneGerm
    (k p : ℕ) (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) : Germ 3 :=
  coordinate (0 : Fin 3) ^ 2 - coordinate (1 : Fin 3) ^ 2 +
    coordinate 2 ^ (k * (p - 2)) *
      (1 - ofFunction (cyclicPowerDifferenceBranch p z)
        (cyclicPowerDifferenceBranch_analyticAt p z hz) ^ k)

/-- The analytic factorization for every actual branch of the second
plane equation associated with a noninvariant root of unity. -/
theorem cyclicPlane_branch_third_factorization
    (G : Source 2 → Source 3)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p N d : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hN : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : ∀ᶠ q in 𝓝 (0 : Source 2), G q 0 = q 0 ^ 2 + q 1 ^ k)
    (hQ : ∀ᶠ q in 𝓝 (0 : Source 2), G q 1 = q 0 ^ p + q 1 ^ k * β (q 1))
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1)
    (hne : cyclicCoefficientGerm β hβ -
      (diagonalPointedEquiv (fun _ : Fin 1 => ζ) (fun _ => hζ0)).forward.pullbackRingHom
        (cyclicCoefficientGerm β hβ) ≠ 0)
    (z : ℂ × ℂ → ℂ) (hz : AnalyticAt ℂ z 0) (hz0 : z 0 = ζ)
    (hsol : ∀ᶠ q in 𝓝 (0 : ℂ × ℂ),
      q.1 + β (q.2 ^ p) - z q ^ k * β (q.2 ^ p * z q) = 0)
    (D : Source 3 → ℂ) (hD : AnalyticAt ℂ D 0)
    (hthird : ∀ᶠ q in 𝓝 (0 : Source 3),
      G (cyclicScaledFirstSource k p q) 2 -
          G (cyclicScaledSecondSource k p (cyclicPowerDifferenceBranch p z) q) 2 =
        q 2 ^ d * D q)
    (htail : coordinate (2 : Fin 3) ∣
      ofFunction D hD - (coordinate (0 : Fin 3) ^ N - coordinate (1 : Fin 3) ^ N)) :
    ∃ v : Germ 3, IsUnit v ∧
      ofFunction D hD - (coordinate (0 : Fin 3) - coordinate (1 : Fin 3)) ^ N * v ∈
        Ideal.span {cyclicFirstPlaneGerm k p z hz} := by
  have hp0 : 0 < p := by omega
  let ν := k * (p - 2)
  have hν : 0 < ν := Nat.mul_pos hk (by omega)
  let b := cyclicPowerDifferenceBranch p z
  have hb := cyclicPowerDifferenceBranch_analyticAt p z hz
  have hb0 : b 0 ≠ 1 := by
    change cyclicPowerDifferenceBranch p z 0 ≠ 1
    rw [cyclicPowerDifferenceBranch_zero, hz0]
    exact hζ1
  let B := cyclicBranchDefectGerm k z hz
  obtain ⟨j, hj, _, u, hδ, _⟩ :=
    cyclicPlane_parameter_defect_order k p hk hp0 β hβ hc ζ hζ hζ0 z hz hz0 hsol hne
  let r := ν + p * j
  have hr : 0 < r := by dsimp only [r]; omega
  let ε : (Germ 3)ˣ := Units.map cyclicLastExtension u
  have hdefect : coordinate (2 : Fin 3) ^ ν * cyclicParameterDefect p B =
      coordinate 2 ^ r * (↑ε : Germ 3) := by
    rw [hδ, ← mul_assoc, ← pow_add]
    rfl
  obtain ⟨K, h, d', hh, _, hhEq, hd0, hd1, _, hplane⟩ :=
    exists_cyclicPlane_hypersurface_coordinates p ν hp B
  obtain ⟨e, he0, he1, he2, heq⟩ :=
    Analytic.CyclicCover.exists_hypersurface_coordinates h hh ε r
  have hH : cyclicFirstPlaneGerm k p z hz =
      (coordinate 0 - coordinate 1) * (coordinate 0 + coordinate 1 + h) +
        coordinate 2 ^ r * (↑ε : Germ 3) := by
    rw [map_mul, hd0, hd1, hdefect] at hplane
    rw [cyclicBranchDefectGerm_powerDifference_pullback] at hplane
    exact hplane
  have heH : e.forward.pullbackRingHom (Analytic.CyclicCover.relationGerm r) =
      -(↑(ε⁻¹) : Germ 3) * cyclicFirstPlaneGerm k p z hz := by
    rw [hH]
    exact heq
  have hdiv : coordinate (2 : Fin 3) ∣ h := by
    rw [hhEq]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self _ hν.ne') _) _
  let R := cyclicRescaledImageDifference k p β b D
  have hR := cyclicRescaledImageDifference_analyticAt k p hp0 β hβ b D hb hD
  have hscale := eventually_cyclicRescaledImageDifference_scaling G k p d hk
    (by omega) β b D hb hP hQ hthird
  have hR0 : ofFunction (fun q => R q 0) (analyticAt_pi_iff.mp hR 0) =
      cyclicFirstPlaneGerm k p z hz := by
    apply Subtype.ext
    rfl
  have hR1 : ofFunction (fun q => R q 1) (analyticAt_pi_iff.mp hR 1) = 0 := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact cyclicPowerDifferenceBranch_solves k p β z hsol
  have hR2 : ofFunction (fun q => R q 2) (analyticAt_pi_iff.mp hR 2) = ofFunction D hD := by
    apply Subtype.ext
    rfl
  have he1' : e.forward.pullbackRingHom (coordinate (1 : Fin 3)) =
      (coordinate 0 + coordinate 1 + h) * (-(↑(ε⁻¹) : Germ 3)) := by
    rw [he1]
    ring
  exact Analytic.CyclicCover.exists_unit_factor_mod_equation_of_scaled_injectivity
    G hinjective k p r N hk hp0 hr hN b hb hb0 ![2 * k, k * p, d] R hR hscale
    (cyclicFirstPlaneGerm k p z hz) (ofFunction D hD) h
    (-(↑(ε⁻¹) : Germ 3)) (-(↑(ε⁻¹) : Germ 3)) (ε⁻¹).isUnit.neg (ε⁻¹).isUnit.neg
    hR0 hR1 hR2 e he0 he1' he2 heH hdiv htail

end OnLeConjecture.DTwo
