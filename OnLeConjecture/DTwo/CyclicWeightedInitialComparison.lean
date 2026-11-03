/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicWeightedArcPlaneFiber
public import OnLeConjecture.DTwo.CyclicWeightedArcConstruction
public import OnLeConjecture.DTwo.CyclicInvariantCoefficientExclusion
public import OnLeConjecture.Analytic.WeightedArcTargetSubtraction

/-!
# Weighted initial comparison from the prepared analytic cyclic map

The local descent and actual lifted arcs determine the initial polynomial
difference after any target subtraction depending on the first two
coordinates. The index, coefficient, comparison scalar, and all limiting
arcs are constructed from the original analytic map.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The weighted comparison on every nonsingular affine point of the
limiting component, obtained without an assumed component identity. -/
theorem exists_cyclic_weighted_initial_comparison
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0)
    (hinjective : ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn G s)
    (k p N : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hN : Odd N)
    (β : ℂ → ℂ) (hβ : AnalyticAt ℂ β 0) (hc : β 0 ≠ 0)
    (hP : ∀ᶠ q in 𝓝 (0 : Source 2), G q 0 = q 0 ^ 2 + q 1 ^ k)
    (hQ : ∀ᶠ q in 𝓝 (0 : Source 2), G q 1 = q 0 ^ p + q 1 ^ k * β (q 1))
    (htail : ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) -
      coordinate (0 : Fin 2) ^ N ∈ twoWeightOrderIdeal k p (k * N + 1))
    (ζ : ℂ) (hζ : ζ ^ k = 1) (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) :
    ∃ j : ℕ, 0 < j ∧ ζ ^ j ≠ 1 ∧
      ∃ J : MvPolynomial (Fin 1) ℂ,
        cyclicCoefficientGerm β hβ - coordinatePolynomialAlgHom 1 J ∈
          maximalIdeal 1 ^ (j + 1) ∧
        MvPolynomial.coeff (Finsupp.single 0 j) J ≠ 0 ∧
        (∀ i < j, J.coeff (Finsupp.single 0 i) = 0 ∨ ζ ^ i = 1) ∧
        ∃ cD : ℂ, cD ≠ 0 ∧
          ∀ F : Source 2 → ℂ, ∀ hF : AnalyticAt ℂ F 0, ∀ Ψ : Source 2 → ℂ,
            (∀ᶠ q in 𝓝 (0 : Source 2), F q = G q 2 - Ψ (![G q 0, G q 1])) →
            ∀ d : ℕ, ∀ P : MvPolynomial (Fin 2) ℂ,
              P.IsWeightedHomogeneous ![k + j, 2] d →
              ofFunction F hF - coordinatePolynomialAlgHom 2 P ∈
                twoWeightOrderIdeal (k + j) 2 (d + 1) →
              ∀ s S : ℂ, S ≠ 0 →
                S ^ 2 = s ^ 2 +
                  (-(MvPolynomial.coeff (Finsupp.single 0 j) J / β 0) * (1 - ζ ^ j)) →
                d ≤ (k + j) * N ∧
                  (d < (k + j) * N →
                    MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P = 0) ∧
                  (d = (k + j) * N →
                    MvPolynomial.eval (![s, 1]) P - MvPolynomial.eval (![S, ζ]) P =
                      cD * (s - S) ^ N) := by
  have hp0 : 0 < p := by omega
  have hnoninv := cyclicPrepared_coefficient_noninvariant G hG hinjective k p N hk hp hN
    β hβ hc hP hQ htail ζ hζ hζ0 hζ1
  obtain ⟨z, hz, hz0, hsol, D, hD, hscale, _, v, hv, hfactor⟩ :=
    exists_cyclicPrepared_branch_descent G hG hinjective k p N hk hp hN
      β hβ hc hP hQ htail ζ hζ hζ0 hζ1 hnoninv
  obtain ⟨j, hj, hchar, ε, hε, hε0, K, hK, hH, J, hJ, hJc, hεvalue, hprevious⟩ :=
    cyclicPlane_weighted_defect_decomposition k p hk hp β hβ hc
      ζ hζ hζ0 z hz hz0 hsol hnoninv
  refine ⟨j, hj, hchar, J, hJ, hJc, hprevious, valueRingHom 3 v,
    valueRingHom_ne_zero_of_isUnit hv, ?_⟩
  intro F hF Ψ hFrep d P hhom hnewtail s S hS hpoint
  have hpoint' : S ^ 2 = s ^ 2 + ε 0 := by rw [hεvalue]; exact hpoint
  obtain ⟨hr, B, hB, hB0, hne, hplane⟩ :=
    exists_cyclicPlane_weighted_arc_of_defect_decomposition k p j hk hp hj ε hε hε0 K hK
      (cyclicFirstPlaneGerm k p z hz) hH s S hS hpoint'
  let r := k * (p - 2) + p * j
  have hdegree : 2 * k + r = p * (k + j) := by
    have h := Nat.sub_add_cancel (show 2 ≤ p by omega)
    dsimp only [r]
    nlinarith
  have hb := cyclicPowerDifferenceBranch_analyticAt p z hz
  obtain ⟨hbArc, hbArc0, U, hU, hU0, hUvalue, hunit⟩ :=
    exists_cyclicWeightedArc_image_difference_unit G k p r (k + j) N hr hdegree
      (cyclicPowerDifferenceBranch p z) hb D hD hscale s B hB hne
      (cyclicFirstPlaneGerm k p z hz) v hv hplane hfactor
  have hbArcζ : (cyclicPowerDifferenceBranch p z ∘ cyclicWeightedArcFunction r s B) 0 = ζ := by
    rw [hbArc0, cyclicPowerDifferenceBranch_zero, hz0]
  have hplaneImages := cyclicWeightedArc_plane_images_agree G k p r (k + j) hk hp hr hdegree
    β hP hQ z hz hsol s B hB hplane
  have hpreserve := weightedArc_difference_after_target_subtraction G F Ψ hFrep
    (k + j) 2 p (by omega) (by decide) hp0 (fun _ => s) (fun _ => 1)
    B (cyclicPowerDifferenceBranch p z ∘ cyclicWeightedArcFunction r s B)
    analyticAt_const analyticAt_const hB hbArc hplaneImages
  have hFunit : ∀ᶠ q in 𝓝 (0 : Source 1),
      F (weightedSourceArc (k + j) 2 p (fun _ => s) (fun _ => 1) q) -
          F (weightedSourceArc (k + j) 2 p B
            (cyclicPowerDifferenceBranch p z ∘ cyclicWeightedArcFunction r s B) q) =
        q 0 ^ (p * ((k + j) * N)) * U q := by
    filter_upwards [hpreserve, hunit] with q hq huq
    exact hq.trans huq
  obtain ⟨hd, hlt, heq⟩ := weightedArc_initial_polynomial_comparison
    (k + j) 2 p d ((k + j) * N) (by omega) (by decide) hp0 P hhom F hF hnewtail
    (fun _ => s) (fun _ => 1) B (cyclicPowerDifferenceBranch p z ∘ cyclicWeightedArcFunction r s B)
    analyticAt_const analyticAt_const hB hbArc U hU hU0 hFunit
  refine ⟨hd, ?_, ?_⟩
  · intro h
    simpa only [hB0, hbArcζ] using hlt h
  · intro h
    have hc := heq h
    rw [hUvalue, hB0] at hc
    simpa only [hB0, hbArcζ, mul_comm] using hc

end OnLeConjecture.DTwo
