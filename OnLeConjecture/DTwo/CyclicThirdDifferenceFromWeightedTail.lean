/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicThirdDifferenceFamily
public import OnLeConjecture.Analytic.CyclicScaledSourceSeparation

/-!
# Constructing the cyclic third difference from its weighted initial term

The strict weighted tail of the original third coordinate constructs a
convergent rescaled difference. No radial representative or divisibility
of its parameter-zero tail is included as an assumption.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

/-- The actual third difference associated with an arbitrary analytic
second-source branch. -/
theorem exists_cyclic_third_difference_of_weighted_tail
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0)
    (k p N : ℕ) (hk : 0 < k) (hp : 0 < p)
    (htail : ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) -
      coordinate (0 : Fin 2) ^ N ∈ twoWeightOrderIdeal k p (k * N + 1))
    (b : Source 3 → ℂ) (hb : AnalyticAt ℂ b 0) :
    ∃ D : Source 3 → ℂ, ∃ hD : AnalyticAt ℂ D 0,
      (∀ᶠ q in 𝓝 (0 : Source 3),
        G (cyclicScaledFirstSource k p q) 2 - G (cyclicScaledSecondSource k p b q) 2 =
          q 2 ^ (k * N) * D q) ∧
      coordinate (2 : Fin 3) ∣
        ofFunction D hD - (coordinate (0 : Fin 3) ^ N - coordinate (1 : Fin 3) ^ N) := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let H : ℂ × ℂ → Source 3 := fun q => ![0, 0, G (e.symm q) 2]
  have hcomp : AnalyticAt ℂ (fun q : ℂ × ℂ => G (e.symm q) 2) 0 := by
    have hf : AnalyticAt ℂ (fun q : Source 2 => G q 2) (e.symm 0) := by
      simpa only [map_zero] using analyticAt_pi_iff.mp hG 2
    exact hf.comp (e.symm.analyticAt 0)
  have hH : AnalyticAt ℂ H 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const
    · exact hcomp
  let P : Fin 3 → MvPolynomial (Fin 2) ℂ := ![0, 0, MvPolynomial.X 0 ^ N]
  let degrees : Fin 3 → ℕ := ![0, 0, k * N]
  have hP : ∀ i, (P i).IsWeightedHomogeneous ![k, p] (degrees i) := by
    intro i
    fin_cases i
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
    · simpa [P, degrees, Nat.mul_comm] using
        (MvPolynomial.isWeightedHomogeneous_X ℂ (![k, p] : Fin 2 → ℕ) 0).pow N
  have hzero : ∀ i : Fin 3, i ≠ 2 →
      DThree.pairRepresentativeComponentGerm H hH i = 0 := by
    intro i hi
    fin_cases i
    · rfl
    · rfl
    · exact (hi rfl).elim
  have htwo : DThree.pairRepresentativeComponentGerm H hH 2 =
      ofFunction (fun q => G q 2) (analyticAt_pi_iff.mp hG 2) := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro q
    change G (e.symm (e q)) 2 = G q 2
    rw [e.symm_apply_apply]
  have htails : ∀ i,
      DThree.pairRepresentativeComponentGerm H hH i - coordinatePolynomialAlgHom 2 (P i) ∈
        twoWeightOrderIdeal k p (degrees i + 1) := by
    intro i
    fin_cases i
    · change DThree.pairRepresentativeComponentGerm H hH 0 -
        coordinatePolynomialAlgHom 2 0 ∈ _
      rw [hzero 0 (by decide), map_zero, sub_self]
      exact Ideal.zero_mem _
    · change DThree.pairRepresentativeComponentGerm H hH 1 -
        coordinatePolynomialAlgHom 2 0 ∈ _
      rw [hzero 1 (by decide), map_zero, sub_self]
      exact Ideal.zero_mem _
    · change DThree.pairRepresentativeComponentGerm H hH 2 -
        coordinatePolynomialAlgHom 2 (MvPolynomial.X 0 ^ N) ∈ _
      rw [htwo, map_pow, coordinatePolynomialAlgHom_X]
      exact htail
  obtain ⟨remainder, hrem⟩ := exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
    k p hk hp degrees P hP H hH htails
  have hinitial : ∀ q : ℂ × ℂ, DThree.weightedPolynomialMap P q 2 = q.1 ^ N := by
    intro q
    simp [DThree.weightedPolynomialMap, P]
  obtain ⟨hD, hscale, hdiv⟩ := cyclicThirdDifference_analytic_and_scaling k p N degrees
    (DThree.weightedPolynomialMap P) H remainder b hb (b 0) rfl
    (hrem (0, 1)) (hrem (0, b 0)) hinitial
  refine ⟨cyclicThirdDifferenceFunction N remainder b, hD, ?_, hdiv⟩
  filter_upwards [hscale] with q hq
  simpa [H, e, twoWeightRadialSource, degrees,
    cyclicScaledFirstSource, cyclicScaledSecondSource] using hq

end OnLeConjecture.DTwo
