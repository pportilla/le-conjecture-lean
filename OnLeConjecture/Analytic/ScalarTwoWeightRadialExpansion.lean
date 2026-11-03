/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TwoWeightRadialExpansion

/-!
# Scalar analytic radial expansion for two positive weights

A strict weighted polynomial tail produces one convergent remainder,
valid near every affine chart point of the weighted scaling.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

theorem exists_scalar_twoWeight_radial_remainder
    (a b d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![a, b] d)
    (F : Source 2 → ℂ) (hF : AnalyticAt ℂ F 0)
    (htail : ofFunction F hF - coordinatePolynomialAlgHom 2 P ∈
      twoWeightOrderIdeal a b (d + 1)) :
    ∃ R : ℂ × (ℂ × ℂ) → ℂ, ∀ z : ℂ × ℂ,
      AnalyticAt ℂ R (0, z) ∧
        ∀ᶠ q in 𝓝 (0, z), F (twoWeightRadialSourceVector a b q) =
          q.1 ^ d * (MvPolynomial.eval
            ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm q.2) P + q.1 * R q) := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let H : ℂ × ℂ → Source 3 := fun q => ![0, 0, F (e.symm q)]
  have hcomp : AnalyticAt ℂ (F ∘ e.symm) 0 := by
    have hf : AnalyticAt ℂ F (e.symm 0) := by simpa only [map_zero] using hF
    exact hf.comp (e.symm.analyticAt 0)
  have hH : AnalyticAt ℂ H 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_const
    · exact hcomp
  let Ps : Fin 3 → MvPolynomial (Fin 2) ℂ := ![0, 0, P]
  let degrees : Fin 3 → ℕ := ![0, 0, d]
  have hPs : ∀ i, (Ps i).IsWeightedHomogeneous ![a, b] (degrees i) := by
    intro i
    fin_cases i
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
    · exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
    · exact hP
  have hzero : ∀ i : Fin 3, i ≠ 2 → DThree.pairRepresentativeComponentGerm H hH i = 0 := by
    intro i hi
    fin_cases i
    · rfl
    · rfl
    · exact (hi rfl).elim
  have htwo : DThree.pairRepresentativeComponentGerm H hH 2 = ofFunction F hF := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    apply Filter.Eventually.of_forall
    intro q
    change F (e.symm (e q)) = F q
    rw [e.symm_apply_apply]
  have htails : ∀ i,
      DThree.pairRepresentativeComponentGerm H hH i - coordinatePolynomialAlgHom 2 (Ps i) ∈
        twoWeightOrderIdeal a b (degrees i + 1) := by
    intro i
    fin_cases i
    · change DThree.pairRepresentativeComponentGerm H hH 0 - coordinatePolynomialAlgHom 2 0 ∈ _
      rw [hzero 0 (by decide), map_zero, sub_self]
      exact Ideal.zero_mem _
    · change DThree.pairRepresentativeComponentGerm H hH 1 - coordinatePolynomialAlgHom 2 0 ∈ _
      rw [hzero 1 (by decide), map_zero, sub_self]
      exact Ideal.zero_mem _
    · change DThree.pairRepresentativeComponentGerm H hH 2 - coordinatePolynomialAlgHom 2 P ∈ _
      rw [htwo]
      exact htail
  obtain ⟨R, hR⟩ := exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
    a b ha hb degrees Ps hPs H hH htails
  refine ⟨fun q => R q 2, fun z => ⟨analyticAt_pi_iff.mp (hR z).remainder_analyticAt 2, ?_⟩⟩
  filter_upwards [(hR z).expansion] with q hq
  simpa [H, e, Ps, degrees, DThree.weightedPolynomialMap, twoWeightRadialSourceVector] using hq 2

end OnLeConjecture.Analytic
