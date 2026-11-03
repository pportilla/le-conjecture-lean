/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HHardOddLocalOrder

/-!
# Root count for the odd H norm

The hard norm has profile degree `10N`. At the two parameters over `X = 1`,
its local orders are bounded by twice the corresponding orders of the
descended difference plus `N`. The profile of that descended difference
bounds the sum of its two orders. Hence the two distinguished norm orders do
not exhaust degree `10N`.
-/

public section

noncomputable section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open scoped WithZero

/-- The hard norm has a projective numerator zero away from the two points
over `X = 1`. A degree drop records the zero at the parameter infinity. -/
theorem exists_hHardOddNorm_numerator_zero_away_or_degree_drop
    (Rzero : MvPolynomial (Fin 2) ℂ) (coefficient : ℂ) (N : ℕ)
    (hNodd : Odd N) (hcoefficient : coefficient ≠ 0)
    (hRzero : Rzero.IsWeightedHomogeneous hFormWeight N)
    (hdifference : hConicDifference Rzero ≠ 0) :
    ∃ numerator : ℂ[X],
      numerator ≠ 0 ∧
      numerator.natDegree ≤ 10 * N ∧
      hHardOddNorm Rzero coefficient N =
        algebraMap ℂ[X] (RatFunc ℂ) numerator /
          algebraMap ℂ[X] (RatFunc ℂ)
            (hPoleProfileDenominator (2 * N) (4 * N)) ∧
      (numerator.natDegree < 10 * N ∨
        ∃ z : ℂ,
          z ≠ hConicOneRootPlus ∧
          z ≠ hConicOneRootMinus ∧
          numerator.IsRoot z) := by
  have hplusEquation := h_conic_one_roots_equations.1
  have hminusEquation := h_conic_one_roots_equations.2
  obtain ⟨kPlus, _hkPlus, hAplus⟩ :=
    exists_h_positive_local_order_at_one
      hplusEquation Rzero hRzero hdifference
  obtain ⟨kMinus, _hkMinus, hAminus⟩ :=
    exists_h_positive_local_order_at_one
      hminusEquation Rzero hRzero hdifference
  obtain ⟨rPlus, hnormPlus, hrPlus⟩ :=
    exists_hHardOddNorm_order_at_one_le
      Rzero coefficient hConicOneRootPlus N kPlus hNodd hcoefficient
        hplusEquation hAplus
  obtain ⟨rMinus, hnormMinus, hrMinus⟩ :=
    exists_hHardOddNorm_order_at_one_le
      Rzero coefficient hConicOneRootMinus N kMinus hNodd hcoefficient
        hminusEquation hAminus
  have hkSum : kPlus + kMinus ≤ N / 2 + 2 * N := by
    have hpole := HasHPoleProfile.projectivePoleDegree_le
      (hasHPoleProfile_hConicDifference N Rzero hRzero)
    exact (h_two_finite_orders_le_pole_degree hdifference
      h_conic_one_roots_ne hAplus hAminus).trans hpole
  have hstrict : rPlus + rMinus < 2 * N + 2 * (4 * N) := by
    have hNpos : 0 < N := hNodd.pos
    omega
  have hnormNe : hHardOddNorm Rzero coefficient N ≠ 0 :=
    h_ratFunc_ne_zero_of_finite_order hnormPlus
  obtain ⟨numerator, hnumerator, hdegree, hrepresentation, hroot⟩ :=
    HasHPoleProfile.exists_numerator_zero_away_or_degree_drop
      (hasHPoleProfile_hHardOddNorm Rzero coefficient N hRzero)
      hnormNe h_conic_one_roots_ne
      (h_pole_profile_denominator_eval_ne_zero_at_one_root
        (2 * N) (4 * N) hplusEquation)
      (h_pole_profile_denominator_eval_ne_zero_at_one_root
        (2 * N) (4 * N) hminusEquation)
      hnormPlus hnormMinus hstrict
  refine ⟨numerator, hnumerator, by omega, hrepresentation, ?_⟩
  rcases hroot with hdrop | hfinite
  · exact Or.inl (by omega)
  · exact Or.inr hfinite

end OnLeConjecture.DThree
