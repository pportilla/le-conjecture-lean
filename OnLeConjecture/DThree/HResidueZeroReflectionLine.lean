/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.HResidueZeroOrdinaryBranchPersistence

/-!
# H reflection line with residue zero

An H reflection line collision determines ordinary analytic source branch
data. Taking roots of its nonzero second coordinates then supplies the
weighted residue zero contradiction for every positive source weight.
-/

public section

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A reflection line collision determines ordinary H source branch data. -/
theorem exists_hHardOddOrdinarySourceBranchData_of_reflectionLine
    {R : Form ℂ} {N : ℕ}
    (hR : R.IsHomogeneous N)
    (data : HReflectionLineCollisionCertificate R) :
    Nonempty (HHardOddOrdinarySourceBranchData R) := by
  let z := data.x / data.t
  let p := eRotationLinePolynomial (-1) R
  have hp : p ≠ 0 :=
    eRotationLinePolynomial_ne_zero hR data.reflectionDifference_ne_zero
  have hz : p.IsRoot z := data.chart_root hR
  obtain ⟨horder, quotient, hfactor, hquotient⟩ :=
    exists_polynomial_local_factorization hp hz
  let firstX : ℂ → ℂ := fun lambda ↦ z + lambda
  let secondPoint : ℂ → Fin 2 → ℂ :=
    fun lambda ↦ ![z + lambda, -1]
  let unit : ℂ → ℂ := fun lambda ↦ quotient.eval (z + lambda)
  refine ⟨{
    firstX := firstX
    secondPoint := secondPoint
    secondX := z
    secondT := -1
    order := p.rootMultiplicity z
    unit := unit
    firstX_analyticAt := analyticAt_const.add analyticAt_id
    secondPoint_analyticAt := ?_
    secondPoint_zero := ?_
    secondT_ne_zero := by norm_num
    chart_points_ne := ?_
    plane_zero := ?_
    order_pos := horder
    unit_analyticAt := ?_
    unit_zero_ne := ?_
    third_factor := ?_
  }⟩
  · rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_const.add analyticAt_id
    · exact analyticAt_const
  · ext i
    fin_cases i
    all_goals simp [secondPoint]
  · intro hequal
    have hsecond := congrArg Prod.snd hequal
    norm_num at hsecond
  · filter_upwards [] with lambda
    funext i
    fin_cases i
    all_goals simp [hCollisionPlaneDifference, firstX, secondPoint,
      hP, hQ]
  · exact analyticAt_polynomial_eval_add quotient z
  · simpa [unit] using hquotient
  · filter_upwards [] with lambda
    calc
      MvPolynomial.eval ![firstX lambda, 1] R -
          MvPolynomial.eval
            ![secondPoint lambda 0, secondPoint lambda 1] R =
          p.eval (z + lambda) := by
        rw [eRotationLinePolynomial_eval]
        simp only [firstX, secondPoint]
        change MvPolynomial.eval ![z + lambda, 1] R -
            MvPolynomial.eval ![z + lambda, -1] R =
          MvPolynomial.eval ![z + lambda, 1]
            (R - eRotateForm (-1) R)
        rw [map_sub, eRotateForm_eval]
        norm_num
      _ = lambda ^ p.rootMultiplicity z * quotient.eval (z + lambda) :=
        polynomial_eval_add_factorization hfactor lambda
      _ = lambda ^ p.rootMultiplicity z * unit lambda := rfl

/-- A reflection line collision excludes injectivity after every positive
power substitution. -/
theorem hReflectionLineResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    {R : Form ℂ} {N : ℕ}
    (a : ℕ) (ha : 0 < a)
    (hR : R.IsHomogeneous N)
    (data : HReflectionLineCollisionCertificate R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (hResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (hQuadraticWeightedDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨sourceData⟩ :=
    exists_hHardOddOrdinarySourceBranchData_of_reflectionLine hR data
  exact
    hOrdinarySourceBranchResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
      a N ha R hR sourceData representative hanalytic hzero htail

end OnLeConjecture.DThree
