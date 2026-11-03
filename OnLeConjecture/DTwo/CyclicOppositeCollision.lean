/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicOppositeBranch

/-!
# Persistence of opposite-sign cyclic collisions

The chart eliminates both first coordinates. Its invertible plane
derivative includes second source points on the first coordinate axis.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

/-- Substitution `t = yᵏ` in an invariant polynomial. -/
@[expose] noncomputable def cyclicInvariantLift (k : ℕ)
    (F : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ :=
  aeval ![X 0, X 1 ^ k] F

theorem cyclicInvariantLift_eval (k : ℕ) (F : MvPolynomial (Fin 2) ℂ) (x y : ℂ) :
    eval ![x, y] (cyclicInvariantLift k F) = eval ![x, y ^ k] F := by
  change aeval ![x, y] (aeval _ F) = aeval _ F
  rw [comp_aeval_apply]
  apply congrArg (fun g : Fin 2 → ℂ ↦ aeval g F)
  funext i
  fin_cases i <;> simp

/-- Evaluation of the rank two decomposition on the opposite-sign graph. -/
theorem cyclicInvariantLift_opposite_difference
    (k p : ℕ) (hp : Odd p) (c : ℂ) (hc : c ≠ 0)
    (F A B : MvPolynomial (Fin 2) ℂ)
    (hdecomp : F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B)
    (x Y : ℂ) (hcurve : 2 * x ^ p = c * (Y ^ k - 1)) :
    eval ![x, 1] (cyclicInvariantLift k F) -
      eval ![-x, Y] (cyclicInvariantLift k F) =
        2 * x * (cyclicOddRestriction p c B).eval x := by
  have hreflection : eval ![x, 1] (cyclicInvariantReflection p c F) =
      eval ![-x, 1 + (2 / c) * x ^ p] F := by
    change aeval ![x, 1] (aeval _ F) = aeval _ F
    rw [comp_aeval_apply]
    apply congrArg (fun g : Fin 2 → ℂ ↦ aeval g F)
    funext i
    fin_cases i <;> simp
  have hY : 1 + (2 / c) * x ^ p = Y ^ k := by
    field_simp
    linear_combination hcurve
  have hdiff := congrArg (eval ![x, 1])
    (cyclicInvariant_reflection_difference p hp c hc F A B hdecomp)
  rw [map_sub, hreflection, hY, map_mul, map_mul, eval_C, eval_X,
    cyclicInvariantBaseHom_eval] at hdiff
  simpa only [cyclicInvariantLift_eval, one_pow, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, cyclicOddRestriction_eval] using hdiff

/-- A cyclic permutation puts the second `y` coordinate first. -/
@[expose] noncomputable def cyclicOppositeRotate (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![q 1, q 2, q 0]

theorem analyticAt_cyclicOppositeRotate (q : Fin 3 → ℂ) :
    AnalyticAt ℂ cyclicOppositeRotate q := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (1 : Fin 3)).analyticAt q
  · exact (ContinuousLinearMap.proj (R := ℂ) (2 : Fin 3)).analyticAt q
  · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 3)).analyticAt q

private theorem analyticAt_cyclicOppositeRotate_parameter (q : ℂ × (Fin 3 → ℂ)) :
    AnalyticAt ℂ (fun q : ℂ × (Fin 3 → ℂ) ↦ (q.1, cyclicOppositeRotate q.2)) q :=
  analyticAt_fst.prod ((analyticAt_cyclicOppositeRotate q.2).fun_comp analyticAt_snd)

/-- Every perturbation of an opposite-sign collision with a nonzero
residual restriction has full zeros in every neighborhood of the collision. -/
theorem eventually_exists_cyclicOppositeZero_mem_nhds
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (k p : ℕ) (hk : 0 < k) (hp : Odd p) (c s Y : ℂ)
    (hc : c ≠ 0) (hs : s ≠ 0) (hY : 2 * s ^ p = c * (Y ^ k - 1))
    (F A B : MvPolynomial (Fin 2) ℂ)
    (hdecomp : F = cyclicInvariantBaseHom p c A + X 0 * cyclicInvariantBaseHom p c B)
    (hF : cyclicOddRestriction p c B ≠ 0)
    (hroot : (cyclicOddRestriction p c B).IsRoot s)
    (hPhi : AnalyticAt ℂ Phi (0, ![s, -s, Y]))
    (hspecial : ∀ q, Phi (0, q) = weightedInitialDifference
      (cyclicResidualInitialMap k p c (cyclicInvariantLift k F)) q)
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![s, -s, Y])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ, (tau, q) ∈ U ∧ Phi (tau, q) = 0 := by
  obtain ⟨x, hx, hxs, hcurve, m, unit, hm, hunit, hunitZero, hfactor⟩ :=
    exists_cyclicOpposite_branch_finite_order k p hk hp.pos c s Y hc hs hY _ hF hroot
  let parameter : ℂ → ℂ := fun u ↦ Y + u
  let v : ℂ → Fin 2 → ℂ := fun u ↦ ![x u, -x u]
  let rotated : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ :=
    fun q ↦ Phi (q.1, cyclicOppositeRotate q.2)
  let third : ℂ × (Fin 2 → ℂ) → ℂ := fun q ↦
    eval ![q.2 0, 1] (cyclicInvariantLift k F) -
      eval ![q.2 1, Y + q.1] (cyclicInvariantLift k F)
  have hparameter : AnalyticAt ℂ parameter 0 := analyticAt_const.add analyticAt_id
  have hv : AnalyticAt ℂ v 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact hx
    · exact hx.neg
  have hrotated : AnalyticAt ℂ rotated (0, ![Y, s, -s]) := by
    exact hPhi.comp_of_eq (analyticAt_cyclicOppositeRotate_parameter _) (by
      simp [cyclicOppositeRotate])
  let V : Set (ℂ × (Fin 3 → ℂ)) :=
    (fun q : ℂ × (Fin 3 → ℂ) ↦ (q.1, cyclicOppositeRotate q.2)) ⁻¹' U
  have hV : V ∈ nhds (0, ![Y, s, -s]) := by
    have ht := (analyticAt_cyclicOppositeRotate_parameter (0, ![Y, s, -s])).continuousAt.tendsto
    exact ht.eventually hU
  have hpersist := eventually_exists_collisionZero_mem_nhds_of_explicit_branch
    rotated parameter v ![s, -s] hparameter hv (by simp [v, hxs])
    (by simpa [hCollisionAffinePoint, parameter] using hrotated)
    (cyclicOppositePlane k p c Y) ?_ (cyclicOppositeDerivative p s)
    (cyclicOpposite_pointDerivative k p hp c s Y)
    (cyclicOpposite_derivative_invertible p hp.pos s hs) ?_ third ?_
    m unit hm hunit hunitZero ?_ V
    (by simpa [hCollisionAffinePoint, parameter] using hV)
  · filter_upwards [hpersist] with tau htau
    obtain ⟨q, hq, hzero⟩ := htau
    exact ⟨cyclicOppositeRotate q, hq, hzero⟩
  · intro u point
    simp [hCollisionPlanePart, hCollisionReparametrization, hCollisionAffinePoint,
      rotated, cyclicOppositeRotate, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint,
      cyclicOppositePlane, parameter]
  · exact Filter.Eventually.of_forall fun u ↦ by
      ext i
      fin_cases i
      · simp [cyclicOppositePlane, v]
      · change x u ^ p + c - ((-x u) ^ p + c * (Y + u) ^ k) = 0
        rw [hp.neg_pow]
        linear_combination hcurve u
  · intro u point
    simp [hCollisionThirdPart, hCollisionReparametrization, hCollisionAffinePoint,
      rotated, cyclicOppositeRotate, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint,
      third, parameter]
  · filter_upwards [hfactor] with u hu
    change eval ![x u, 1] (cyclicInvariantLift k F) -
      eval ![-x u, Y + u] (cyclicInvariantLift k F) = _
    rw [cyclicInvariantLift_opposite_difference k p hp c hc F A B hdecomp
      (x u) (Y + u) (hcurve u)]
    exact hu

end OnLeConjecture.DTwo
