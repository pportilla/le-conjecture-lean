/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicResidualCollision
public import OnLeConjecture.DTwo.ExtremeMonomialCollision

/-!
# Rotation collisions in the extreme quadratic alternative

The plane Jacobian is nonzero at every point with second coordinate a
root of unity, including points with first coordinate zero. A nonzero
rotation difference with any complex root therefore produces an analytic
collision, without a simplicity assumption on that root.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open Analytic DThree

@[expose] noncomputable def extremeResidualPolynomialMap
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) : Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ (2 * a),
    2 * MvPolynomial.X 0 ^ 3 + 3 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ (2 * a), R]

@[expose] noncomputable def extremeResidualInitialMap
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 2 + z.2 ^ (2 * a),
    2 * z.1 ^ 3 + 3 * z.1 * z.2 ^ (2 * a), MvPolynomial.eval ![z.1, z.2] R]

theorem weightedPolynomialMap_extremeResidualPolynomialMap
    (a : ℕ) (R : MvPolynomial (Fin 2) ℂ) :
    weightedPolynomialMap (extremeResidualPolynomialMap a R) =
      extremeResidualInitialMap a R := by
  funext z i
  fin_cases i <;> simp [weightedPolynomialMap, extremeResidualPolynomialMap,
    extremeResidualInitialMap]

theorem extremeResidualPolynomialMap_homogeneous (a D : ℕ)
    (R : MvPolynomial (Fin 2) ℂ) (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (i : Fin 3) : (extremeResidualPolynomialMap a R i).IsWeightedHomogeneous
      ![a, 1] (![2 * a, 3 * a, D] i) := by
  fin_cases i
  · exact extremeMonomial_homogeneous a D 0 0
  · exact extremeMonomial_homogeneous a D 0 1
  · exact hR

@[expose] noncomputable def extremeResidualPlane (a : ℕ) (s : ℂ)
    (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![(s + q.1) ^ 2 + 1 - (q.2 0 ^ 2 + q.2 1 ^ (2 * a)),
    2 * (s + q.1) ^ 3 + 3 * (s + q.1) -
      (2 * q.2 0 ^ 3 + 3 * q.2 0 * q.2 1 ^ (2 * a))]

@[expose] noncomputable def extremeResidualDerivative (a : ℕ) (s ζ : ℂ) :
    (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' !![-2 * s, -(2 * a : ℕ) * ζ ^ (2 * a - 1);
    -(6 * s ^ 2 + 3 * ζ ^ (2 * a)),
      -3 * s * (2 * a : ℕ) * ζ ^ (2 * a - 1)]).toContinuousLinearMap

theorem extremeResidual_pointDerivative (a : ℕ) (s ζ : ℂ) :
    HasStrictFDerivAt (fun v => extremeResidualPlane a s (0, v))
      (extremeResidualDerivative a s ζ) ![s, ζ] := by
  have hd (i : Fin 2) := hasStrictFDerivAt_apply (𝕜 := ℂ) i ![s, ζ]
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  · convert (hasStrictFDerivAt_const (𝕜 := ℂ) (s ^ 2 + 1) ![s, ζ]).sub
      (((hd 0).pow 2).add ((hd 1).pow (2 * a))) using 1
    all_goals ext v
    all_goals simp [extremeResidualPlane, extremeResidualDerivative,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    <;> ring
  · convert (hasStrictFDerivAt_const (𝕜 := ℂ) (2 * s ^ 3 + 3 * s) ![s, ζ]).sub
      ((((hd 0).pow 3).const_mul 2).add
        (((hd 0).const_mul 3).mul ((hd 1).pow (2 * a)))) using 1
    all_goals ext v
    all_goals simp [extremeResidualPlane, extremeResidualDerivative,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    <;> ring

theorem extremeResidual_derivative_invertible (a : ℕ) (ha : 0 < a)
    (s ζ : ℂ) (hζpow : ζ ^ (2 * a) = 1) :
    (extremeResidualDerivative a s ζ).IsInvertible := by
  have hζ : ζ ≠ 0 := by intro hz; simp [hz, ha.ne'] at hζpow
  have heq : (extremeResidualDerivative a s ζ).det =
      -3 * (2 * a : ℕ) * ζ ^ (2 * a - 1) := by
    simp [extremeResidualDerivative, LinearMap.det_toContinuousLinearMap,
      LinearMap.det_toLin', Matrix.det_fin_two, hζpow]
    ring
  have hdet : (extremeResidualDerivative a s ζ).det ≠ 0 := by
    rw [heq]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Nat.cast_ne_zero.mpr (by omega))) (pow_ne_zero _ hζ)
  exact ⟨(extremeResidualDerivative a s ζ).toContinuousLinearEquivOfDetNeZero hdet,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

theorem eventually_exists_extremeResidualZero_mem_nhds
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (a : ℕ) (ha : 0 < a) (s ζ : ℂ) (hζpow : ζ ^ (2 * a) = 1)
    (R : MvPolynomial (Fin 2) ℂ)
    (hPhi : AnalyticAt ℂ Phi (0, ![s, s, ζ]))
    (hspecial : ∀ q, Phi (0, q) = weightedInitialDifference
      (extremeResidualInitialMap a R) q)
    (hD : cyclicRotationDifference R ζ ≠ 0)
    (hroot : (cyclicRotationDifference R ζ).IsRoot s)
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![s, s, ζ])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ, (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let x : ℂ → ℂ := fun lambda => s + lambda
  let v : ℂ → Fin 2 → ℂ := fun lambda => ![s + lambda, ζ]
  let third : ℂ × (Fin 2 → ℂ) → ℂ := fun q =>
    MvPolynomial.eval ![s + q.1, 1] R - MvPolynomial.eval ![q.2 0, q.2 1] R
  have hx : AnalyticAt ℂ x 0 := analyticAt_const.add analyticAt_id
  have hv : AnalyticAt ℂ v 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact hx
    · exact analyticAt_const
  obtain ⟨hm, quotient, hfactor, hquotient⟩ := exists_polynomial_local_factorization hD hroot
  let u : ℂ → ℂ := fun lambda => quotient.eval (s + lambda)
  have hu : AnalyticAt ℂ u 0 := by
    simpa [u, x, Polynomial.aeval_def] using hx.aeval_polynomial quotient
  have hu0 : u 0 ≠ 0 := by simpa [u] using hquotient
  apply eventually_exists_collisionZero_mem_nhds_of_explicit_branch
    Phi x v ![s, ζ] hx hv (by simp [v]) (by simpa [hCollisionAffinePoint, x] using hPhi)
    (extremeResidualPlane a s) ?_ (extremeResidualDerivative a s ζ)
    (extremeResidual_pointDerivative a s ζ)
    (extremeResidual_derivative_invertible a ha s ζ hζpow) ?_
    third ?_ ((cyclicRotationDifference R ζ).rootMultiplicity s) u hm hu hu0 ?_
    U (by simpa [hCollisionAffinePoint, x] using hU)
  · intro lambda point
    simp [hCollisionPlanePart, hCollisionReparametrization, hCollisionAffinePoint,
      hspecial, weightedInitialDifference, extremeResidualInitialMap,
      residueFirstChartPoint, residueSecondChartPoint, extremeResidualPlane, x]
  · exact Filter.Eventually.of_forall fun lambda => by
      ext i
      fin_cases i <;> simp [extremeResidualPlane, v, hζpow]
  · intro lambda point
    simp [hCollisionThirdPart, hCollisionReparametrization, hCollisionAffinePoint,
      hspecial, weightedInitialDifference, extremeResidualInitialMap,
      residueFirstChartPoint, residueSecondChartPoint, third, x]
  · exact Filter.Eventually.of_forall fun lambda => by
      change MvPolynomial.eval ![s + lambda, 1] R -
        MvPolynomial.eval ![s + lambda, ζ] R = _
      rw [← cyclicRotationDifference_eval, polynomial_eval_add_factorization hfactor]

theorem analyticAt_extremeResidualInitialMap (a : ℕ)
    (R : MvPolynomial (Fin 2) ℂ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (extremeResidualInitialMap a R) z := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (analyticAt_fst.pow 2).add (analyticAt_snd.pow (2 * a))
  · exact (analyticAt_const.mul (analyticAt_fst.pow 3)).add
      ((analyticAt_const.mul analyticAt_fst).mul (analyticAt_snd.pow (2 * a)))
  · have hcoords : AnalyticAt ℂ (fun z : ℂ × ℂ => (![z.1, z.2] : Fin 2 → ℂ)) z := by
      apply AnalyticAt.pi
      intro j
      fin_cases j
      · exact analyticAt_fst
      · exact analyticAt_snd
    exact ((AnalyticOnNhd.eval_mvPolynomial R) _ (Set.mem_univ _)).fun_comp hcoords

theorem analyticAt_extremeResidualInitialDifference (a : ℕ)
    (R : MvPolynomial (Fin 2) ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ (weightedInitialDifference (extremeResidualInitialMap a R)) q :=
  ((analyticAt_extremeResidualInitialMap a R _).fun_comp
    (analyticAt_residueFirstChartPoint q)).sub
      ((analyticAt_extremeResidualInitialMap a R _).fun_comp
        (analyticAt_residueSecondChartPoint q))

/-- Every root of a nonzero rotation difference gives collisions of the
analytic triple. This includes the root zero and roots of higher multiplicity. -/
theorem extremeResidual_no_roots_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (a D : ℕ) (ha : 0 < a) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous ![a, 1] D)
    (htail : ∀ i, g.1.component i -
      Germ.coordinatePolynomialAlgHom 2 (extremeResidualPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a (![2 * a, 3 * a, D] i + 1)) :
    ∀ ζ : ℂ, ζ ^ (2 * a) = 1 → cyclicRotationDifference R ζ ≠ 0 →
      ∀ s : ℂ, (cyclicRotationDifference R ζ).eval s ≠ 0 := by
  intro ζ hζ hD s hs
  have hζone : ζ ≠ 1 := by
    intro hone
    apply hD
    simp [cyclicRotationDifference, hone]
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  have htail' : ∀ i, pairRepresentativeComponentGerm representative hanalytic i -
      Germ.coordinatePolynomialAlgHom 2 (extremeResidualPolynomialMap a R i) ∈
        Germ.twoWeightOrderIdeal a 1 (![2 * a, 3 * a, D] i + 1) := by
    intro i
    rw [hcomponents i, ← Germ.weightedOrderIdeal_eq_twoWeightOrderIdeal a _ ha]
    exact htail i
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      a 1 ha one_pos ![2 * a, 3 * a, D] (extremeResidualPolynomialMap a R)
      (extremeResidualPolynomialMap_homogeneous a D R hR) representative hanalytic htail'
  simp only [weightedPolynomialMap_extremeResidualPolynomialMap] at hexpansion
  have hnon : ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
    apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
    apply not_neighborhood_injective_of_twoWeightRotationZeros
      a 1 ![2 * a, 3 * a, D] (extremeResidualInitialMap a R)
      representative remainder s ζ ha one_pos hζone (hexpansion (s, 1)) (hexpansion (s, ζ))
    intro U hU
    apply eventually_exists_extremeResidualZero_mem_nhds
      (weightedRescaledPerturbation (extremeResidualInitialMap a R) remainder)
      a ha s ζ hζ R ?_ ?_ hD hs U hU
    · apply analyticAt_weightedRescaledPerturbation
      · exact analyticAt_extremeResidualInitialDifference a R _
      · exact (hexpansion (s, 1)).remainder_analyticAt
      · exact (hexpansion (s, ζ)).remainder_analyticAt
    · intro q
      exact weightedRescaledPerturbation_zero _ _ q
  exact hnon (heq ▸ hg)

end OnLeConjecture.DTwo
