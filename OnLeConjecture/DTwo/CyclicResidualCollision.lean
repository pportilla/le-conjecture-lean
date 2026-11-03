/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicResidualFourier
public import OnLeConjecture.Analytic.ExplicitBranchCollisionPersistence
public import OnLeConjecture.Analytic.TwoWeightRadialExpansion
public import OnLeConjecture.Analytic.TwoWeightRotationNoninjectivity
public import OnLeConjecture.DThree.EInvariantRegularPersistence
public import OnLeConjecture.DTwo.PreparedCyclicPair
public import OnLeConjecture.DThree.PairRepresentativeComponents

/-!
# Collisions from a nonzero root of the cyclic residual difference

The two plane equations are transverse at `(s,1),(s,ζ)` when `s ≠ 0`.
Analytic elimination and persistence of a zero of finite multiplicity apply
without a simplicity assumption on the residual root.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree

@[expose] noncomputable def cyclicResidualInitialMap
    (k p : ℕ) (c : ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (z : ℂ × ℂ) : Fin 3 → ℂ :=
  ![z.1 ^ 2, z.1 ^ p + c * z.2 ^ k, MvPolynomial.eval ![z.1, z.2] R]

@[expose] noncomputable def cyclicResidualPlane
    (k p : ℕ) (c s : ℂ) (q : ℂ × (Fin 2 → ℂ)) : Fin 2 → ℂ :=
  ![(s + q.1) ^ 2 - q.2 0 ^ 2,
    (s + q.1) ^ p + c - (q.2 0 ^ p + c * q.2 1 ^ k)]

@[expose] noncomputable def cyclicResidualDerivative (k p : ℕ) (c s ζ : ℂ) :
    (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLin' !![-2 * s, 0;
    -(p : ℂ) * s ^ (p - 1), -c * (k : ℂ) * ζ ^ (k - 1)]).toContinuousLinearMap

theorem cyclicResidual_pointDerivative (k p : ℕ) (c s ζ : ℂ) :
    HasStrictFDerivAt (fun v ↦ cyclicResidualPlane k p c s (0, v))
      (cyclicResidualDerivative k p c s ζ) ![s, ζ] := by
  rw [hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  · convert (hasStrictFDerivAt_const (𝕜 := ℂ) (s ^ 2) ![s, ζ]).sub
      ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, ζ]).pow 2) using 1
    all_goals ext v
    all_goals simp [cyclicResidualPlane, cyclicResidualDerivative,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
  · convert (hasStrictFDerivAt_const (𝕜 := ℂ) (s ^ p + c) ![s, ζ]).sub
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![s, ζ]).pow p).add
        (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![s, ζ]).pow k).const_mul c))
      using 1
    all_goals ext v
    all_goals simp [cyclicResidualPlane, cyclicResidualDerivative,
      Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring

theorem cyclicResidual_derivative_invertible (k p : ℕ) (hk : 0 < k)
    (c s ζ : ℂ) (hc : c ≠ 0) (hs : s ≠ 0) (hζ : ζ ≠ 0) :
    (cyclicResidualDerivative k p c s ζ).IsInvertible := by
  have hdet : (cyclicResidualDerivative k p c s ζ).det ≠ 0 := by
    have heq : (cyclicResidualDerivative k p c s ζ).det =
        2 * s * c * (k : ℂ) * ζ ^ (k - 1) := by
      simp [cyclicResidualDerivative, LinearMap.det_toContinuousLinearMap,
        LinearMap.det_toLin', Matrix.det_fin_two]
      ring
    rw [heq]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs) hc)
        (Nat.cast_ne_zero.mpr hk.ne')) (pow_ne_zero _ hζ)
  exact ⟨(cyclicResidualDerivative k p c s ζ).toContinuousLinearEquivOfDetNeZero hdet,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

theorem cyclicRotationDifference_eval (R : MvPolynomial (Fin 2) ℂ) (ζ s : ℂ) :
    (cyclicRotationDifference R ζ).eval s =
      MvPolynomial.eval ![s, 1] R - MvPolynomial.eval ![s, ζ] R := by
  have heval (t : ℂ) :
      (MvPolynomial.aeval ![Polynomial.X, Polynomial.C t] R).eval s =
        MvPolynomial.eval ![s, t] R := by
    have heq : (Polynomial.evalRingHom s).comp
        (MvPolynomial.aeval ![Polynomial.X, Polynomial.C t]).toRingHom =
        MvPolynomial.eval ![s, t] := by
      apply MvPolynomial.ringHom_ext
      · intro z
        simp
      · intro i
        fin_cases i <;> simp
    exact congrArg (fun f : MvPolynomial (Fin 2) ℂ →+* ℂ ↦ f R) heq
  rw [cyclicRotationDifference, Polynomial.eval_sub, heval ζ]
  congr 1
  simpa only [Polynomial.C_1] using heval 1

theorem eventually_exists_cyclicResidualZero_mem_nhds
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (k p : ℕ) (hk : 0 < k) (c s ζ : ℂ)
    (hc : c ≠ 0) (hs : s ≠ 0) (hζpow : ζ ^ k = 1)
    (R : MvPolynomial (Fin 2) ℂ)
    (hPhi : AnalyticAt ℂ Phi (0, ![s, s, ζ]))
    (hspecial : ∀ q, Phi (0, q) = weightedInitialDifference
      (cyclicResidualInitialMap k p c R) q)
    (hD : cyclicRotationDifference R ζ ≠ 0)
    (hroot : (cyclicRotationDifference R ζ).IsRoot s)
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![s, s, ζ])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ, (tau, point) ∈ U ∧ Phi (tau, point) = 0 := by
  let x : ℂ → ℂ := fun lambda ↦ s + lambda
  let v : ℂ → Fin 2 → ℂ := fun lambda ↦ ![s + lambda, ζ]
  let third : ℂ × (Fin 2 → ℂ) → ℂ := fun q ↦
    MvPolynomial.eval ![s + q.1, 1] R - MvPolynomial.eval ![q.2 0, q.2 1] R
  have hx : AnalyticAt ℂ x 0 := analyticAt_const.add analyticAt_id
  have hv : AnalyticAt ℂ v 0 := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact hx
    · exact analyticAt_const
  have hζ : ζ ≠ 0 := by
    intro hz
    simp [hz, hk.ne'] at hζpow
  obtain ⟨hm, quotient, hfactor, hquotient⟩ := exists_polynomial_local_factorization hD hroot
  let u : ℂ → ℂ := fun lambda ↦ quotient.eval (s + lambda)
  have hu : AnalyticAt ℂ u 0 := by
    simpa [u, x, Polynomial.aeval_def] using hx.aeval_polynomial quotient
  have hu0 : u 0 ≠ 0 := by simpa [u] using hquotient
  apply eventually_exists_collisionZero_mem_nhds_of_explicit_branch
    Phi x v ![s, ζ] hx hv (by simp [v]) (by simpa [hCollisionAffinePoint, x] using hPhi)
    (cyclicResidualPlane k p c s) ?_ (cyclicResidualDerivative k p c s ζ)
    (cyclicResidual_pointDerivative k p c s ζ)
    (cyclicResidual_derivative_invertible k p hk c s ζ hc hs hζ) ?_
    third ?_ ((cyclicRotationDifference R ζ).rootMultiplicity s) u hm hu hu0 ?_
    U (by simpa [hCollisionAffinePoint, x] using hU)
  · intro lambda point
    simp [hCollisionPlanePart, hCollisionReparametrization, hCollisionAffinePoint,
      hspecial, weightedInitialDifference, cyclicResidualInitialMap,
      residueFirstChartPoint, residueSecondChartPoint, cyclicResidualPlane, x]
  · exact Filter.Eventually.of_forall fun lambda ↦ by
      ext i
      fin_cases i <;> simp [cyclicResidualPlane, v, hζpow]
  · intro lambda point
    simp [hCollisionThirdPart, hCollisionReparametrization, hCollisionAffinePoint,
      hspecial, weightedInitialDifference, cyclicResidualInitialMap,
      residueFirstChartPoint, residueSecondChartPoint, third, x]
  · exact Filter.Eventually.of_forall fun lambda ↦ by
      change MvPolynomial.eval ![s + lambda, 1] R -
        MvPolynomial.eval ![s + lambda, ζ] R = _
      rw [← cyclicRotationDifference_eval, polynomial_eval_add_factorization hfactor]

/-- Analyticity of the initial polynomial map at every affine point. -/
theorem analyticAt_cyclicResidualInitialMap
    (k p : ℕ) (c : ℂ) (R : MvPolynomial (Fin 2) ℂ) (z : ℂ × ℂ) :
    AnalyticAt ℂ (cyclicResidualInitialMap k p c R) z := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_fst.pow 2
  · exact (analyticAt_fst.pow p).add (analyticAt_const.mul (analyticAt_snd.pow k))
  · have hcoords : AnalyticAt ℂ (fun z : ℂ × ℂ ↦ (![z.1, z.2] : Fin 2 → ℂ)) z := by
      apply AnalyticAt.pi
      intro j
      fin_cases j
      · exact analyticAt_fst
      · exact analyticAt_snd
    exact ((AnalyticOnNhd.eval_mvPolynomial R) _ (Set.mem_univ _)).fun_comp hcoords

theorem analyticAt_cyclicResidualInitialDifference
    (k p : ℕ) (c : ℂ) (R : MvPolynomial (Fin 2) ℂ) (q : Fin 3 → ℂ) :
    AnalyticAt ℂ (weightedInitialDifference (cyclicResidualInitialMap k p c R)) q :=
  ((analyticAt_cyclicResidualInitialMap k p c R _).fun_comp
    (analyticAt_residueFirstChartPoint q)).sub
      ((analyticAt_cyclicResidualInitialMap k p c R _).fun_comp
        (analyticAt_residueSecondChartPoint q))

/-- The polynomial triple used for two weight radial expansion. -/
@[expose] noncomputable def cyclicResidualPolynomialMap
    (k p : ℕ) (c : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    Fin 3 → MvPolynomial (Fin 2) ℂ :=
  ![cyclicInitialPair k p c 0, cyclicInitialPair k p c 1, R]

theorem cyclicResidualPolynomialMap_homogeneous
    (k p D : ℕ) (c : ℂ) (R : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous ![k, p] D) (i : Fin 3) :
    (cyclicResidualPolynomialMap k p c R i).IsWeightedHomogeneous
      ![k, p] (![2 * k, p * k, D] i) := by
  fin_cases i
  · exact cyclicInitialPair_homogeneous k p c 0
  · exact cyclicInitialPair_homogeneous k p c 1
  · exact hR

theorem weightedPolynomialMap_cyclicResidualPolynomialMap
    (k p : ℕ) (c : ℂ) (R : MvPolynomial (Fin 2) ℂ) :
    weightedPolynomialMap (cyclicResidualPolynomialMap k p c R) =
      cyclicResidualInitialMap k p c R := by
  funext z i
  fin_cases i <;> simp [weightedPolynomialMap, cyclicResidualPolynomialMap,
    cyclicInitialPair, cyclicResidualInitialMap]

/-- A nonzero residual difference with a nonzero root prevents local
injectivity of an analytic representative with these polynomial initial forms.
The multiplicity of the root is unrestricted. -/
theorem cyclicResidualTails_not_hasInjectiveRepresentative
    (k p D : ℕ) (hk : 0 < k) (hp : 0 < p) (c s ζ : ℂ)
    (hc : c ≠ 0) (hs : s ≠ 0) (hζpow : ζ ^ k = 1) (hζone : ζ ≠ 1)
    (R : MvPolynomial (Fin 2) ℂ) (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hD : cyclicRotationDifference R ζ ≠ 0)
    (hroot : (cyclicRotationDifference R ζ).IsRoot s)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0) (hzero : representative 0 = 0)
    (htail : ∀ i, pairRepresentativeComponentGerm representative hanalytic i -
      Germ.coordinatePolynomialAlgHom 2 (cyclicResidualPolynomialMap k p c R i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      k p hk hp ![2 * k, p * k, D] (cyclicResidualPolynomialMap k p c R)
      (cyclicResidualPolynomialMap_homogeneous k p D c R hR)
      representative hanalytic htail
  simp only [weightedPolynomialMap_cyclicResidualPolynomialMap] at hexpansion
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightRotationZeros
    k p ![2 * k, p * k, D] (cyclicResidualInitialMap k p c R)
    representative remainder s ζ hk hp hζone (hexpansion (s, 1)) (hexpansion (s, ζ))
  intro U hU
  apply eventually_exists_cyclicResidualZero_mem_nhds
    (weightedRescaledPerturbation (cyclicResidualInitialMap k p c R) remainder)
    k p hk c s ζ hc hs hζpow R ?_ ?_ hD hroot U hU
  · apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_cyclicResidualInitialDifference k p c R _
    · exact (hexpansion (s, 1)).remainder_analyticAt
    · exact (hexpansion (s, ζ)).remainder_analyticAt
  · intro q
    exact weightedRescaledPerturbation_zero _ _ q

/-- Injectivity excludes every nonzero root of every nonzero cyclic
rotation difference. An identically zero difference is allowed. -/
theorem cyclicResidual_no_nonzero_roots_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p D : ℕ) (hk : 0 < k) (hp : 0 < p) (c : ℂ) (hc : c ≠ 0)
    (R : MvPolynomial (Fin 2) ℂ) (hR : R.IsWeightedHomogeneous ![k, p] D)
    (htail : ∀ i, g.1.component i -
      Germ.coordinatePolynomialAlgHom 2 (cyclicResidualPolynomialMap k p c R i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1)) :
    ∀ ζ : ℂ, ζ ^ k = 1 → cyclicRotationDifference R ζ ≠ 0 →
      ∀ s : ℂ, (cyclicRotationDifference R ζ).eval s = 0 → s = 0 := by
  intro ζ hζ hD s hs
  by_contra hsne
  have hζone : ζ ≠ 1 := by
    intro hone
    apply hD
    simp [cyclicRotationDifference, hone]
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  apply cyclicResidualTails_not_hasInjectiveRepresentative
    k p D hk hp c s ζ hc hsne hζ hζone R hR hD hs
    representative hanalytic hzero
    (fun i ↦ by rw [hcomponents i]; exact htail i)
  rw [← heq]
  exact hg

/-- The residual initial form of an injective analytic triple is invariant,
or differs from an invariant form by one noninvariant monomial. -/
theorem cyclicResidual_fourier_dichotomy_of_injective
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p D : ℕ) (hk : 0 < k) (hp : 0 < p) (c : ℂ) (hc : c ≠ 0)
    (R : MvPolynomial (Fin 2) ℂ) (hR : R.IsWeightedHomogeneous ![k, p] D)
    (htail : ∀ i, g.1.component i -
      Germ.coordinatePolynomialAlgHom 2 (cyclicResidualPolynomialMap k p c R i) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] i + 1)) :
    R ∈ cyclicInvariantAlgebra k ∨
      ∃ Rinv : MvPolynomial (Fin 2) ℂ, ∃ i j : ℕ, ∃ γ : ℂ,
        Rinv ∈ cyclicInvariantAlgebra k ∧ Rinv.IsWeightedHomogeneous ![k, p] D ∧
        γ ≠ 0 ∧ ¬ k ∣ j ∧ k * i + p * j = D ∧
        R = Rinv + MvPolynomial.C γ * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j := by
  by_cases hinv : R ∈ cyclicInvariantAlgebra k
  · exact Or.inl hinv
  · exact Or.inr (cyclic_residual_fourier_classification_of_no_nonzero_roots
      k p k D hp hk R hR hinv
      (cyclicResidual_no_nonzero_roots_of_injective g hg k p D hk hp c hc R hR htail))

end OnLeConjecture.DTwo
