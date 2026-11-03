/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicPreparationDichotomy
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Exclusion of a pure noninvariant monomial residual

An opposite-sign collision persists under all strictly higher weighted
analytic terms. The original exponent is retained, without reduction
modulo the cyclic order.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

/-- A root of the monomial collision equation can be chosen off `Yᵏ = 1`.
No coprimality assumption on the original exponent is needed. -/
theorem exists_cyclicPureMonomial_root (k i j : ℕ) (hk : 0 < k) (hj : 0 < j) :
    ∃ Y : ℂ, Y ≠ 0 ∧ Y ^ (k + j) = (-1 : ℂ) ^ i ∧ Y ^ k ≠ 1 := by
  have hN : 0 < k + j := by omega
  rcases Nat.even_or_odd i with hi | hi
  · let Y : ℂ := Complex.exp (2 * Real.pi * Complex.I / (↑(k + j) : ℂ))
    have hprimitive : IsPrimitiveRoot Y (k + j) :=
      Complex.isPrimitiveRoot_exp _ hN.ne'
    refine ⟨Y, ?_, ?_, ?_⟩
    · intro hzero
      have := hprimitive.pow_eq_one
      rw [hzero, zero_pow hN.ne'] at this
      exact zero_ne_one this
    · rw [hi.neg_one_pow]
      exact hprimitive.pow_eq_one
    · intro hone
      have hdvd := (hprimitive.pow_eq_one_iff_dvd k).mp hone
      have := Nat.le_of_dvd hk hdvd
      omega
  · let Y : ℂ := Complex.exp (2 * Real.pi * Complex.I / (↑(2 * (k + j)) : ℂ))
    have hprimitive : IsPrimitiveRoot Y (2 * (k + j)) :=
      Complex.isPrimitiveRoot_exp _ (Nat.mul_ne_zero (by decide) hN.ne')
    have hhalf : Y ^ (k + j) ≠ 1 := by
      intro hone
      have hdvd := (hprimitive.pow_eq_one_iff_dvd (k + j)).mp hone
      have := Nat.le_of_dvd hN hdvd
      omega
    refine ⟨Y, ?_, ?_, ?_⟩
    · intro hzero
      have := hprimitive.pow_eq_one
      rw [hzero, zero_pow (Nat.mul_ne_zero (by decide) hN.ne')] at this
      exact zero_ne_one this
    · rw [hi.neg_one_pow]
      apply (sq_eq_one_iff.mp ?_).resolve_left hhalf
      rw [← pow_mul, Nat.mul_comm]
      exact hprimitive.pow_eq_one
    · intro hone
      have hdvd := (hprimitive.pow_eq_one_iff_dvd k).mp hone
      have := Nat.le_of_dvd hk hdvd
      omega

set_option maxRecDepth 2048 in
/-- On the opposite-sign plane branch, the pure monomial difference has
finite positive order in the second `y` coordinate. -/
theorem exists_cyclicPureMonomial_branch_finite_order
    (k p i j : ℕ) (hp : 0 < p) (hN : 0 < k + j)
    (c s Y γ : ℂ) (hs : s ≠ 0) (hγ : γ ≠ 0)
    (hY : 2 * s ^ p = c * (Y ^ k - 1))
    (hroot : Y ^ (k + j) = (-1 : ℂ) ^ i) :
    ∃ x : ℂ → ℂ, AnalyticAt ℂ x 0 ∧ x 0 = s ∧
      (∀ u, 2 * x u ^ p = c * ((Y + u) ^ k - 1)) ∧
      ∃ m : ℕ, ∃ unit : ℂ → ℂ, 0 < m ∧ AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
        ∀ᶠ u in nhds 0,
          γ * x u ^ i - γ * (-x u) ^ i * (Y + u) ^ (k + j) = u ^ m * unit u := by
  let power : ℂ → ℂ := fun u ↦ c / 2 * ((Y + u) ^ k - 1)
  have hpower : AnalyticAt ℂ power 0 :=
    analyticAt_const.mul (((analyticAt_const.add analyticAt_id).pow k).sub analyticAt_const)
  have hpowerValue : power 0 = s ^ p := by
    dsimp [power]
    simp only [add_zero]
    linear_combination -(1 / 2 : ℂ) * hY
  obtain ⟨x, hx, hxs, hxpower⟩ := exists_analyticAt_root_with_value
    power hpower (by rw [hpowerValue]; exact pow_ne_zero p hs) p hp.ne' s hpowerValue.symm
  have hcurve (u : ℂ) : 2 * x u ^ p = c * ((Y + u) ^ k - 1) := by
    rw [hxpower]
    dsimp [power]
    ring
  let Q : _root_.Polynomial ℂ :=
    1 - _root_.Polynomial.C ((-1 : ℂ) ^ i) * _root_.Polynomial.X ^ (k + j)
  have hQ : Q ≠ 0 := by
    intro heq
    have hcoeff := congrArg (fun P : _root_.Polynomial ℂ ↦ P.coeff 0) heq
    simp [Q, hN.ne] at hcoeff
  have hQroot : Q.IsRoot Y := by
    change Q.eval Y = 0
    simp only [Q, _root_.Polynomial.eval_sub, _root_.Polynomial.eval_one,
      _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C,
      _root_.Polynomial.eval_pow, _root_.Polynomial.eval_X, hroot]
    rw [← mul_pow]
    norm_num
  obtain ⟨hm, quotient, hfactor, hquotient⟩ := exists_polynomial_local_factorization hQ hQroot
  let unit : ℂ → ℂ := fun u ↦ γ * x u ^ i * quotient.eval (Y + u)
  have htranslation : AnalyticAt ℂ (fun u : ℂ ↦ Y + u) 0 :=
    analyticAt_const.add analyticAt_id
  have hquotientAnalytic : AnalyticAt ℂ (fun u : ℂ ↦ quotient.eval (Y + u)) 0 := by
    simpa [_root_.Polynomial.aeval_def] using htranslation.aeval_polynomial quotient
  refine ⟨x, hx, hxs, hcurve, Q.rootMultiplicity Y, unit, hm,
    (analyticAt_const.mul (hx.pow i)).mul hquotientAnalytic, ?_, ?_⟩
  · simpa [unit, hxs] using mul_ne_zero (mul_ne_zero hγ (pow_ne_zero i hs)) hquotient
  · exact Filter.Eventually.of_forall fun u ↦ by
      have heval := congrArg (fun P : _root_.Polynomial ℂ ↦ P.eval (Y + u)) hfactor
      simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_pow,
        _root_.Polynomial.eval_sub, _root_.Polynomial.eval_X,
        _root_.Polynomial.eval_C, add_sub_cancel_left] at heval
      have hscalar : γ * x u ^ i - γ * (-x u) ^ i * (Y + u) ^ (k + j) =
          γ * x u ^ i * Q.eval (Y + u) := by
        simp only [Q, _root_.Polynomial.eval_sub, _root_.Polynomial.eval_one,
          _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C,
          _root_.Polynomial.eval_pow, _root_.Polynomial.eval_X]
        rw [neg_pow]
        ring
      rw [hscalar, heval]
      dsimp [unit]
      ring

/-- Full analytic perturbations have zeros near the selected pure monomial
collision, not only zeros of their initial polynomial equations. -/
theorem eventually_exists_cyclicPureMonomialZero_mem_nhds
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (k p i j : ℕ) (hp : Odd p) (hN : 0 < k + j)
    (c s Y γ : ℂ) (hs : s ≠ 0) (hγ : γ ≠ 0)
    (hY : 2 * s ^ p = c * (Y ^ k - 1))
    (hroot : Y ^ (k + j) = (-1 : ℂ) ^ i)
    (hPhi : AnalyticAt ℂ Phi (0, ![s, -s, Y]))
    (hspecial : ∀ q, Phi (0, q) = weightedInitialDifference
      (cyclicResidualInitialMap k p c (C γ * X 0 ^ i * X 1 ^ (k + j))) q)
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![s, -s, Y])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ, (tau, q) ∈ U ∧ Phi (tau, q) = 0 := by
  obtain ⟨x, hx, hxs, hcurve, m, unit, hm, hunit, hunitZero, hfactor⟩ :=
    exists_cyclicPureMonomial_branch_finite_order k p i j hp.pos hN
      c s Y γ hs hγ hY hroot
  let parameter : ℂ → ℂ := fun u ↦ Y + u
  let v : ℂ → Fin 2 → ℂ := fun u ↦ ![x u, -x u]
  let rotate : ℂ × (Fin 3 → ℂ) → ℂ × (Fin 3 → ℂ) :=
    fun q ↦ (q.1, cyclicOppositeRotate q.2)
  let rotated : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ := fun q ↦ Phi (rotate q)
  let third : ℂ × (Fin 2 → ℂ) → ℂ := fun q ↦
    γ * q.2 0 ^ i - γ * q.2 1 ^ i * (Y + q.1) ^ (k + j)
  have hparameter : AnalyticAt ℂ parameter 0 := analyticAt_const.add analyticAt_id
  have hv : AnalyticAt ℂ v 0 := by
    apply AnalyticAt.pi
    intro index
    fin_cases index
    · exact hx
    · exact hx.neg
  have hrotateAt (q : ℂ × (Fin 3 → ℂ)) : AnalyticAt ℂ rotate q :=
    analyticAt_fst.prod ((analyticAt_cyclicOppositeRotate q.2).fun_comp analyticAt_snd)
  have hrotate := hrotateAt (0, ![Y, s, -s])
  have hrotated : AnalyticAt ℂ rotated (0, ![Y, s, -s]) :=
    hPhi.comp_of_eq hrotate (by simp [rotate, cyclicOppositeRotate])
  let V : Set (ℂ × (Fin 3 → ℂ)) := rotate ⁻¹' U
  have hV : V ∈ nhds (0, ![Y, s, -s]) := hrotate.continuousAt.tendsto.eventually hU
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
      rotated, rotate, cyclicOppositeRotate, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint,
      cyclicOppositePlane, parameter]
  · exact Filter.Eventually.of_forall fun u ↦ by
      ext index
      fin_cases index
      · simp [cyclicOppositePlane, v]
      · change x u ^ p + c - ((-x u) ^ p + c * (Y + u) ^ k) = 0
        rw [hp.neg_pow]
        linear_combination hcurve u
  · intro u point
    simp [hCollisionThirdPart, hCollisionReparametrization, hCollisionAffinePoint,
      rotated, rotate, cyclicOppositeRotate, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint,
      third, parameter]
  · simpa only [third, v, Matrix.cons_val_zero, Matrix.cons_val_one] using hfactor

/-- Strictly higher weighted analytic terms do not restore injectivity to
a pure monomial cyclic residual with positive original second exponent. -/
theorem cyclicPureMonomial_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k p i j D : ℕ)
    (hk : 0 < k) (hp : Odd p) (hj : 0 < j) (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (hR : IsWeightedHomogeneous ![k, p] (C γ * X 0 ^ i * X 1 ^ (k + j)) D)
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c (C γ * X 0 ^ i * X 1 ^ (k + j)) index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨Y, _, hroot, hYnot⟩ := exists_cyclicPureMonomial_root k i j hk hj
  obtain ⟨s, hsp⟩ := IsAlgClosed.exists_pow_nat_eq (c / 2 * (Y ^ k - 1)) hp.pos
  have hs : s ≠ 0 := by
    intro hzero
    have hnonzero : c / 2 * (Y ^ k - 1) ≠ 0 :=
      mul_ne_zero (div_ne_zero hc (by norm_num)) (sub_ne_zero.mpr hYnot)
    exact hnonzero (by simpa [hzero, hp.pos.ne'] using hsp.symm)
  have hY : 2 * s ^ p = c * (Y ^ k - 1) := by rw [hsp]; ring
  have hYone : Y ≠ 1 := by intro heq; exact hYnot (by simp [heq])
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      k p hk hp.pos ![2 * k, p * k, D]
      (cyclicResidualPolynomialMap k p c (C γ * X 0 ^ i * X 1 ^ (k + j)))
      (cyclicResidualPolynomialMap_homogeneous k p D c _ hR)
      representative hanalytic (fun index ↦ by rw [hcomponents index]; exact htail index)
  simp only [weightedPolynomialMap_cyclicResidualPolynomialMap] at hexpansion
  rw [heq]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightChartZeros
    k p ![2 * k, p * k, D]
    (cyclicResidualInitialMap k p c (C γ * X 0 ^ i * X 1 ^ (k + j)))
    representative remainder s (-s) Y hk hp.pos hYone
    (hexpansion (s, 1)) (hexpansion (-s, Y))
  intro U hU
  apply eventually_exists_cyclicPureMonomialZero_mem_nhds
    (weightedRescaledPerturbation
      (cyclicResidualInitialMap k p c (C γ * X 0 ^ i * X 1 ^ (k + j))) remainder)
    k p i j hp (by omega) c s Y γ hs hγ hY hroot ?_ ?_ U hU
  · apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_cyclicResidualInitialDifference k p c _ _
    · exact (hexpansion (s, 1)).remainder_analyticAt
    · exact (hexpansion (-s, Y)).remainder_analyticAt
  · intro q
    exact weightedRescaledPerturbation_zero _ _ q

/-- The invariant summand of a Fourier residual of an injective analytic
triple cannot vanish. The strict tails concern the original analytic germ. -/
theorem cyclicResidual_invariant_part_ne_zero
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p i j D : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (R Λinv : MvPolynomial (Fin 2) ℂ)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (Λinv + C γ * X 0 ^ i * X 1 ^ j))
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) :
    Λinv ≠ 0 := by
  intro hzero
  have hjpos : 0 < j := by
    by_contra h
    have : j = 0 := by omega
    exact hj (this ▸ dvd_zero k)
  have heq : R = C γ * X 0 ^ i * X 1 ^ (k + j) := by
    rw [hfactor, hzero, zero_add, pow_add]
    ring
  rw [heq] at hR htail
  exact cyclicPureMonomial_not_hasInjectiveRepresentative
    g k p i j D hk hp hjpos c γ hc hγ hR htail hg

/-- The remaining residual has both a nonzero invariant part and its
single noninvariant monomial, together with the analytic elimination data. -/
@[expose] def CyclicMixedResidual (g : PointedMapGerm 2 3) (k p : ℕ) (c : ℂ) : Prop :=
  ∃ g' : PointedMapGerm 2 3, ∃ D : ℕ, ∃ h : Germ 2,
    ∃ R Λ Λinv : MvPolynomial (Fin 2) ℂ, ∃ i j : ℕ, ∃ γ : ℂ,
      g.RightLeftEquivalent g' ∧ g'.HasInjectiveRepresentative ∧
      g'.1.component 0 = g.1.component 0 ∧ g'.1.component 1 = g.1.component 1 ∧
      h ∈ Germ.maximalIdeal 2 ∧ h ≠ 0 ∧
      g'.1.component 2 = Germ.coordinate 1 ^ k * h ∧
      p * k < D ∧ R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      Germ.coordinate 1 ^ k * h ∈ Germ.twoWeightOrderIdeal k p D ∧
      Germ.coordinate 1 ^ k * h - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      R ∉ Set.range (aeval (cyclicInitialPair k p c) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) ∧
      Λ ≠ 0 ∧ Λ.IsWeightedHomogeneous ![k, p] (D - p * k) ∧ R = X 1 ^ k * Λ ∧
      Λinv ∈ cyclicInvariantAlgebra k ∧ Λinv.IsWeightedHomogeneous ![k, p] (D - p * k) ∧
      γ ≠ 0 ∧ ¬ k ∣ j ∧ k * i + p * j = D - p * k ∧
      Λ = Λinv + C γ * X 0 ^ i * X 1 ^ j ∧ Λinv ≠ 0

/-- The analytic data retained in `CyclicNoninvariantResidual` exclude its
pure monomial subcase for the prepared pair. -/
theorem cyclic_noninvariant_residual_is_mixed
    (g : PointedMapGerm 2 3) (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (hresidual : CyclicNoninvariantResidual g k p (Germ.valueRingHom 2 β)) :
    CyclicMixedResidual g k p (Germ.valueRingHom 2 β) := by
  obtain ⟨g', D, h, R, Λ, Λinv, i, j, γ, hequiv, hg', hzero, hone,
    hh, hhzero, hthird, hD, hRzero, hR, horder, htail, hbase, hΛzero, hΛ, hfactor,
    hinv, hinvHom, hγ, hj, hdegree, hΛeq⟩ := hresidual
  have hpairtail := cyclic_pair_strict_tails g'.firstTwo k p hk hp β
    (by simpa using hzero.trans hP) (by simpa using hone.trans hQ)
  have htriple : ∀ index, g'.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p (Germ.valueRingHom 2 β) R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1) := by
    intro index
    fin_cases index
    · simpa [cyclicResidualPolynomialMap] using hpairtail 0
    · simpa [cyclicResidualPolynomialMap] using hpairtail 1
    · change g'.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1)
      rw [hthird]
      exact htail
  have hnonzero := cyclicResidual_invariant_part_ne_zero g' hg' k p i j D hk hodd hj
    (Germ.valueRingHom 2 β) γ hβ hγ R Λinv hR (hfactor.trans (by rw [hΛeq])) htriple
  exact ⟨g', D, h, R, Λ, Λinv, i, j, γ, hequiv, hg', hzero, hone,
    hh, hhzero, hthird, hD, hRzero, hR, horder, htail, hbase, hΛzero, hΛ, hfactor,
    hinv, hinvHom, hγ, hj, hdegree, hΛeq, hnonzero⟩

/-- From the original prepared analytic germ, either pure odd preparation
holds or the residual has a nonzero invariant part. -/
theorem cyclic_preparation_pure_odd_or_mixed
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (h : Germ 2) (hh : h ∈ Germ.maximalIdeal 2)
    (hH : g.1.component 2 = Germ.coordinate 1 ^ k * h) :
    CyclicPureOddPreparation g k p ∨ CyclicMixedResidual g k p (Germ.valueRingHom 2 β) := by
  rcases cyclic_preparation_dichotomy g hg k p hk hp hodd β hβ hP hQ h hh hH with
    hpure | hresidual
  · exact Or.inl hpure
  · exact Or.inr (cyclic_noninvariant_residual_is_mixed g k p hk hp hodd β hβ hP hQ hresidual)

end OnLeConjecture.DTwo
