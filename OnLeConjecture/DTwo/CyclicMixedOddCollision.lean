/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicMixedPowerObstruction

/-!
# Mixed cyclic collisions of odd descended degree

For odd descended degree a root with `Yᵏ = Yʲ = -1` gives an explicit
opposite-sign collision. A polynomial multiplicity argument proves that
the collision is isolated and therefore persists under strict tails.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

/-- The degree identity constructs the two required negative powers
without reducing `j` or imposing coprimality conditions. -/
theorem exists_cyclicMixedOdd_root
    (k p j d : ℕ) (hk : 0 < k) (hp : Odd p) (hd : Odd d)
    (hdegree : p * j = k * d) :
    ∃ Y : ℂ, Y ^ k = -1 ∧ Y ^ j = -1 := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * k : ℕ))
  have hω : IsPrimitiveRoot ω (2 * k) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  have hhalf : ω ^ k ≠ 1 := by
    intro h
    have hdiv := (hω.pow_eq_one_iff_dvd k).mp h
    have hle := Nat.le_of_dvd hk hdiv
    omega
  have hnegative : ω ^ k = -1 := by
    apply (sq_eq_one_iff.mp ?_).resolve_left hhalf
    rw [← pow_mul, Nat.mul_comm k 2]
    exact hω.pow_eq_one
  refine ⟨ω ^ p, ?_, ?_⟩
  · rw [← pow_mul, Nat.mul_comm p k, pow_mul, hnegative, hp.neg_one_pow]
  · rw [← pow_mul, hdegree, pow_mul, hnegative, hd.neg_one_pow]

/-- Odd weighted degree makes the invariant terms cancel at the explicit
opposite-sign point. -/
theorem cyclicMixedOdd_initial_collision
    (k p j d : ℕ) (hp : Odd p) (hd : Odd d) (c γ s Y : ℂ)
    (hs : s ^ p = -c) (hY : Y ^ k = -1) (hYj : Y ^ j = -1)
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j)) :
    2 * s ^ p = c * (Y ^ k - 1) ∧ eval ![s, 1] R - eval ![-s, Y] R = 0 := by
  have hcoordinates : (fun index : Fin 2 ↦ (-1 : ℂ) ^ (![1, p] index) *
      (![s, 1] index)) = ![-s, -1] := by
    ext index
    fin_cases index <;> simp [hp.neg_one_pow]
  have hscale := OnLeConjecture.DThree.eval_weighted_smul_of_isWeightedHomogeneous
    hL (-1) ![s, 1]
  rw [hcoordinates, hd.neg_one_pow, neg_one_mul] at hscale
  constructor
  · rw [hs, hY]
    ring
  · rw [hR]
    simp [cyclicInvariantLift_eval, hY, hYj, hscale]
    ring

/-- The mixed difference has finite positive order at every off-axis
opposite-sign collision, irrespective of parity of its descended degree. -/
theorem exists_cyclicMixedZero_branch_finite_order
    (k p j d : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : p * j = k * d) (c γ s Y : ℂ)
    (hc : c ≠ 0) (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hcurve : 2 * s ^ p = c * (Y ^ k - 1))
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j))
    (hroot : eval ![s, 1] R - eval ![-s, Y] R = 0) :
    ∃ x : ℂ → ℂ, AnalyticAt ℂ x 0 ∧ x 0 = s ∧
      (∀ u, 2 * x u ^ p = c * ((Y + u) ^ k - 1)) ∧
      ∃ m : ℕ, ∃ unit : ℂ → ℂ, 0 < m ∧ AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
        ∀ᶠ u in nhds 0,
          eval ![x u, 1] R - eval ![-x u, Y + u] R = u ^ m * unit u := by
  let power : ℂ → ℂ := fun u ↦ c / 2 * ((Y + u) ^ k - 1)
  have hpower : AnalyticAt ℂ power 0 :=
    analyticAt_const.mul (((analyticAt_const.add analyticAt_id).pow k).sub analyticAt_const)
  have hpowerValue : power 0 = s ^ p := by
    dsimp [power]
    simp only [add_zero]
    linear_combination -(1 / 2 : ℂ) * hcurve
  obtain ⟨x, hx, hxs, hxpower⟩ := exists_analyticAt_root_with_value
    power hpower (by rw [hpowerValue]; exact pow_ne_zero _ hs) p hp.pos.ne' s hpowerValue.symm
  let f : ℂ → ℂ := fun u ↦ eval ![x u, 1] R - eval ![-x u, Y + u] R
  have hf : AnalyticAt ℂ f 0 :=
    (analyticAt_eval_finTwo R x (fun _ ↦ 1) hx analyticAt_const).sub
      (analyticAt_eval_finTwo R (fun u ↦ -x u) (fun u ↦ Y + u) hx.neg
        (analyticAt_const.add analyticAt_id))
  have hnonzero : ¬ ∀ᶠ u in nhds 0, f u = 0 := by
    intro hzero
    apply cyclicMixedZero_opposite_not_eventually_zero k p j d hk hp hj hdegree
      c γ Y hc hγ L hL x hxpower
    filter_upwards [hzero] with u hu
    dsimp [f] at hu
    rw [hR] at hu
    simp only [map_mul, map_add, eval_pow, eval_X, eval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one, cyclicInvariantLift_eval,
      one_pow, one_mul, mul_one] at hu
    rw [pow_add]
    linear_combination hu
  obtain ⟨m, unit, hunit, hunitZero, hfactor⟩ :=
    hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnonzero
  have hfzero : f 0 = 0 := by simpa [f, hxs] using hroot
  have hm : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    have hvalue := hfactor.self_of_nhds
    simp [hmzero, hfzero] at hvalue
    exact hunitZero hvalue.symm
  refine ⟨x, hx, hxs, ?_, m, unit, hm, hunit, hunitZero, ?_⟩
  · intro u
    rw [hxpower]
    dsimp [power]
    ring
  · simpa only [sub_zero, smul_eq_mul] using hfactor

/-- Finite-order opposite-sign zeros persist for the full analytic
equations, including their weighted tails. -/
theorem eventually_exists_cyclicMixedZero_mem_nhds
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (k p j d : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j)
    (hdegree : p * j = k * d) (c γ s Y : ℂ)
    (hc : c ≠ 0) (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hcurve : 2 * s ^ p = c * (Y ^ k - 1))
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j))
    (hroot : eval ![s, 1] R - eval ![-s, Y] R = 0)
    (hPhi : AnalyticAt ℂ Phi (0, ![s, -s, Y]))
    (hspecial : ∀ q, Phi (0, q) =
      weightedInitialDifference (cyclicResidualInitialMap k p c R) q)
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![s, -s, Y])) :
    ∀ᶠ tau in nhds 0, ∃ q : Fin 3 → ℂ, (tau, q) ∈ U ∧ Phi (tau, q) = 0 := by
  obtain ⟨x, hx, hxs, hcurveX, m, unit, hm, hunit, hunitZero, hfactor⟩ :=
    exists_cyclicMixedZero_branch_finite_order k p j d hk hp hj hdegree c γ s Y
      hc hγ hs hcurve L R hL hR hroot
  let parameter : ℂ → ℂ := fun u ↦ Y + u
  let v : ℂ → Fin 2 → ℂ := fun u ↦ ![x u, -x u]
  let rotate : ℂ × (Fin 3 → ℂ) → ℂ × (Fin 3 → ℂ) :=
    fun q ↦ (q.1, cyclicOppositeRotate q.2)
  let rotated : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ := fun q ↦ Phi (rotate q)
  let third : ℂ × (Fin 2 → ℂ) → ℂ := fun q ↦
    eval ![q.2 0, 1] R - eval ![q.2 1, Y + q.1] R
  have hparameter : AnalyticAt ℂ parameter 0 := analyticAt_const.add analyticAt_id
  have hv : AnalyticAt ℂ v 0 := by
    apply AnalyticAt.pi
    intro index
    fin_cases index
    · exact hx
    · exact hx.neg
  have hrotate (q : ℂ × (Fin 3 → ℂ)) : AnalyticAt ℂ rotate q :=
    analyticAt_fst.prod ((analyticAt_cyclicOppositeRotate q.2).fun_comp analyticAt_snd)
  have hrotated : AnalyticAt ℂ rotated (0, ![Y, s, -s]) :=
    hPhi.comp_of_eq (hrotate _) (by simp [rotate, cyclicOppositeRotate])
  let V : Set (ℂ × (Fin 3 → ℂ)) := rotate ⁻¹' U
  have hV : V ∈ nhds (0, ![Y, s, -s]) := (hrotate _).continuousAt.tendsto.eventually hU
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
        linear_combination hcurveX u
  · intro u point
    simp [hCollisionThirdPart, hCollisionReparametrization, hCollisionAffinePoint,
      rotated, rotate, cyclicOppositeRotate, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint, third, parameter]
  · simpa only [third, v, Matrix.cons_val_zero, Matrix.cons_val_one] using hfactor

/-- Every off-axis opposite-sign collision of a mixed zero-exponent
initial form contradicts injectivity of the full analytic germ. -/
theorem cyclicMixedZero_collision_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k p j d D : ℕ)
    (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j) (hdegree : p * j = k * d)
    (c γ s Y : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hcurve : 2 * s ^ p = c * (Y ^ k - 1))
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j))
    (hroot : eval ![s, 1] R - eval ![-s, Y] R = 0)
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  have hYone : Y ≠ 1 := by
    intro h
    have hxzero : s ^ p = 0 := by simpa [h] using hcurve
    exact pow_ne_zero p hs hxzero
  obtain ⟨representative, hanalytic, hzero, heq, hcomponents⟩ :=
    OnLeConjecture.DThree.PointedMapGerm.exists_pairRepresentative_with_components g
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasTwoWeightRadialExpansionAt_of_mem_twoWeightOrderIdeal
      k p hk hp.pos ![2 * k, p * k, D] (cyclicResidualPolynomialMap k p c R)
      (cyclicResidualPolynomialMap_homogeneous k p D c R hR)
      representative hanalytic (fun index ↦ by rw [hcomponents index]; exact htail index)
  simp only [weightedPolynomialMap_cyclicResidualPolynomialMap] at hexpansion
  rw [heq]
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_twoWeightChartZeros
    k p ![2 * k, p * k, D] (cyclicResidualInitialMap k p c R)
    representative remainder s (-s) Y hk hp.pos hYone (hexpansion (s, 1)) (hexpansion (-s, Y))
  intro U hU
  apply eventually_exists_cyclicMixedZero_mem_nhds
    (weightedRescaledPerturbation (cyclicResidualInitialMap k p c R) remainder)
    k p j d hk hp hj hdegree c γ s Y hc hγ hs hcurve L R hL hfactor hroot ?_ ?_ U hU
  · apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_cyclicResidualInitialDifference k p c R _
    · exact (hexpansion (s, 1)).remainder_analyticAt
    · exact (hexpansion (-s, Y)).remainder_analyticAt
  · intro q
    exact weightedRescaledPerturbation_zero _ _ q

/-- Odd descended degree supplies the isolated off-axis collision from
the polynomial data, and excludes analytic injectivity. -/
theorem cyclicMixedOdd_not_hasInjectiveRepresentative
    (g : PointedMapGerm 2 3) (k p j d D : ℕ)
    (hk : 0 < k) (hp : Odd p) (hd : Odd d) (hj : ¬ k ∣ j) (hdegree : p * j = k * d)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (L R : MvPolynomial (Fin 2) ℂ) (hL : L.IsWeightedHomogeneous ![1, p] d)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (cyclicInvariantLift k L + C γ * X 1 ^ j))
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) :
    ¬ g.HasInjectiveRepresentative := by
  obtain ⟨Y, hY, hYj⟩ := exists_cyclicMixedOdd_root k p j d hk hp hd hdegree
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-c) hp.pos
  have hsnonzero : s ≠ 0 := by
    intro h
    exact neg_ne_zero.mpr hc (by simpa [h, zero_pow hp.pos.ne'] using hs.symm)
  obtain ⟨hcurve, hroot⟩ := cyclicMixedOdd_initial_collision k p j d hp hd c γ s Y
    hs hY hYj L R hL hfactor
  exact cyclicMixedZero_collision_not_hasInjectiveRepresentative g k p j d D hk hp hj hdegree
    c γ s Y hc hγ hsnonzero hcurve L R hL hR hfactor hroot htail

/-- The invariant degree descended from the actual mixed residual must
be even. No Fermat intersection or finite-order hypothesis is supplied. -/
theorem cyclicMixedZero_descended_degree_even
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p j E D : ℕ) (hk : 0 < k) (hp : Odd p) (hj : ¬ k ∣ j) (hdegree : p * j = E)
    (c γ : ℂ) (hc : c ≠ 0) (hγ : γ ≠ 0)
    (R Λinv : MvPolynomial (Fin 2) ℂ)
    (hinv : Λinv ∈ cyclicInvariantAlgebra k)
    (hinvHom : Λinv.IsWeightedHomogeneous ![k, p] E) (hinvZero : Λinv ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (Λinv + C γ * X 1 ^ j))
    (htail : ∀ index, g.1.component index - Germ.coordinatePolynomialAlgHom 2
      (cyclicResidualPolynomialMap k p c R index) ∈
        Germ.twoWeightOrderIdeal k p (![2 * k, p * k, D] index + 1)) : Even (E / k) := by
  obtain ⟨d, L, _, hL, hE, hΛinv⟩ :=
    exists_cyclicInvariant_homogeneous_descent k p E hk Λinv hinvZero hinvHom hinv
  have hd : Even d := by
    rcases Nat.even_or_odd d with heven | hodd
    · exact heven
    · exact (cyclicMixedOdd_not_hasInjectiveRepresentative g k p j d D hk hp hodd hj
        (hdegree.trans hE) c γ hc hγ L R hL hR
        (by simpa only [hΛinv] using hfactor) htail hg).elim
  simpa only [hE, Nat.mul_div_cancel_left d hk] using hd

/-- For the prepared pair, the even-degree conclusion uses only its
analytic coordinate identities and the retained initial third remainder. -/
theorem cyclic_prepared_mixed_descended_degree_even
    (g : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (k p j E D : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p)
    (β : Germ 2) (hβ : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β)
    (γ : ℂ) (hγ : γ ≠ 0) (hj : ¬ k ∣ j) (hdegree : p * j = E)
    (R Λinv : MvPolynomial (Fin 2) ℂ)
    (hinv : Λinv ∈ cyclicInvariantAlgebra k)
    (hinvHom : Λinv.IsWeightedHomogeneous ![k, p] E) (hinvZero : Λinv ≠ 0)
    (hR : R.IsWeightedHomogeneous ![k, p] D)
    (hfactor : R = X 1 ^ k * (Λinv + C γ * X 1 ^ j))
    (htail : g.1.component 2 - Germ.coordinatePolynomialAlgHom 2 R ∈
      Germ.twoWeightOrderIdeal k p (D + 1)) : Even (E / k) := by
  apply cyclicMixedZero_descended_degree_even g hg k p j E D hk hodd hj hdegree
    (Germ.valueRingHom 2 β) γ hβ hγ R Λinv hinv hinvHom hinvZero hR hfactor
  have hpair := cyclic_pair_strict_tails g.firstTwo k p hk hp β
    (by simpa using hP) (by simpa using hQ)
  intro index
  fin_cases index
  · simpa [cyclicResidualPolynomialMap] using hpair 0
  · simpa [cyclicResidualPolynomialMap] using hpair 1
  · exact htail

end OnLeConjecture.DTwo
