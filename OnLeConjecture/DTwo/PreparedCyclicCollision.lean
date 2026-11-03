/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.PreparedCyclicPair
public import OnLeConjecture.Analytic.SimpleZeroCollision
public import OnLeConjecture.DThree.AnalyticThirdElimination
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Analytic collisions of the prepared cyclic pair

Weighted rescaling exhibits the transverse collision `(1,0),(-1,η)`,
where `β(0)ηᵏ = 2`. The analytic implicit function theorem preserves this
collision. This works for every positive `k`, including `k = 1`.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic Filter
open scoped Topology

/-- A function representative of the prepared analytic pair. -/
@[expose] noncomputable def cyclicPairFunction (k p : ℕ) (β : Source 2 → ℂ)
    (z : Source 2) : Source 2 := ![z 0 ^ 2 + z 1 ^ k, z 0 ^ p + z 1 ^ k * β z]

/-- The variable second point after weighted rescaling. -/
@[expose] noncomputable def cyclicCollisionSecond (k p : ℕ)
    (q : ℂ × Source 2) : Source 2 := ![q.1 ^ k * q.2 0, q.1 ^ p * q.2 1]

/-- The fixed first point after weighted rescaling. -/
@[expose] noncomputable def cyclicCollisionFirst (k : ℕ)
    (q : ℂ × Source 2) : Source 2 := ![q.1 ^ k, 0]

/-- The two rescaled equal-image equations. -/
@[expose] noncomputable def cyclicCollisionEquation (k p : ℕ) (β : Source 2 → ℂ)
    (q : ℂ × Source 2) : Source 2 :=
  ![q.2 0 ^ 2 + q.1 ^ (k * (p - 2)) * q.2 1 ^ k - 1,
    q.2 0 ^ p + q.2 1 ^ k * β (cyclicCollisionSecond k p q) - 1]

private theorem analyticAt_cyclicCollisionSecond (k p : ℕ) (q : ℂ × Source 2) :
    AnalyticAt ℂ (cyclicCollisionSecond k p) q := by
  have hcoord (i : Fin 2) : AnalyticAt ℂ (fun q : ℂ × Source 2 => q.2 i) q :=
    ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt q.2).fun_comp analyticAt_snd
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (analyticAt_fst.pow k).mul (hcoord 0)
  · exact (analyticAt_fst.pow p).mul (hcoord 1)

private theorem analyticAt_cyclicCollisionEquation (k p : ℕ) (hk : 0 < k)
    (hp : 0 < p) (β : Source 2 → ℂ) (hβ : AnalyticAt ℂ β 0) (η : ℂ) :
    AnalyticAt ℂ (cyclicCollisionEquation k p β) (0, ![-1, η]) := by
  have hs : cyclicCollisionSecond k p (0, ![-1, η]) = 0 := by
    simp [cyclicCollisionSecond, hk.ne', hp.ne']
  have hb := AnalyticAt.comp_of_eq hβ (analyticAt_cyclicCollisionSecond k p (0, ![-1, η])) hs
  have hcoord (i : Fin 2) :
      AnalyticAt ℂ (fun q : ℂ × Source 2 => q.2 i) (0, ![-1, η]) :=
    ((ContinuousLinearMap.proj (R := ℂ) i).comp
      (ContinuousLinearMap.snd ℂ ℂ (Source 2))).analyticAt _
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ((hcoord 0).pow 2 |>.add
      ((analyticAt_fst.pow (k * (p - 2))).mul ((hcoord 1).pow k))).sub analyticAt_const
  · exact ((hcoord 0).pow p |>.add (((hcoord 1).pow k).mul hb)).sub analyticAt_const

private noncomputable def cyclicCollisionDerivative (k p : ℕ) (c η : ℂ) :
    Source 2 →L[ℂ] Source 2 :=
  (Matrix.toLin' !![-2, 0; (p : ℂ) * (-1 : ℂ) ^ (p - 1),
    (k : ℂ) * η ^ (k - 1) * c]).toContinuousLinearMap

private theorem cyclicCollision_pointDerivative (k p : ℕ) (hk : 0 < k)
    (hp : 3 ≤ p) (β : Source 2 → ℂ) (η : ℂ) :
    HasStrictFDerivAt (fun z => cyclicCollisionEquation k p β (0, z))
      (cyclicCollisionDerivative k p (β 0) η) ![-1, η] := by
  have hslice : (fun z => cyclicCollisionEquation k p β (0, z)) =
      (fun z : Source 2 => ![z 0 ^ 2 - 1, z 0 ^ p + z 1 ^ k * β 0 - 1]) := by
    funext z
    simp [cyclicCollisionEquation, cyclicCollisionSecond, hk.ne',
      show p ≠ 0 by omega, show k * (p - 2) ≠ 0 from Nat.mul_ne_zero hk.ne' (by omega),
      show (![0, 0] : Source 2) = 0 from by ext i; fin_cases i <;> rfl]
  rw [hslice, hasStrictFDerivAt_pi']
  intro i
  fin_cases i
  · convert ((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![-1, η]).pow 2).sub_const 1
      using 1
    all_goals ext z
    all_goals simp [cyclicCollisionDerivative, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
  · convert (((hasStrictFDerivAt_apply (𝕜 := ℂ) (0 : Fin 2) ![-1, η]).pow p).add
      (((hasStrictFDerivAt_apply (𝕜 := ℂ) (1 : Fin 2) ![-1, η]).pow k).mul_const
        (β 0))).sub_const 1 using 1
    all_goals ext z
    all_goals simp [cyclicCollisionDerivative, Matrix.toLin'_apply, dotProduct, Fin.sum_univ_succ]
    all_goals ring

private theorem cyclicCollision_pointDerivative_invertible (k p : ℕ) (hk : 0 < k)
    (hp : 3 ≤ p) (β : Source 2 → ℂ) (hβ : AnalyticAt ℂ β 0)
    (hβzero : β 0 ≠ 0) (η : ℂ) (hη : η ≠ 0) :
    (fderiv ℂ (cyclicCollisionEquation k p β) (0, ![-1, η]) ∘L
      ContinuousLinearMap.inr ℂ ℂ (Source 2)).IsInvertible := by
  have han := analyticAt_cyclicCollisionEquation k p hk (by omega) β hβ η
  have hcomp := han.hasStrictFDerivAt.comp ![-1, η]
    (ContinuousLinearMap.inr ℂ ℂ (Source 2)).hasStrictFDerivAt
  have heq := hcomp.hasFDerivAt.unique
    (cyclicCollision_pointDerivative k p hk hp β η).hasFDerivAt
  rw [heq]
  have hdet : (cyclicCollisionDerivative k p (β 0) η).det ≠ 0 := by
    have hnonzero : (-2 : ℂ) * ((k : ℂ) * η ^ (k - 1) * β 0) ≠ 0 :=
      mul_ne_zero (by norm_num)
        (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hk.ne') (pow_ne_zero _ hη)) hβzero)
    simpa [cyclicCollisionDerivative, LinearMap.det_toContinuousLinearMap,
      LinearMap.det_toLin', Matrix.det_fin_two] using hnonzero
  exact ⟨(cyclicCollisionDerivative k p (β 0) η).toContinuousLinearEquivOfDetNeZero hdet,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _⟩

private theorem cyclicCollision_scaled_image (k p : ℕ) (hp : 3 ≤ p)
    (β : Source 2 → ℂ) (q : ℂ × Source 2) :
    cyclicPairFunction k p β (cyclicCollisionSecond k p q) =
      ![q.1 ^ (2 * k) * (cyclicCollisionEquation k p β q 0 + 1),
        q.1 ^ (p * k) * (cyclicCollisionEquation k p β q 1 + 1)] := by
  have hdegree : 2 * k + k * (p - 2) = p * k := by
    have : p - 2 + 2 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hpower : q.1 ^ (p * k) = q.1 ^ (2 * k) * q.1 ^ (k * (p - 2)) := by
    rw [← pow_add, hdegree]
  funext i
  fin_cases i
  · change cyclicPairFunction k p β (cyclicCollisionSecond k p q) 0 =
      q.1 ^ (2 * k) * (cyclicCollisionEquation k p β q 0 + 1)
    simp only [cyclicPairFunction, cyclicCollisionSecond, cyclicCollisionEquation,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow, ← pow_mul, Nat.mul_comm k 2]
    rw [hpower]
    ring
  · change cyclicPairFunction k p β (cyclicCollisionSecond k p q) 1 =
      q.1 ^ (p * k) * (cyclicCollisionEquation k p β q 1 + 1)
    simp only [cyclicPairFunction, cyclicCollisionSecond, cyclicCollisionEquation,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow, ← pow_mul, Nat.mul_comm k p]
    ring

/-- Every analytic prepared pair with odd `p ≥ 3` has collisions in each
neighborhood of the origin. The coefficient may depend on both coordinates. -/
theorem cyclicPairFunction_not_neighborhood_injective (k p : ℕ) (hk : 0 < k)
    (hp : 3 ≤ p) (hodd : Odd p) (β : Source 2 → ℂ)
    (hβ : AnalyticAt ℂ β 0) (hβzero : β 0 ≠ 0) :
    ¬ ∃ s ∈ 𝓝 (0 : Source 2), Set.InjOn (cyclicPairFunction k p β) s := by
  obtain ⟨η, hηpow⟩ := IsAlgClosed.exists_pow_nat_eq (2 / β 0) hk
  have hη : η ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hk.ne'] at hηpow
    exact (div_ne_zero (by norm_num) hβzero) hηpow.symm
  have hroot : η ^ k * β 0 = 2 := by
    rw [hηpow, div_mul_cancel₀ _ hβzero]
  have hbase : cyclicCollisionEquation k p β (0, ![-1, η]) = 0 := by
    norm_num [cyclicCollisionEquation, cyclicCollisionSecond, hk.ne',
      show p ≠ 0 by omega, show k * (p - 2) ≠ 0 from Nat.mul_ne_zero hk.ne' (by omega),
      show (![0, 0] : Source 2) = 0 from by ext i; fin_cases i <;> rfl,
      hodd.neg_one_pow, hroot]
  apply not_neighborhood_injective_of_analytic_simpleZeroCollision
    (cyclicPairFunction k p β) (cyclicCollisionEquation k p β) ![-1, η]
    (cyclicCollisionFirst k) (cyclicCollisionSecond k p) hbase
    (analyticAt_cyclicCollisionEquation k p hk (by omega) β hβ η)
    (cyclicCollision_pointDerivative_invertible k p hk hp β hβ hβzero η hη)
  · rw [continuousAt_pi]
    intro i
    fin_cases i
    · exact continuousAt_fst.pow k
    · exact continuousAt_const
  · exact (analyticAt_cyclicCollisionSecond k p _).continuousAt
  · simp [cyclicCollisionFirst, hk.ne']
  · simp [cyclicCollisionSecond, hk.ne', show p ≠ 0 by omega]
  · apply Filter.Eventually.of_forall
    intro q heq
    rw [cyclicCollision_scaled_image k p hp β q, heq]
    simp [cyclicPairFunction, cyclicCollisionFirst, hk.ne', ← pow_mul, Nat.mul_comm]
  · have hcoord : ContinuousAt (fun q : ℂ × Source 2 => q.2 0) (0, ![-1, η]) :=
      (continuous_apply 0).continuousAt.comp continuousAt_snd
    have hnear := hcoord.eventually_ne (show (![-1, η] : Source 2) 0 ≠ 1 by norm_num)
    filter_upwards [hnear] with q hq hparameter hsame
    apply hq
    have hsame0 := congrFun hsame 0
    change q.1 ^ k = q.1 ^ k * q.2 0 at hsame0
    have hcancel := mul_left_cancel₀ (pow_ne_zero k hparameter)
      (show q.1 ^ k * (1 : ℂ) = q.1 ^ k * q.2 0 by simpa using hsame0)
    exact hcancel.symm

/-- A pointed analytic germ with the prepared components has no injective
representative. This is proved by analytic collision persistence. -/
theorem cyclic_not_hasInjectiveRepresentative (f : PointedMapGerm 2 2)
    (k p : ℕ) (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβzero : Germ.valueRingHom 2 β ≠ 0)
    (hP : f.1.component 0 = cyclicFirst k)
    (hQ : f.1.component 1 = cyclicSecond k p β) :
    ¬ f.HasInjectiveRepresentative := by
  rcases β with ⟨β, hβanalytic⟩
  induction β using Filter.Germ.inductionOn with
  | _ β =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hβanalytic
      change β 0 ≠ 0 at hβzero
      have hcoordinate (i : Fin 2) : AnalyticAt ℂ (fun z : Source 2 => z i) 0 :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).analyticAt 0
      have hF : AnalyticAt ℂ (cyclicPairFunction k p β) 0 := by
        apply AnalyticAt.pi
        intro i
        fin_cases i
        · exact ((hcoordinate 0).pow 2).add ((hcoordinate 1).pow k)
        · exact ((hcoordinate 0).pow p).add (((hcoordinate 1).pow k).mul hβanalytic)
      have hFzero : cyclicPairFunction k p β 0 = 0 := by
        simp [cyclicPairFunction, hk.ne', show p ≠ 0 by omega]
      have hfg : f = PointedMapGerm.ofFunction (cyclicPairFunction k p β) hF hFzero := by
        apply PointedMapGerm.ext_components
        intro i
        fin_cases i
        · change f.1.component 0 = _
          rw [hP]
          apply Subtype.ext
          rfl
        · change f.1.component 1 = _
          rw [hQ]
          apply Subtype.ext
          rfl
      rw [hfg]
      exact PointedMapGerm.not_hasInjectiveRepresentative_ofFunction _ hF hFzero
        (cyclicPairFunction_not_neighborhood_injective k p hk hp hodd β hβanalytic hβzero)

/-- The third component of an injective prepared triple does not belong
to the analytic image ring of its first pair. -/
theorem cyclic_third_not_mem_imageRing (g : PointedMapGerm 2 3)
    (hg : g.HasInjectiveRepresentative) (k p : ℕ)
    (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβzero : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β) :
    g.1.component 2 ∉ g.firstTwo.ImageRing :=
  g.third_not_mem_imageRing_firstTwo_of_injective hg
    (cyclic_not_hasInjectiveRepresentative g.firstTwo k p hk hp hodd β hβzero
      (by simpa using hP) (by simpa using hQ))

/-- An injective prepared triple admits an analytic target expression
whose subtraction has a nonzero initial form outside the initial-pair algebra.
No associated graded image-algebra hypothesis is assumed. -/
theorem cyclic_injective_triple_initial_remainder (g : PointedMapGerm 2 3)
    (hg : g.HasInjectiveRepresentative) (k p : ℕ)
    (hk : 0 < k) (hp : 3 ≤ p) (hodd : Odd p) (β : Germ 2)
    (hβzero : Germ.valueRingHom 2 β ≠ 0)
    (hP : g.1.component 0 = cyclicFirst k)
    (hQ : g.1.component 1 = cyclicSecond k p β) :
    ∃ D : ℕ, ∃ Φ : Germ 2, ∃ R : MvPolynomial (Fin 2) ℂ,
      R ≠ 0 ∧ R.IsWeightedHomogeneous ![k, p] D ∧
      g.1.component 2 - g.firstTwo.pullbackRingHom Φ ∈ Germ.twoWeightOrderIdeal k p D ∧
      g.1.component 2 - g.firstTwo.pullbackRingHom Φ - Germ.coordinatePolynomialAlgHom 2 R ∈
        Germ.twoWeightOrderIdeal k p (D + 1) ∧
      R ∉ Set.range (MvPolynomial.aeval (cyclicInitialPair k p (Germ.valueRingHom 2 β)) :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ) :=
  cyclic_exists_initial_form_outside_pair_algebra g.firstTwo k p hk hp β hβzero
    (by simpa using hP) (by simpa using hQ) (g.1.component 2)
    (cyclic_third_not_mem_imageRing g hg k p hk hp hodd β hβzero hP hQ)

end OnLeConjecture.DTwo
