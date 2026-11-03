/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.FiniteResultantElimination
public import OnLeConjecture.Analytic.PolynomialCommonZeroPersistence
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.DivisionRepresentatives
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.PolynomialFibers

/-!
# Analytic equations for projection along a prepared coordinate

Weierstrass division replaces finitely many analytic equations by polynomial
remainders. A finite list of resultants then gives analytic equations for
the exact projection of their common zero set with a prepared polynomial.
Prepared-root confinement puts every lift in any prescribed neighborhood.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic

open LocalComplexGeometry

/-- Analytic coefficients of a polynomial remainder give analytic scalar
functions for every coefficient of the specialized polynomial. -/
theorem analyticAt_coeff_remainderPolynomialAt {n d : ℕ}
    (b : Fin d → ComplexEuclidean n → ℂ)
    (hb : ∀ i, AnalyticAt ℂ (b i) 0) (k : ℕ) :
    AnalyticAt ℂ (fun z => (remainderPolynomialAt b z).coeff k) 0 := by
  classical
  simp only [remainderPolynomialAt, _root_.Polynomial.finsetSum_coeff,
    _root_.Polynomial.coeff_C_mul_X_pow]
  apply Finset.analyticAt_fun_sum
  intro i hi
  split_ifs
  · exact hb i
  · exact analyticAt_const

/-- Every coefficient of a specialized prepared polynomial is analytic. -/
theorem analyticAt_coeff_preparedPolynomialAt {n d : ℕ}
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (k : ℕ) :
    AnalyticAt ℂ (fun z => (preparedPolynomialAt a z).coeff k) 0 := by
  have heq (z : ComplexEuclidean n) :
      preparedPolynomialAt a z = _root_.Polynomial.X ^ d + remainderPolynomialAt a z := rfl
  simp_rw [heq, _root_.Polynomial.coeff_add]
  exact analyticAt_const.add (analyticAt_coeff_remainderPolynomialAt a ha k)

/-- A prepared polynomial together with finitely many analytic equations
has an exact projection described by finitely many analytic equations.
The same equations work for every prescribed neighborhood of the ambient
origin after shrinking the base neighborhood. -/
theorem exists_analytic_equations_for_prepared_projection
    {n d r : ℕ} (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (H : Fin r → ComplexEuclidean (n + 1) → ℂ)
    (hH : ∀ j, AnalyticAt ℂ (H j) 0) :
    ∃ E : Fin (d * r + 1) → ComplexEuclidean n → ℂ,
      (∀ k, AnalyticAt ℂ (E k) 0) ∧
      ∀ (V : Set (ComplexEuclidean (n + 1))), V ∈ 𝓝 0 →
        ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
          (∀ k, E k z = 0) ↔
            ∃ w : ℂ, appendLastCLE n (z, w) ∈ V ∧
              preparedValue a z w = 0 ∧
              ∀ j, H j (appendLastCLE n (z, w)) = 0 := by
  classical
  let h (j : Fin r) := HolomorphicGerm.ofFunction (H j) (hH j)
  let b (j : Fin r) : Fin d → ComplexEuclidean n → ℂ :=
    HolomorphicGerm.coefficientRepresentatives
      (WPTBridge.preparedGermDivisionRemainder a ha ha0 (h j))
  let R (j : Fin r) (z : ComplexEuclidean n) := remainderPolynomialAt (b j) z
  let P (z : ComplexEuclidean n) := preparedPolynomialAt a z
  let E (k : Fin (d * r + 1)) (z : ComplexEuclidean n) :=
    _root_.Polynomial.resultant (P z)
      (OnLeConjecture.Polynomial.momentCombination (fun j => R j z) (k : ℕ)) d d
  have hb (j : Fin r) (i : Fin d) : AnalyticAt ℂ (b j i) 0 :=
    HolomorphicGerm.analyticAt_coefficientRepresentatives _ i
  have hR (j : Fin r) (k : ℕ) : AnalyticAt ℂ (fun z => (R j z).coeff k) 0 :=
    analyticAt_coeff_remainderPolynomialAt (b j) (hb j) k
  have hE (k : Fin (d * r + 1)) : AnalyticAt ℂ (E k) 0 := by
    apply analyticAt_fixedDegreeResultant _ _ d d 0
    · exact analyticAt_coeff_preparedPolynomialAt a ha
    · intro l
      simp only [OnLeConjecture.Polynomial.momentCombination,
        _root_.Polynomial.finsetSum_coeff, _root_.Polynomial.coeff_C_mul]
      apply Finset.analyticAt_fun_sum
      intro j hj
      exact analyticAt_const.mul (hR j l)
  have hrepresentative (j : Fin r) :
      HolomorphicGerm.representative (h j) =ᶠ[𝓝 0] H j :=
    Filter.Germ.coe_eq.mp (HolomorphicGerm.coe_representative (h j))
  have hremainder (j : Fin r) : ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
      ∀ w : ℂ, preparedValue a z w = 0 →
        H j (appendLastCLE n (z, w)) = (R j z).eval w := by
    have hdivision := eventually_representative_eq_remainder_on_preparedRoots
      hd a ha ha0 (h j)
    have hpointwise := eventually_on_all_prepared_roots hd a ha ha0 (hrepresentative j)
    filter_upwards [hdivision, hpointwise] with z hzdivision hzpointwise
    intro w hw
    rw [← hzpointwise w hw, hzdivision w hw]
    exact (remainderPolynomialAt_eval (b j) z w).symm
  have hremainderAll := Filter.eventually_all.mpr hremainder
  refine ⟨E, hE, ?_⟩
  intro V hV
  have hconfine := eventually_appendLast_mem_of_preparedValue_eq_zero hd a ha ha0 hV
  filter_upwards [hremainderAll, hconfine] with z hz hconfineZ
  have hdegree : (P z).natDegree = d := preparedPolynomialAt_natDegree a z
  have hcommon := OnLeConjecture.Polynomial.exists_common_root_iff_finite_resultants_vanish
    (P z) (preparedPolynomialAt_monic a z) (fun j => R j z)
    (fun j => (remainderPolynomialAt_natDegree_lt hd (b j) z).le)
  rw [hdegree] at hcommon
  change (∀ k, E k z = 0) ↔ _
  rw [show (∀ k, E k z = 0) ↔
      ∃ w : ℂ, (P z).eval w = 0 ∧ ∀ j, (R j z).eval w = 0 from hcommon.symm]
  constructor
  · rintro ⟨w, hwP, hwR⟩
    have hw : preparedValue a z w = 0 := by
      simpa only [P, preparedPolynomialAt_eval] using hwP
    exact ⟨w, hconfineZ w hw, hw, fun j => (hz j w hw).trans (hwR j)⟩
  · rintro ⟨w, _, hw, hwH⟩
    refine ⟨w, ?_, fun j => (hz j w hw).symm.trans (hwH j)⟩
    simpa only [P, preparedPolynomialAt_eval] using hw

/-- Append two coordinates successively, keeping the base coordinates first. -/
noncomputable def appendTwoCoordinates (n : ℕ) (z : ComplexEuclidean n) (u v : ℂ) :
    ComplexEuclidean (n + 1 + 1) :=
  appendLastCLE (n + 1) (appendLastCLE n (z, u), v)

/-- Two successive prepared projections give exact analytic equations for
eliminating two coordinates. All lifts remain in an arbitrarily prescribed
ambient neighborhood. -/
theorem exists_analytic_equations_for_two_prepared_projections
    {n d₁ d₂ r : ℕ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (a₁ : Fin d₁ → ComplexEuclidean n → ℂ)
    (a₂ : Fin d₂ → ComplexEuclidean n → ℂ)
    (ha₁ : ∀ i, AnalyticAt ℂ (a₁ i) 0) (ha₁0 : ∀ i, a₁ i 0 = 0)
    (ha₂ : ∀ i, AnalyticAt ℂ (a₂ i) 0) (ha₂0 : ∀ i, a₂ i 0 = 0)
    (H : Fin r → ComplexEuclidean (n + 1 + 1) → ℂ)
    (hH : ∀ j, AnalyticAt ℂ (H j) 0) :
    ∃ E : Fin (d₁ * (d₂ * r + 1) + 1) → ComplexEuclidean n → ℂ,
      (∀ k, AnalyticAt ℂ (E k) 0) ∧
      ∀ (V : Set (ComplexEuclidean (n + 1 + 1))), V ∈ 𝓝 0 →
        ∀ᶠ z in 𝓝 (0 : ComplexEuclidean n),
          (∀ k, E k z = 0) ↔
            ∃ u v : ℂ, appendTwoCoordinates n z u v ∈ V ∧
              preparedValue a₁ z u = 0 ∧ preparedValue a₂ z v = 0 ∧
              ∀ j, H j (appendTwoCoordinates n z u v) = 0 := by
  let b₂ (i : Fin d₂) (x : ComplexEuclidean (n + 1)) := a₂ i (dropLastCLM n x)
  have hb₂ (i : Fin d₂) : AnalyticAt ℂ (b₂ i) 0 := by
    apply (ha₂ i).comp_of_eq ((dropLastCLM n).analyticAt 0)
    exact map_zero _
  have hb₂0 (i : Fin d₂) : b₂ i 0 = 0 := by
    simpa only [b₂, map_zero] using ha₂0 i
  obtain ⟨E₁, hE₁, hprojection₁⟩ :=
    exists_analytic_equations_for_prepared_projection hd₂ b₂ hb₂ hb₂0 H hH
  obtain ⟨E, hE, hprojection⟩ :=
    exists_analytic_equations_for_prepared_projection hd₁ a₁ ha₁ ha₁0 E₁ hE₁
  refine ⟨E, hE, ?_⟩
  intro V hV
  let W : Set (ComplexEuclidean (n + 1)) := {x |
    (∀ k, E₁ k x = 0) ↔ ∃ v : ℂ, appendLastCLE (n + 1) (x, v) ∈ V ∧
      preparedValue b₂ x v = 0 ∧ ∀ j, H j (appendLastCLE (n + 1) (x, v)) = 0}
  have hW : W ∈ 𝓝 0 := hprojection₁ V hV
  have hconfine := eventually_appendLast_mem_of_preparedValue_eq_zero
    hd₁ a₁ ha₁ ha₁0 hW
  filter_upwards [hprojection W hW, hconfine] with z hz hconfineZ
  have hprepared (u v : ℂ) :
      preparedValue b₂ (appendLastCLE n (z, u)) v = preparedValue a₂ z v := by
    simp only [preparedValue, b₂, dropLastCLM_appendLastCLE]
  constructor
  · intro hzero
    obtain ⟨u, huW, hu, huE⟩ := hz.mp hzero
    obtain ⟨v, hvV, hv, hvH⟩ := huW.mp huE
    exact ⟨u, v, hvV, hu, (hprepared u v) ▸ hv, hvH⟩
  · rintro ⟨u, v, huvV, hu, hv, huvH⟩
    have huW := hconfineZ u hu
    apply hz.mpr
    refine ⟨u, huW, hu, huW.mpr ⟨v, huvV, ?_, huvH⟩⟩
    rwa [hprepared]

end OnLeConjecture.Analytic
