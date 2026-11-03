/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultipleZeroPersistence
public import OnLeConjecture.Analytic.MonicRootConvergence
public import OnLeConjecture.Analytic.ParametricResultant
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Persistence of common roots of analytic polynomial families

The coefficients are analytic functions, not formal coefficients. Fixed
degree resultants are analytic, and their scalar zeros give common roots.
Monic specialization to a coordinate power confines every common root.
-/

public section

open Filter Set Polynomial
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic

/-- A fixed degree resultant is analytic in analytic polynomial coefficients. -/
theorem analyticAt_fixedDegreeResultant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P Q : E → Polynomial ℂ) (d e : ℕ) (z : E)
    (hP : ∀ n, AnalyticAt ℂ (fun w ↦ (P w).coeff n) z)
    (hQ : ∀ n, AnalyticAt ℂ (fun w ↦ (Q w).coeff n) z) :
    AnalyticAt ℂ (fun w ↦ (P w).resultant (Q w) d e) z := by
  have hmatrix (i j : Fin (d + e)) :
      AnalyticAt ℂ (fun w ↦ (P w).sylvester (Q w) d e i j) z := by
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact hQ _
        · exact analyticAt_const
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact hP _
        · exact analyticAt_const
  simp only [Polynomial.resultant, Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro permutation _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hmatrix _ _

/-- Over the complex numbers, a zero resultant of a monic polynomial and
a degree-bounded polynomial gives a common root, including a zero second polynomial. -/
theorem exists_common_root_of_monic_fixedDegreeResultant_eq_zero
    (P Q : Polynomial ℂ) (e : ℕ) (hP : P.Monic) (hQ : Q.natDegree ≤ e)
    (hzero : P.resultant Q P.natDegree e = 0) :
    ∃ x : ℂ, P.IsRoot x ∧ Q.IsRoot x := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hQ
  subst e
  rw [Polynomial.resultant_add_right_deg, hP.coeff_natDegree, one_pow, one_mul] at hzero
  · have hcoprime := (Polynomial.resultant_eq_zero_iff.mp hzero).2
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := ℂ) (K := ℂ)] at hcoprime
    push Not at hcoprime
    simpa [Polynomial.IsRoot.def, Polynomial.aeval_def] using hcoprime
  · exact le_rfl

/-- All roots of a fixed degree monic family tend uniformly to zero when
the polynomial at the base point is `Xᵈ`. No choice of continuous roots is used. -/
theorem eventually_forall_monic_root_mem_nhds
    {E : Type*} [TopologicalSpace E] [Zero E]
    (P : E → Polynomial ℂ) (d : ℕ) (hd : 0 < d)
    (hP : ∀ z, (P z).Monic) (hdegree : ∀ z, (P z).natDegree = d)
    (hcoeff : ∀ i : Fin d, ContinuousAt (fun z ↦ (P z).coeff i) 0)
    (hbase : P 0 = Polynomial.X ^ d)
    (U : Set ℂ) (hU : U ∈ nhds 0) :
    ∀ᶠ z in nhds 0, ∀ x : ℂ, (P z).IsRoot x → x ∈ U := by
  let RootData := {q : E × ℂ // (P q.1).IsRoot q.2}
  let projection : RootData → E := fun q ↦ q.1.1
  let root : RootData → ℂ := fun q ↦ q.1.2
  let l : Filter RootData := Filter.comap projection (nhds 0)
  have hcoefficient (i : Fin d) :
      Tendsto (fun q : RootData ↦ (P (projection q)).coeff i) l (nhds 0) := by
    have hzero : (P 0).coeff i = 0 := by
      simp [hbase, show (i : ℕ) ≠ d from Nat.ne_of_lt i.isLt]
    have ht := (hcoeff i).tendsto
    rw [hzero] at ht
    exact ht.comp tendsto_comap
  have hrelation (q : RootData) :
      root q ^ d + ∑ i : Fin d, (P (projection q)).coeff i * root q ^ (i : ℕ) = 0 := by
    have hleading : (P (projection q)).coeff d = 1 := by
      rw [← hdegree (projection q)]
      exact (hP _).coeff_natDegree
    have heval := (P (projection q)).eval_eq_sum_range (root q)
    rw [hdegree, Finset.sum_range_succ, hleading, one_mul, add_comm,
      ← Fin.sum_univ_eq_sum_range] at heval
    exact heval.symm.trans q.property
  have ht := tendsto_zero_of_monic_power_relation hd
    (fun i q ↦ (P (projection q)).coeff i) root hcoefficient
    (Filter.Eventually.of_forall hrelation)
  have heventual := Filter.eventually_comap.mp (ht.eventually hU)
  filter_upwards [heventual] with z hz
  intro x hx
  exact hz ⟨(z, x), hx⟩ rfl

/-- An isolated special-fibre resultant zero produces common roots in
every neighborhood of the origin for all sufficiently small parameters. -/
theorem eventually_exists_common_root_mem_nhds_of_resultant_finite_order
    (P Q : ℂ × ℂ → Polynomial ℂ) (d e : ℕ) (hd : 0 < d)
    (hP : ∀ n, AnalyticAt ℂ (fun z ↦ (P z).coeff n) (0, 0))
    (hQ : ∀ n, AnalyticAt ℂ (fun z ↦ (Q z).coeff n) (0, 0))
    (hmonic : ∀ z, (P z).Monic) (hdegree : ∀ z, (P z).natDegree = d)
    (hQdegree : ∀ z, (Q z).natDegree ≤ e)
    (hbase : P (0, 0) = Polynomial.X ^ d)
    (m : ℕ) (unit : ℂ → ℂ) (hm : 0 < m)
    (hunit : AnalyticAt ℂ unit 0) (hunitZero : unit 0 ≠ 0)
    (hfactor : ∀ᶠ x in nhds 0,
      (P (0, x)).resultant (Q (0, x)) d e = x ^ m * unit x)
    (U : Set ((ℂ × ℂ) × ℂ)) (hU : U ∈ nhds ((0, 0), 0)) :
    ∀ᶠ tau in nhds 0, ∃ x y : ℂ,
      ((tau, x), y) ∈ U ∧ (P (tau, x)).IsRoot y ∧ (Q (tau, x)).IsRoot y := by
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hU
  have hconfine := eventually_forall_monic_root_mem_nhds P d hd hmonic hdegree
    (fun i ↦ (hP i).continuousAt) hbase W hW
  have hnear : ∀ᶠ z in nhds ((0, 0) : ℂ × ℂ),
      z ∈ V ∧ ∀ y : ℂ, (P z).IsRoot y → y ∈ W := Filter.Eventually.and hV hconfine
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨r, _, hrdelta, hzeros⟩ :=
    eventually_exists_zero_of_analyticAt_of_specialFiber_factorization_lt
      (fun z ↦ (P z).resultant (Q z) d e) m unit hm
      (analyticAt_fixedDegreeResultant P Q d e (0, 0) hP hQ)
      hunit hunitZero hfactor delta hdelta
  filter_upwards [hzeros, Metric.ball_mem_nhds (0 : ℂ) hdelta] with tau htau hsmall
  obtain ⟨x, hx, hresultant⟩ := htau
  have hxsmall : dist x 0 < delta :=
    (Metric.mem_closedBall.mp hx).trans_lt hrdelta
  have hparameter : (tau, x) ∈ Metric.ball ((0, 0) : ℂ × ℂ) delta := by
    simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using
      And.intro (Metric.mem_ball.mp hsmall) hxsmall
  obtain ⟨y, hPy, hQy⟩ := exists_common_root_of_monic_fixedDegreeResultant_eq_zero
    (P (tau, x)) (Q (tau, x)) e (hmonic _) (hQdegree _)
    (by rwa [hdegree])
  have hnearAt := hball hparameter
  exact ⟨x, y, hVW ⟨hnearAt.1, hnearAt.2 y hPy⟩, hPy, hQy⟩

/-- A nonzero resultant germ on the special fibre, vanishing at its origin,
suffices. Its finite order and unit factor are deduced from analyticity. -/
theorem eventually_exists_common_root_mem_nhds_of_resultant_not_locally_zero
    (P Q : ℂ × ℂ → Polynomial ℂ) (d e : ℕ) (hd : 0 < d)
    (hP : ∀ n, AnalyticAt ℂ (fun z ↦ (P z).coeff n) (0, 0))
    (hQ : ∀ n, AnalyticAt ℂ (fun z ↦ (Q z).coeff n) (0, 0))
    (hmonic : ∀ z, (P z).Monic) (hdegree : ∀ z, (P z).natDegree = d)
    (hQdegree : ∀ z, (Q z).natDegree ≤ e)
    (hbase : P (0, 0) = Polynomial.X ^ d) (hQzero : (Q (0, 0)).IsRoot 0)
    (hnonzero : ¬ ∀ᶠ x in nhds 0, (P (0, x)).resultant (Q (0, x)) d e = 0)
    (U : Set ((ℂ × ℂ) × ℂ)) (hU : U ∈ nhds ((0, 0), 0)) :
    ∀ᶠ tau in nhds 0, ∃ x y : ℂ,
      ((tau, x), y) ∈ U ∧ (P (tau, x)).IsRoot y ∧ (Q (tau, x)).IsRoot y := by
  have hresultant := analyticAt_fixedDegreeResultant P Q d e (0, 0) hP hQ
  have hscalar : AnalyticAt ℂ (fun x ↦ (P (0, x)).resultant (Q (0, x)) d e) 0 :=
    hresultant.comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨m, unit, hunit, hunitZero, hfactor⟩ :=
    hscalar.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnonzero
  have hresultantZero : (P (0, 0)).resultant (Q (0, 0)) d e = 0 := by
    rw [← hdegree (0, 0)]
    apply PolynomialResultant.resultant_eq_zero_of_common_root_fixedDegree
      _ _ e (hmonic _) (hQdegree _) (x := 0) ?_ hQzero
    simp [hbase, Polynomial.IsRoot.def, hd.ne']
  have hm : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    have hvalue := hfactor.self_of_nhds
    simp [hmzero, hresultantZero] at hvalue
    exact hunitZero hvalue.symm
  apply eventually_exists_common_root_mem_nhds_of_resultant_finite_order
    P Q d e hd hP hQ hmonic hdegree hQdegree hbase m unit hm hunit hunitZero ?_ U hU
  simpa only [sub_zero, smul_eq_mul] using hfactor

/-- Evaluation at an analytic argument preserves analyticity for a family
of polynomials with analytic coefficients and a uniform finite degree bound. -/
theorem analyticAt_polynomialFamily_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : E → Polynomial ℂ) (e : ℕ) (x : E → ℂ) (z : E)
    (hQ : ∀ n, AnalyticAt ℂ (fun w ↦ (Q w).coeff n) z)
    (hdegree : ∀ w, (Q w).natDegree ≤ e) (hx : AnalyticAt ℂ x z) :
    AnalyticAt ℂ (fun w ↦ (Q w).eval (x w)) z := by
  have heq : (fun w ↦ (Q w).eval (x w)) =
      fun w ↦ ∑ i ∈ Finset.range (e + 1), (Q w).coeff i * x w ^ i := by
    funext w
    exact Polynomial.eval_eq_sum_range' (by have := hdegree w; omega) (x w)
  rw [heq]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact (hQ i).mul (hx.pow i)

/-- The quadratic resultant is the product of the restrictions to its two
branches. This identity remains valid when the second polynomial is zero. -/
theorem resultant_X_sq_sub_C_sq (Q : Polynomial ℂ) (e : ℕ)
    (hQ : Q.natDegree ≤ e) (x : ℂ) :
    (Polynomial.X ^ 2 - Polynomial.C (x ^ 2)).resultant Q 2 e =
      Q.eval x * Q.eval (-x) := by
  have hproduct : (Polynomial.X ^ 2 - Polynomial.C (x ^ 2) : Polynomial ℂ) =
      (Polynomial.X - Polynomial.C x) * (Polynomial.X + Polynomial.C x) := by
    rw [map_pow]
    ring
  rw [hproduct]
  have hresultant := Polynomial.resultant_mul_left
    (Polynomial.X - Polynomial.C x) (Polynomial.X + Polynomial.C x) Q e hQ
  simpa only [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_add_C,
    Nat.reduceAdd, Polynomial.resultant_X_sub_C_left Q e x hQ,
    Polynomial.resultant_X_add_C_left Q e x hQ] using hresultant

private theorem exists_positive_analytic_factorization
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hfzero : f 0 = 0)
    (hne : ¬ ∀ᶠ x in nhds 0, f x = 0) :
    ∃ m : ℕ, ∃ unit : ℂ → ℂ, 0 < m ∧ AnalyticAt ℂ unit 0 ∧ unit 0 ≠ 0 ∧
      ∀ᶠ x in nhds 0, f x = x ^ m * unit x := by
  obtain ⟨m, unit, hunit, hunitZero, hfactor⟩ :=
    hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hm : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    have hvalue := hfactor.self_of_nhds
    simp [hmzero, hfzero] at hvalue
    exact hunitZero hvalue.symm
  exact ⟨m, unit, hm, hunit, hunitZero, by
    simpa only [sub_zero, smul_eq_mul] using hfactor⟩

/-- If the special first polynomial is `Y² - x²` and neither restriction
of the second polynomial to `Y = ±x` vanishes identically, their common
origin persists under all analytic coefficient perturbations. -/
theorem eventually_exists_common_root_mem_nhds_of_quadratic_branches
    (P Q : ℂ × ℂ → Polynomial ℂ) (e : ℕ)
    (hP : ∀ n, AnalyticAt ℂ (fun z ↦ (P z).coeff n) (0, 0))
    (hQ : ∀ n, AnalyticAt ℂ (fun z ↦ (Q z).coeff n) (0, 0))
    (hmonic : ∀ z, (P z).Monic) (hdegree : ∀ z, (P z).natDegree = 2)
    (hQdegree : ∀ z, (Q z).natDegree ≤ e)
    (hspecial : ∀ᶠ x in nhds 0, P (0, x) = Polynomial.X ^ 2 - Polynomial.C (x ^ 2))
    (hQzero : (Q (0, 0)).IsRoot 0)
    (hplus : ¬ ∀ᶠ x in nhds 0, (Q (0, x)).eval x = 0)
    (hminus : ¬ ∀ᶠ x in nhds 0, (Q (0, x)).eval (-x) = 0)
    (U : Set ((ℂ × ℂ) × ℂ)) (hU : U ∈ nhds ((0, 0), 0)) :
    ∀ᶠ tau in nhds 0, ∃ x y : ℂ,
      ((tau, x), y) ∈ U ∧ (P (tau, x)).IsRoot y ∧ (Q (tau, x)).IsRoot y := by
  have hQfiber (n : ℕ) : AnalyticAt ℂ (fun x ↦ (Q (0, x)).coeff n) 0 :=
    (hQ n).comp (analyticAt_const.prod analyticAt_id)
  have hplusAnalytic := analyticAt_polynomialFamily_eval (fun x ↦ Q (0, x)) e
    id 0 hQfiber (fun x ↦ hQdegree (0, x)) analyticAt_id
  have hminusAnalytic := analyticAt_polynomialFamily_eval (fun x ↦ Q (0, x)) e
    (fun x ↦ -x) 0 hQfiber (fun x ↦ hQdegree (0, x)) analyticAt_id.neg
  obtain ⟨m, u, hm, hu, huZero, hufactor⟩ := exists_positive_analytic_factorization
    (fun x ↦ (Q (0, x)).eval x) hplusAnalytic hQzero hplus
  obtain ⟨n, v, _, hv, hvZero, hvfactor⟩ := exists_positive_analytic_factorization
    (fun x ↦ (Q (0, x)).eval (-x)) hminusAnalytic (by simpa using hQzero) hminus
  have hbase : P (0, 0) = Polynomial.X ^ 2 := by
    simpa using hspecial.self_of_nhds
  apply eventually_exists_common_root_mem_nhds_of_resultant_finite_order
    P Q 2 e (by decide) hP hQ hmonic hdegree hQdegree hbase
    (m + n) (fun x ↦ u x * v x) (by omega) (hu.mul hv) (mul_ne_zero huZero hvZero) ?_ U hU
  filter_upwards [hspecial, hufactor, hvfactor] with x hx huAt hvAt
  rw [hx, resultant_X_sq_sub_C_sq _ e (hQdegree _) x, huAt, hvAt, pow_add]
  ring

end OnLeConjecture.Analytic
