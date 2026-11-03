/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.GenericLinearCombination
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Open coefficient sets of squarefree polynomial combinations

At a fixed maximal degree, nonvanishing of the leading coefficient and
the Sylvester determinant is an open condition. It is equivalent to
nonvanishing of the leading coefficient and squarefreeness. Finitely many
polynomial families without common zeros therefore have a common nonempty
open coefficient set of squarefree members attaining their maximal degrees.
-/

public section

namespace OnLeConjecture.Polynomial

open _root_.Polynomial
open scoped BigOperators

/-- The resultant with fixed matrix dimensions depends continuously on
the polynomial coefficients. No polynomial-degree condition is required. -/
theorem continuous_resultant_of_continuous_coeff
    {T : Type*} [TopologicalSpace T] (P Q : T → ℂ[X])
    (hP : ∀ j, Continuous (fun t => (P t).coeff j))
    (hQ : ∀ j, Continuous (fun t => (Q t).coeff j)) (m n : ℕ) :
    Continuous (fun t => resultant (P t) (Q t) m n) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  induction j using Fin.addCases with
  | left j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · exact continuous_const
  | right j =>
      simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · exact continuous_const

/-- In characteristic zero, the resultant against the derivative has
exactly the expected fixed dimensions whenever the leading coefficient
at the prescribed degree is nonzero. -/
theorem squarefree_iff_fixed_resultant_ne_zero
    (P : ℂ[X]) (n : ℕ) (hdegree : P.natDegree ≤ n) (hcoeff : P.coeff n ≠ 0) :
    Squarefree P ↔ resultant P P.derivative n (n - 1) ≠ 0 := by
  have hPn : P.natDegree = n := le_antisymm hdegree (le_natDegree_of_ne_zero hcoeff)
  have hP : P ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, coeff_zero])
  have hderivative : P.derivative.natDegree = n - 1 := by
    rw [natDegree_derivative, hPn]
  rw [← hderivative, ← hPn]
  constructor
  · intro hsquarefree
    exact resultant_ne_zero P P.derivative
      ((PerfectField.separable_iff_squarefree).mpr hsquarefree)
  · intro hresultant
    have hcoprime : IsCoprime P P.derivative := by
      by_contra hnot
      exact hresultant (resultant_eq_zero_iff.mpr ⟨Or.inl hP, hnot⟩)
    exact (show P.Separable from hcoprime).squarefree

/-- The simultaneous nonzero leading coefficient and squarefree condition
is open for a polynomial family of bounded degree. -/
theorem isOpen_coeff_ne_zero_and_squarefree
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (n : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ n)
    (hcoeff : ∀ j, Continuous (fun t => (P t).coeff j)) :
    IsOpen {t | (P t).coeff n ≠ 0 ∧ Squarefree (P t)} := by
  have hderivative (j : ℕ) : Continuous (fun t => (P t).derivative.coeff j) := by
    simp only [coeff_derivative]
    exact (hcoeff (j + 1)).mul continuous_const
  have hresultant := continuous_resultant_of_continuous_coeff P
    (fun t => (P t).derivative) hcoeff hderivative n (n - 1)
  have hset : {t | (P t).coeff n ≠ 0 ∧ Squarefree (P t)} =
      {t | (P t).coeff n ≠ 0} ∩
        {t | resultant (P t) (P t).derivative n (n - 1) ≠ 0} := by
    ext t
    change (_ ∧ _) ↔ (_ ∧ _)
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc, (squarefree_iff_fixed_resultant_ne_zero (P t) n (hdegree t) hc).mp hs⟩
    · rintro ⟨hc, hr⟩
      exact ⟨hc, (squarefree_iff_fixed_resultant_ne_zero (P t) n (hdegree t) hc).mpr hr⟩
  rw [hset]
  exact (isOpen_ne_fun (hcoeff n) continuous_const).inter
    (isOpen_ne_fun hresultant continuous_const)

theorem continuous_coeff_polynomialLinearCombination
    {ι : Type*} [Fintype ι] (F : ι → ℂ[X]) (j : ℕ) :
    Continuous (fun q : ι → ℂ => (polynomialLinearCombination F q).coeff j) := by
  change Continuous (fun q : ι → ℂ => (∑ i, q i • F i).coeff j)
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul]
  fun_prop

theorem natDegree_polynomialLinearCombination_le
    {ι : Type*} [Fintype ι] (F : ι → ℂ[X]) (n : ℕ)
    (hdegree : ∀ i, (F i).natDegree ≤ n) (q : ι → ℂ) :
    (polynomialLinearCombination F q).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_smul_le _ _).trans (hdegree i)

/-- All families have squarefree members of their prescribed maximal
degrees throughout one nonempty open subset of the supplied open set. -/
theorem exists_open_squarefree_linear_combinations_of_degree_bounds
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → ℂ[X]) (hbase : ∀ k z, ∃ i, (F k i).eval z ≠ 0)
    (n : κ → ℕ) (hdegree : ∀ k i, (F k i).natDegree ≤ n k)
    (hattained : ∀ k, ∃ i, (F k i).coeff (n k) ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ k, Squarefree (polynomialLinearCombination (F k) q) ∧
        (polynomialLinearCombination (F k) q).natDegree = n k := by
  classical
  let ell : κ → (ι → ℂ) →ₗ[ℂ] ℂ := fun k =>
    (lcoeff ℂ (n k)).comp (polynomialLinearCombination (F k))
  have hell (k : κ) : ell k ≠ 0 := by
    obtain ⟨i, hi⟩ := hattained k
    intro hz
    have h := LinearMap.congr_fun hz (Pi.single i 1)
    change (polynomialLinearCombination (F k) (Pi.single i 1)).coeff (n k) = 0 at h
    rw [polynomialLinearCombination_single] at h
    exact hi h
  let W : Set (ι → ℂ) := U ∩ {q | ∀ k, ell k q ≠ 0}
  have hWopen : IsOpen W := by
    apply hU.inter
    have hset : {q : ι → ℂ | ∀ k, ell k q ≠ 0} = ⋂ k, {q | ell k q ≠ 0} := by
      ext q
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_ne_fun (continuous_coeff_polynomialLinearCombination (F k) (n k))
      continuous_const
  have hWne : W.Nonempty := by
    obtain ⟨q, hqU, hq⟩ := Analytic.exists_coefficients_avoiding_submodules_mem_open
      (fun k => LinearMap.ker (ell k))
      (fun k h => hell k (LinearMap.ker_eq_top.mp h)) U hU hUne
    exact ⟨q, hqU, hq⟩
  obtain ⟨q₀, hq₀W, hq₀squarefree⟩ :=
    exists_squarefree_linear_combinations_mem_open F hbase W hWopen hWne
  let V : Set (ι → ℂ) := U ∩
    {q | ∀ k, (polynomialLinearCombination (F k) q).coeff (n k) ≠ 0 ∧
      Squarefree (polynomialLinearCombination (F k) q)}
  have hVopen : IsOpen V := by
    apply hU.inter
    have hset : {q : ι → ℂ | ∀ k,
        (polynomialLinearCombination (F k) q).coeff (n k) ≠ 0 ∧
          Squarefree (polynomialLinearCombination (F k) q)} =
        ⋂ k, {q : ι → ℂ | (polynomialLinearCombination (F k) q).coeff (n k) ≠ 0 ∧
          Squarefree (polynomialLinearCombination (F k) q)} := by
      ext q
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_coeff_ne_zero_and_squarefree (polynomialLinearCombination (F k)) (n k)
      (natDegree_polynomialLinearCombination_le (F k) (n k) (hdegree k))
      (continuous_coeff_polynomialLinearCombination (F k))
  refine ⟨V, hVopen, ⟨q₀, hq₀W.1, fun k => ⟨hq₀W.2 k, hq₀squarefree k⟩⟩,
    fun _ h => h.1, ?_⟩
  intro q hq k
  exact ⟨(hq.2 k).2, le_antisymm
    (natDegree_polynomialLinearCombination_le (F k) (n k) (hdegree k) q)
    (le_natDegree_of_ne_zero (hq.2 k).1)⟩

/-- A finite nonzero polynomial family has an attained coefficient at
its maximal degree, also when that degree is zero. -/
theorem exists_attained_polynomial_family_degree
    {ι : Type*} [Finite ι] (F : ι → ℂ[X]) (hne : ∃ i, F i ≠ 0) :
    ∃ n : ℕ, (∀ i, (F i).natDegree ≤ n) ∧ ∃ i, (F i).coeff n ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i₀, hi₀⟩ := hne
  let n := Finset.univ.sup (fun i => (F i).natDegree)
  have hdegree (i : ι) : (F i).natDegree ≤ n :=
    Finset.le_sup (f := fun j => (F j).natDegree) (Finset.mem_univ i)
  refine ⟨n, hdegree, ?_⟩
  by_cases hn : n = 0
  · have hiLe := hdegree i₀
    have hiDegree : (F i₀).natDegree = n := by omega
    exact ⟨i₀, by rw [← hiDegree, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hi₀⟩
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
      (show (Finset.univ : Finset ι).Nonempty from ⟨i₀, Finset.mem_univ i₀⟩)
      (fun i => (F i).natDegree)
    change n = (F i).natDegree at hi
    have hFi : F i ≠ 0 := by
      intro hz
      exact hn (by simpa only [hz, natDegree_zero] using hi)
    exact ⟨i, by rw [hi, coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hFi⟩

/-- Finitely many polynomial families without common zeros have
simultaneously squarefree members throughout a nonempty open subset
of any supplied nonempty open coefficient set. -/
theorem exists_open_squarefree_linear_combinations
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → ℂ[X]) (hbase : ∀ k z, ∃ i, (F k i).eval z ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ k, Squarefree (polynomialLinearCombination (F k) q) := by
  have hne (k : κ) : ∃ i, F k i ≠ 0 := by
    obtain ⟨i, hi⟩ := hbase k 0
    exact ⟨i, fun hz => hi (by rw [hz, eval_zero])⟩
  choose n hdegree hattained using fun k =>
    exists_attained_polynomial_family_degree (F k) (hne k)
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    exists_open_squarefree_linear_combinations_of_degree_bounds
      F hbase n hdegree hattained U hU hUne
  exact ⟨V, hVopen, hVne, hVU, fun q hq k => (hV q hq k).1⟩

/-- Common factors and their zero sets are fixed independently of the
coefficient row. All residual members are squarefree on one nonempty
open coefficient set. -/
theorem exists_open_squarefree_residual_combinations
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → ℂ[X]) (hne : ∀ k, ∃ i, F k i ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (G : κ → ℂ[X]) (H : κ → ι → ℂ[X]) (V : Set (ι → ℂ)),
      IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      (∀ k, G k ≠ 0 ∧ (∀ i, F k i = G k * H k i) ∧
        (∀ z : ℂ, ∃ i, (H k i).eval z ≠ 0) ∧
        (∀ z : ℂ, (G k).eval z = 0 ↔ ∀ i, (F k i).eval z = 0)) ∧
      ∀ q ∈ V, ∀ k, Squarefree (polynomialLinearCombination (H k) q) := by
  classical
  choose G H hG hfactor hbase hzero using
    fun k => exists_common_factor_residual (F k) (hne k)
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    exists_open_squarefree_linear_combinations H hbase U hU hUne
  exact ⟨G, H, V, hVopen, hVne, hVU,
    fun k => ⟨hG k, hfactor k, hbase k, hzero k⟩, hV⟩

/-- Coprimality to a fixed nonzero polynomial is open in the coefficient
row. Only the finitely many roots of the fixed polynomial are relevant. -/
theorem isOpen_isCoprime_polynomialLinearCombination
    {ι : Type*} [Fintype ι] (P : ℂ[X]) (hP : P ≠ 0) (F : ι → ℂ[X]) :
    IsOpen {q : ι → ℂ | IsCoprime P (polynomialLinearCombination F q)} := by
  classical
  have hset : {q : ι → ℂ | IsCoprime P (polynomialLinearCombination F q)} =
      ⋂ z : P.roots.toFinset, {q | (polynomialLinearCombination F q).eval z.val ≠ 0} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id]
    constructor
    · intro h z
      exact (h z.val).resolve_left (not_not.mpr
        ((mem_roots hP).mp (Multiset.mem_toFinset.mp z.property)))
    · intro h z
      by_cases hz : P.eval z ≠ 0
      · exact Or.inl hz
      · exact Or.inr (h ⟨z, Multiset.mem_toFinset.mpr
          ((mem_roots hP).mpr (not_not.mp hz))⟩)
  rw [hset]
  apply isOpen_iInter_of_finite
  intro z
  have hcontinuous : Continuous (fun q : ι → ℂ =>
      (polynomialLinearCombination F q).eval z.val) := by
    change Continuous (fun q : ι → ℂ => (∑ i, q i • F i).eval z.val)
    simp only [eval_finsetSum, eval_smul, smul_eq_mul]
    fun_prop
  exact isOpen_ne_fun hcontinuous continuous_const

/-- Squarefreeness and avoidance of fixed polynomial roots hold
simultaneously on a nonempty open coefficient set. -/
theorem exists_open_squarefree_coprime_linear_combinations
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (P : κ → ℂ[X]) (hP : ∀ k, P k ≠ 0)
    (F : κ → ι → ℂ[X]) (hbase : ∀ k z, ∃ i, (F k i).eval z ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ q ∈ V, ∀ k, Squarefree (polynomialLinearCombination (F k) q) ∧
        IsCoprime (P k) (polynomialLinearCombination (F k) q) := by
  let W : Set (ι → ℂ) := U ∩
    {q | ∀ k, IsCoprime (P k) (polynomialLinearCombination (F k) q)}
  have hWopen : IsOpen W := by
    apply hU.inter
    have hset : {q : ι → ℂ | ∀ k, IsCoprime (P k) (polynomialLinearCombination (F k) q)} =
        ⋂ k, {q | IsCoprime (P k) (polynomialLinearCombination (F k) q)} := by
      ext q
      simp
    rw [hset]
    exact isOpen_iInter_of_finite
      (fun k => isOpen_isCoprime_polynomialLinearCombination (P k) (hP k) (F k))
  have hWne : W.Nonempty := by
    obtain ⟨q, hqU, hq⟩ := exists_coprime_linear_combinations_mem_open P hP F
      (fun k z _ => hbase k z) U hU hUne
    exact ⟨q, hqU, hq⟩
  obtain ⟨V, hVopen, hVne, hVW, hV⟩ :=
    exists_open_squarefree_linear_combinations F hbase W hWopen hWne
  exact ⟨V, hVopen, hVne, fun q hq => (hVW hq).1,
    fun q hq k => ⟨hV q hq k, (hVW hq).2 k⟩⟩

/-- The residual members are squarefree and avoid the common factor's
roots on one nonempty open coefficient set. The factors and their exact
zero sets are constructed independently of the coefficient row. -/
theorem exists_open_squarefree_coprime_residual_combinations
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → ℂ[X]) (hne : ∀ k, ∃ i, F k i ≠ 0)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (G : κ → ℂ[X]) (H : κ → ι → ℂ[X]) (V : Set (ι → ℂ)),
      IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      (∀ k, G k ≠ 0 ∧ (∀ i, F k i = G k * H k i) ∧
        (∀ z : ℂ, ∃ i, (H k i).eval z ≠ 0) ∧
        (∀ z : ℂ, (G k).eval z = 0 ↔ ∀ i, (F k i).eval z = 0)) ∧
      ∀ q ∈ V, ∀ k, Squarefree (polynomialLinearCombination (H k) q) ∧
        IsCoprime (G k) (polynomialLinearCombination (H k) q) := by
  classical
  choose G H hG hfactor hbase hzero using
    fun k => exists_common_factor_residual (F k) (hne k)
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    exists_open_squarefree_coprime_linear_combinations G hG H hbase U hU hUne
  exact ⟨G, H, V, hVopen, hVne, hVU,
    fun k => ⟨hG k, hfactor k, hbase k, hzero k⟩, hV⟩

end OnLeConjecture.Polynomial
