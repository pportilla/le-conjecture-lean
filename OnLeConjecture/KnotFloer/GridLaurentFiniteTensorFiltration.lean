/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensor

/-! # The finite tensor filtration and its product certificate -/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- Coordinatewise convolution, including a Laurent scalar so that the empty family
retains the graded and filtered Laurent unit. -/
def laurentFiniteBifiltrationLevel (A B : ℝ) :
    Submodule K (LaurentFiniteTensor (K := K) (n := n)) :=
  Submodule.span K {z | ∃ j : ℤ, ∃ a b : ι → ℝ, ∃ x : ∀ i, LaurentChain K (n i),
    (∀ i, x i ∈ laurentBifiltrationLevel (G i) K (a i) (b i)) ∧
      (∑ i, a i) - j ≤ A ∧ (∑ i, b i) - j ≤ B ∧
        z = (LaurentPolynomial.T j : LaurentPolynomial K) • tprod (LaurentPolynomial K) x}

/-- The finite tensor differential preserves each coordinate of the filtration. -/
theorem laurentFiniteDifferential_mem_bifiltrationLevel (A B : ℝ)
    {z : LaurentFiniteTensor (K := K) (n := n)}
    (hz : z ∈ laurentFiniteBifiltrationLevel G A B) :
    laurentFiniteDifferential G z ∈ laurentFiniteBifiltrationLevel G A B := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, a, b, x, hx, hA, hB, rfl⟩ := hz
    rw [map_smul, laurentFiniteDifferential_tprod, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    refine ⟨j, a, b, _, ?_, hA, hB, rfl⟩
    intro k
    by_cases h : k = i
    · subst k
      simpa using laurentDifferential_mem_bifiltrationLevel (G i) K (a i) (b i) (x i) (hx i)
    · simpa [h] using hx k
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz =>
    change ((laurentFiniteDifferential G).restrictScalars K) (a • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hz

/-- The weighted real filtration of the finite tensor module. -/
def laurentFiniteWeightedLevel (t s : ℝ) :
    Submodule K (LaurentFiniteTensor (K := K) (n := n)) :=
  Submodule.span K {z | ∃ A B : ℝ, z ∈ laurentFiniteBifiltrationLevel G A B ∧
    (1 - t / 2) * A + (t / 2) * B ≤ s}

omit [DecidableEq ι] in
/-- Finite Laurent products have the sum of the factor filtration bounds. -/
theorem laurentCoefficientLevel_prod (p : ι → LaurentPolynomial K) (a : ι → ℝ)
    (hp : ∀ i, p i ∈ laurentCoefficientLevel (K := K) (a i)) :
    ∏ i, p i ∈ laurentCoefficientLevel (K := K) (∑ i, a i) := by
  classical
  have h : ∀ s : Finset ι, ∏ i ∈ s, p i ∈ laurentCoefficientLevel (K := K) (∑ i ∈ s, a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      intro j hj
      have hj' : j = 0 := by simpa using hj
      simp [hj']
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact laurentCoefficientLevel_mul (hp i) ih
  exact h Finset.univ

/-- A Laurent scalar translates the output coefficient bound by minus its exponent. -/
theorem T_mul_mem_laurentCoefficientLevel (j : ℤ) {p : LaurentPolynomial K} {s : ℝ}
    (hp : p ∈ laurentCoefficientLevel (K := K) s) :
    LaurentPolynomial.T j * p ∈ laurentCoefficientLevel (K := K) (s - j) := by
  classical
  intro k hk
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp
    (AddMonoidAlgebra.support_coeff_single_mul_subset p (1 : K) j hk)
  have h := hp l hl
  push_cast
  linarith

omit [DecidableEq ι] in
/-- The finite product certificate lowers the weighted filtration by the sum of
its factor bounds. This includes the empty sum and empty Laurent product. -/
theorem laurentFinitePairing_mem_coefficientLevel
    (Λ : ∀ i, LaurentChain K (n i) →ₗ[LaurentPolynomial K] LaurentPolynomial K)
    (t : ℝ) (a : ι → ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (hΛ : ∀ i s x, x ∈ laurentWeightedLevel (G i) t s →
      Λ i x ∈ laurentCoefficientLevel (K := K) (s - a i))
    {s : ℝ} {z : LaurentFiniteTensor (K := K) (n := n)}
    (hz : z ∈ laurentFiniteWeightedLevel G t s) :
    laurentFinitePairing Λ z ∈ laurentCoefficientLevel (K := K) (s - ∑ i, a i) := by
  have hα : 0 ≤ 1 - t / 2 := by linarith
  have hβ : 0 ≤ t / 2 := by linarith
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A, B, hz, hs⟩ := hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, u, v, x, hx, hA, hB, rfl⟩ := hz
      rw [map_smul, laurentFinitePairing_tprod, smul_eq_mul]
      have hprod := laurentCoefficientLevel_prod (fun i => Λ i (x i))
        (fun i => (1 - t / 2) * u i + (t / 2) * v i - a i)
        (fun i => hΛ i _ _ (Submodule.subset_span ⟨u i, v i, hx i, le_rfl⟩))
      have hshift := T_mul_mem_laurentCoefficientLevel j hprod
      intro k hk
      have hk' := hshift k hk
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum] at hk'
      have hA' := mul_le_mul_of_nonneg_left hA hα
      have hB' := mul_le_mul_of_nonneg_left hB hβ
      nlinarith
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
    | smul r z _ hz =>
      change ((laurentFinitePairing Λ).restrictScalars K) (r • z) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ r hz
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul r z _ hz =>
    change ((laurentFinitePairing Λ).restrictScalars K) (r • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ r hz

end OnLeConjecture.KnotFloer.GridFull
