/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.Order

/-!
# Weighted antidiagonal sums

Pairs of natural numbers are reindexed by the weighted degree `q * m + j`.
This reindexing allows an absolutely convergent double series to be grouped
into its finite weighted antidiagonals.
-/

public section

namespace OnLeConjecture.Analytic

/-- The pair `(m, j)` corresponds to the point indexed by `m` on the weighted
antidiagonal of degree `q * m + j`. -/
def weightedAntidiagonalEquiv (q : ℕ) (hq : 0 < q) :
    (Σ d : ℕ, Fin (d / q + 1)) ≃ ℕ × ℕ where
  toFun z := (z.2.1, z.1 - q * z.2.1)
  invFun z :=
    ⟨q * z.1 + z.2,
      ⟨z.1, by
        rw [Nat.lt_add_one_iff]
        apply (Nat.le_div_iff_mul_le hq).2
        rw [Nat.mul_comm z.1 q]
        exact Nat.le_add_right (q * z.1) z.2⟩⟩
  left_inv z := by
    rcases z with ⟨d, m⟩
    have hm : m.1 ≤ d / q := by omega
    have hqm : q * m.1 ≤ d := by
      have hm' := (Nat.le_div_iff_mul_le hq).1 hm
      rw [Nat.mul_comm] at hm'
      exact hm'
    have hd : q * m.1 + (d - q * m.1) = d := by omega
    apply Sigma.ext hd
    have hsize :
        (q * m.1 + (d - q * m.1)) / q + 1 = d / q + 1 :=
      congrArg (fun n : ℕ ↦ n / q + 1) hd
    apply (Fin.heq_ext_iff hsize).mpr
    rfl
  right_inv z := by
    rcases z with ⟨m, j⟩
    apply Prod.ext
    · rfl
    · simp

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
  [ContinuousAdd E] [RegularSpace E]

/-- A convergent double series has the same sum after grouping its terms by
weighted degree. -/
theorem hasSum_weightedAntidiagonal (q : ℕ) (hq : 0 < q)
    (f : ℕ → ℕ → E) (s : E)
    (hf : HasSum (fun z : ℕ × ℕ ↦ f z.1 z.2) s) :
    HasSum (fun d : ℕ ↦
      ∑ m : Fin (d / q + 1), f m.1 (d - q * m.1)) s := by
  have hsigma : HasSum (fun z : Σ d : ℕ, Fin (d / q + 1) ↦
      f z.2.1 (z.1 - q * z.2.1)) s :=
    (weightedAntidiagonalEquiv q hq).hasSum_iff.mpr hf
  apply hsigma.sigma
  intro d
  exact hasSum_fintype _

/-- Absolute convergence is preserved by grouping terms into finite weighted
antidiagonals. -/
theorem summable_weightedAntidiagonal (q : ℕ) (hq : 0 < q)
    (f : ℕ → ℕ → E)
    (hf : Summable (fun z : ℕ × ℕ ↦ f z.1 z.2)) :
    Summable (fun d : ℕ ↦
      ∑ m : Fin (d / q + 1), f m.1 (d - q * m.1)) :=
  (hasSum_weightedAntidiagonal q hq f _ hf.hasSum).summable

/-- The sum of a convergent double series equals the sum of its finite
weighted antidiagonals. -/
theorem tsum_weightedAntidiagonal (q : ℕ) (hq : 0 < q)
    [T2Space E]
    (f : ℕ → ℕ → E)
    (hf : Summable (fun z : ℕ × ℕ ↦ f z.1 z.2)) :
    ∑' d : ℕ, (∑ m : Fin (d / q + 1), f m.1 (d - q * m.1)) =
      ∑' z : ℕ × ℕ, f z.1 z.2 :=
  (hasSum_weightedAntidiagonal q hq f _ hf.hasSum).tsum_eq

end OnLeConjecture.Analytic
