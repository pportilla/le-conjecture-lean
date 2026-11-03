/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchPositiveBraidIsotopy

/-! # The single permutation orbit of the branch event word

The endpoint label rotation determines the inverse cyclic conjugacy class
of the word permutation. Hence its permutation has one orbit and every
adjacent generator occurs. These are combinatorial consequences, without
an assertion of geometric grid realization.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open KnotTheory

theorem braid_permutation_eq_conjugate_inverse_rotation {a : ℕ}
    (before after p : Equiv.Perm (Fin a))
    (hword : before * p = after) (hcycle : after.trans (finRotate a) = before) :
    p = before⁻¹ * (finRotate a)⁻¹ * before := by
  have hc : finRotate a * after = before := by
    apply Equiv.ext
    intro k
    simpa only [Equiv.Perm.mul_apply, Equiv.trans_apply] using
      congrArg (fun e : Equiv.Perm (Fin a) => e k) hcycle
  calc
    p = before⁻¹ * (before * p) := by simp only [← mul_assoc, inv_mul_cancel, one_mul]
    _ = before⁻¹ * after := by rw [hword]
    _ = before⁻¹ * (finRotate a)⁻¹ * before := by
      rw [← hc]
      simp only [mul_assoc, inv_mul_cancel_left]

theorem braid_permutation_sameCycle_of_endpoint_rotation {a : ℕ} (ha : 0 < a)
    (before after p : Equiv.Perm (Fin a))
    (hword : before * p = after) (hcycle : after.trans (finRotate a) = before)
    (k l : Fin a) : p.SameCycle k l := by
  rw [braid_permutation_eq_conjugate_inverse_rotation before after p hword hcycle]
  have hconj := (Equiv.Perm.sameCycle_conj (f := (finRotate a)⁻¹)
    (g := before⁻¹) (x := k) (y := l))
  simp only [inv_inv] at hconj
  exact hconj.mpr (Equiv.Perm.sameCycle_inv.mpr
    (planeBranchBraidLabel_sameCycle ha (before k) (before l)))

theorem braid_word_cycleCount_eq_one_of_endpoint_rotation {a : ℕ} (ha : 0 < a)
    (before after : Equiv.Perm (Fin a)) (w : SignedAdjacentWord a)
    (hword : before * w.permutation = after)
    (hcycle : after.trans (finRotate a) = before) : w.cycleCount = 1 := by
  exact w.cycleCount_eq_one_of_sameCycle ha
    (braid_permutation_sameCycle_of_endpoint_rotation ha before after w.permutation hword hcycle)

/-- The single orbit forces each adjacent cut to be crossed by a letter. -/
theorem braid_word_generatorIndices_eq_univ_of_endpoint_rotation {a : ℕ} (ha : 0 < a)
    (before after : Equiv.Perm (Fin a)) (w : SignedAdjacentWord a)
    (hword : before * w.permutation = after)
    (hcycle : after.trans (finRotate a) = before) : w.generatorIndices = Finset.univ := by
  have hcount := braid_word_cycleCount_eq_one_of_endpoint_rotation ha before after w hword hcycle
  have hle := w.strandCount_le_cycleCount_add_generatorCount
  rw [hcount] at hle
  have hupper : w.generatorIndices.card ≤ a - 1 := by
    simpa only [Fintype.card_fin] using w.generatorIndices.card_le_univ
  apply Finset.eq_univ_of_card
  simp only [Fintype.card_fin]
  omega

end OnLeConjecture.Analytic
