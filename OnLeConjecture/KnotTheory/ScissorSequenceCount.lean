/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ScissorSequenceOrbits
public import OnLeConjecture.KnotTheory.ExteriorHurwitzWords
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# Factor permutations and the auxiliary count of the scissors

This file records the facts about the factor permutations of a `NormalizedFactorization` used by
the forest of Section 9 of the written proof of Statement E (`statement_E_complete_proof.tex`,
subsection "The explicit forest for O-switch selection").

Every factor permutation is a cycle (`isCycle_factor_permutation`); with strand `0` in every
factor cycle, every strand moved by a factor lies in the cycle of `0` (`sameCycle_factor_zero`).
The cycle of the factor `l` has `a_l` elements, where `a_l` is the number of strands of the local
word for a singular factor and `2` for a simple factor (`card_support_factor_permutation`).
Transitivity gives a factor moving any strand (`exists_factor_moves`).

The number `U` of pairs `(l, y)` with `y` fixed by the factor `l` is the number of auxiliary
components of the scissor endpoint; it satisfies `U = Σ_l (S - a_l)` (`auxCount_eq`), and
`(S - 1)(r - 1) - U` is the shift count `F.scissorShiftCount` (`scissorShiftCount_eq`). All
results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.NormalizedFactorization

open Equiv Equiv.Perm SignedAdjacentWord

variable {S N B : ℕ} (F : NormalizedFactorization S N B)

/-- The number of strands of the nontrivial cycle of a factor. -/
def cycleLength (l : Fin (N + B)) : ℕ := if h : l.val < N then F.strands ⟨l.val, h⟩ else 2

theorem isCycle_core_permutation (hS : 2 ≤ S) (l : Fin (N + B)) :
    (F.core l).permutation.IsCycle := by
  unfold core
  split_ifs with h
  · exact isCycle_permutation_liftPositiveWord _ (F.two_le_strands _) _ (F.word_cycleCount _)
  · exact isCycle_permutation_firstLetter hS

theorem factor_permutation_eq (l : Fin (N + B)) :
    (F.factor l).permutation = (padWord S ++ F.conjugator l).permutation *
      (F.core l).permutation * (padWord S ++ F.conjugator l).permutation⁻¹ := by
  rw [factor, permutation_conjugateWord]

theorem isCycle_factor_permutation (hS : 2 ≤ S) (l : Fin (N + B)) :
    (F.factor l).permutation.IsCycle := by
  rw [factor_permutation_eq]
  exact (F.isCycle_core_permutation hS l).conj

/-- With strand `0` in every factor cycle, every strand moved by a factor lies in the cycle of
`0`. -/
theorem sameCycle_factor_zero (hS : 2 ≤ S) (hzero : F.StrandZeroInEveryFactor (by omega))
    (l : Fin (N + B)) (y : Fin S) (hy : (F.factor l).permutation y ≠ y) :
    (F.factor l).permutation.SameCycle y ⟨0, by omega⟩ :=
  (F.isCycle_factor_permutation hS l).sameCycle hy (hzero l)

/-- A positive word on `a ≥ 2` strands with one cycle has no fixed strand. -/
theorem permutation_ne_of_cycleCount {a : ℕ} (ha : 2 ≤ a) (w : PositiveAdjacentWord a)
    (hw : w.toSigned.cycleCount = 1) (x : Fin a) : w.toSigned.permutation x ≠ x := by
  classical
  set σ := w.toSigned.permutation with hσ
  have hsub : Subsingleton (Quotient (Perm.SameCycle.setoid σ)) := by
    rw [← Fintype.card_le_one_iff_subsingleton]
    have : SignedAdjacentWord.cycleCount w.toSigned = 1 := hw
    unfold SignedAdjacentWord.cycleCount at this
    rw [← hσ] at this
    convert this.le
  intro hx
  obtain ⟨y, hy⟩ : ∃ y : Fin a, y ≠ x :=
    ⟨if x.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
      split_ifs with h <;> intro e <;> rw [Fin.ext_iff] at e <;> simp at e <;> omega⟩
  have hxy : σ.SameCycle x y :=
    Quotient.exact (Subsingleton.elim (Quotient.mk (Perm.SameCycle.setoid σ) x) ⟦y⟧)
  obtain ⟨k, hk⟩ := hxy
  rw [zpow_apply_eq_self_of_apply_eq_self hx] at hk
  exact hy hk.symm

theorem card_support_core_permutation (hS : 2 ≤ S) (l : Fin (N + B)) :
    (F.core l).permutation.support.card = F.cycleLength l := by
  classical
  unfold core cycleLength
  split_ifs with h
  · set a := F.strands ⟨l.val, h⟩
    have hle : a ≤ S := F.strands_le _
    have hsupp : (liftPositiveWord hle (F.word ⟨l.val, h⟩)).permutation.support =
        Finset.univ.map (Fin.castLEEmb hle) := by
      ext y
      rw [Perm.mem_support, Finset.mem_map]
      constructor
      · intro hy
        by_contra hno
        push Not at hno
        apply hy
        apply liftPositiveWord_permutation_of_le
        by_contra hya
        exact hno ⟨y.val, by omega⟩ (Finset.mem_univ _) (Fin.ext rfl)
      · rintro ⟨x, -, rfl⟩
        rw [Fin.castLEEmb_apply, liftPositiveWord_permutation_castLE]
        intro e
        exact permutation_ne_of_cycleCount (F.two_le_strands _) _ (F.word_cycleCount _) x
          (Fin.castLE_injective hle e)
    rw [hsupp, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · rw [firstLetter, dif_pos hS, permutation_cons, permutation_nil, mul_one]
    unfold adjacentSwap
    exact card_support_swap (by simp [Fin.ext_iff])

theorem card_support_factor_permutation (hS : 2 ≤ S) (l : Fin (N + B)) :
    (F.factor l).permutation.support.card = F.cycleLength l := by
  rw [factor_permutation_eq, card_support_conj, F.card_support_core_permutation hS l]

theorem cycleLength_le (hS : 2 ≤ S) (l : Fin (N + B)) : F.cycleLength l ≤ S := by
  unfold cycleLength
  split_ifs
  · exact F.strands_le _
  · exact hS

/-- The number of strands fixed by a factor. -/
theorem card_fixed_factor (hS : 2 ≤ S) (l : Fin (N + B)) :
    (Finset.univ.filter fun y => (F.factor l).permutation y = y).card = S - F.cycleLength l := by
  classical
  have e : (Finset.univ.filter fun y => (F.factor l).permutation y = y) =
      (F.factor l).permutation.supportᶜ := by
    ext y; simp [Perm.mem_support]
  rw [e, Finset.card_compl, Fintype.card_fin, card_support_factor_permutation F hS l]

/-- The factor permutations. -/
def factorPerm (l : Fin (N + B)) : Perm (Fin S) := (F.factor l).permutation

/-- The number of auxiliary components: pairs `(l, y)` with `y` fixed by the factor `l`. -/
def auxCount : ℕ := Nat.card {a : Fin (N + B) × Fin S // ¬ MergeMoved F.factorPerm a}

theorem auxCount_eq (hS : 2 ≤ S) : F.auxCount = ∑ l, (S - F.cycleLength l) := by
  classical
  rw [auxCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← F.card_fixed_factor hS l, Finset.card_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [MergeMoved, factorPerm]

/-- **Transitivity gives a moving factor.** -/
theorem exists_factor_moves (hS : 2 ≤ S) (htrans : F.Transitive) (x : Fin S) :
    ∃ l, F.factorPerm l x ≠ x := by
  by_contra hno
  push Not at hno
  obtain ⟨y, hy⟩ : ∃ y : Fin S, y ≠ x :=
    ⟨if x.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩, by
      split_ifs with h <;> intro e <;> rw [Fin.ext_iff] at e <;> simp at e <;> omega⟩
  obtain ⟨σ, hσ, hσx⟩ := htrans x y
  have hle : Subgroup.closure (Set.range fun l => (F.factor l).permutation) ≤
      MulAction.stabilizer (Perm (Fin S)) x := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Perm.smul_def]
    exact hno l
  have := hle hσ
  rw [MulAction.mem_stabilizer_iff, Perm.smul_def] at this
  exact hy (hσx.symm.trans this)

/-- **The shift count.** The number `(S - 1)(r - 1)` of scissors minus the number of auxiliary
components is `F.scissorShiftCount`. -/
theorem scissorShiftCount_eq (hS : 2 ≤ S) :
    ((S : ℤ) - 1) * ((N : ℤ) + B - 1) - (F.auxCount : ℤ) = F.scissorShiftCount := by
  rw [F.auxCount_eq hS, Nat.cast_sum, Fin.sum_univ_add]
  have h1 : ∀ i : Fin N, ((S - F.cycleLength (Fin.castAdd B i) : ℕ) : ℤ) =
      (S : ℤ) - F.strands i := by
    intro i
    have : F.cycleLength (Fin.castAdd B i) = F.strands i := by
      simp [cycleLength]
    rw [this, Nat.cast_sub (F.strands_le i)]
  have h2 : ∀ j : Fin B, ((S - F.cycleLength (Fin.natAdd N j) : ℕ) : ℤ) = (S : ℤ) - 2 := by
    intro j
    have : F.cycleLength (Fin.natAdd N j) = 2 := by
      simp [cycleLength]
    rw [this, Nat.cast_sub hS]
    norm_num
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, scissorShiftCount]
  ring

end OnLeConjecture.KnotTheory.NormalizedFactorization
