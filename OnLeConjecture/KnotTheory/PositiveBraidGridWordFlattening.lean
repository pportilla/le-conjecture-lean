/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridLetterSchedule

/-! # Exact path identities for concatenated positive words

The equalities retain the literal generator paths and prefix labels. They are
identities of complex-valued functions, not inferences from permutations.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff

namespace OnLeConjecture.KnotTheory

theorem positiveGridWord_at_cut {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin m) (j : ℕ) (hj : j ≤ w.length) :
    positiveGridWord w k (j : ℝ) = (((positiveWordPrefix w j).symm k).val : ℂ) := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · rw [positiveGridWord_stage w j hj k ⟨le_rfl, by linarith⟩, sub_self]
    exact (positiveGridGenerator_endpoints _ _).1 0 le_rfl
  · rw [positiveGridWord_of_length_le w k le_rfl, positiveWordPrefix_length]

/-- The first literal subword is unchanged up to and including its endpoint. -/
theorem positiveGridWord_append_left {m : ℕ} (u v : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ≤ u.length) :
    positiveGridWord (u ++ v) k t = positiveGridWord u k t := by
  by_cases ht0 : t ≤ 0
  · rw [positiveGridWord_of_nonpos _ k ht0, positiveGridWord_of_nonpos _ k ht0]
  rcases lt_or_eq_of_le ht with ht | rfl
  · let j := Nat.floor t
    have hj : j < u.length := (Nat.floor_lt (le_of_not_ge ht0)).mpr ht
    have hj' : j < (u ++ v).length := by simp only [List.length_append]; omega
    have htj : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) :=
      ⟨Nat.floor_le (le_of_not_ge ht0), (Nat.lt_floor_add_one t).le⟩
    rw [positiveGridWord_stage _ j hj' k htj, positiveGridWord_stage _ j hj k htj,
      List.getElem_append_left hj, positiveWordPrefix_append_left u v hj.le]
  · rw [positiveGridWord_at_cut (u ++ v) k u.length (by simp),
      positiveGridWord_at_cut u k u.length le_rfl, positiveWordPrefix_append_left u v le_rfl]

/-- The second literal subword starts with precisely the inverse-prefix relabelling. -/
theorem positiveGridWord_append_right {m : ℕ} (u v : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : (u.length : ℝ) ≤ t) :
    positiveGridWord (u ++ v) k t =
      positiveGridWord v (u.permutation.symm k) (t - u.length) := by
  by_cases ht1 : ((u ++ v).length : ℝ) ≤ t
  · have ht' : (v.length : ℝ) ≤ t - u.length := by
      have hh := ht1
      simp only [List.length_append, Nat.cast_add] at hh
      linarith
    rw [positiveGridWord_of_length_le _ k ht1, positiveGridWord_of_length_le v _ ht']
    have happ : (u ++ v).permutation = u.permutation * v.permutation :=
      PositiveAdjacentWord.permutation_append u v
    rw [happ]
    rfl
  · have hnonneg : 0 ≤ t - (u.length : ℝ) := sub_nonneg.mpr ht
    have hlt : t - (u.length : ℝ) < v.length := by
      have hh := lt_of_not_ge ht1
      simp only [List.length_append, Nat.cast_add] at hh
      linarith
    let j := Nat.floor (t - (u.length : ℝ))
    have hj : j < v.length := (Nat.floor_lt hnonneg).mpr hlt
    have hj' : u.length + j < (u ++ v).length := by simp only [List.length_append]; omega
    have htj : t - (u.length : ℝ) ∈ Icc (j : ℝ) ((j : ℝ) + 1) :=
      ⟨Nat.floor_le hnonneg, (Nat.lt_floor_add_one _).le⟩
    have htj' : t ∈ Icc ((u.length + j : ℕ) : ℝ) (((u.length + j : ℕ) : ℝ) + 1) := by
      simp only [Nat.cast_add]
      constructor <;> linarith [htj.1, htj.2]
    have hletter : (u ++ v)[u.length + j] = v[j] := by
      simpa only [Nat.add_comm] using (List.getElem_append_right' u hj).symm
    rw [positiveGridWord_stage _ (u.length + j) hj' k htj',
      positiveGridWord_stage _ j hj _ htj,
      hletter, positiveWordPrefix_append_offset]
    have hlabel : (u.permutation * positiveWordPrefix v j).symm k =
        (positiveWordPrefix v j).symm (u.permutation.symm k) := rfl
    rw [hlabel, Nat.cast_add]
    congr 1
    ring

/-- A subword in a larger literal word is traversed with the exact accumulated prefix. -/
theorem positiveGridWord_append_context {m : ℕ} (u v z : PositiveAdjacentWord m)
    (k : Fin m) {t : ℝ} (ht : t ∈ Icc (u.length : ℝ) (u.length + v.length : ℝ)) :
    positiveGridWord ((u ++ v) ++ z) k t =
      positiveGridWord v (u.permutation.symm k) (t - u.length) := by
  rw [positiveGridWord_append_left (u ++ v) z k
    (by simpa only [List.length_append, Nat.cast_add] using ht.2)]
  exact positiveGridWord_append_right u v k ht.1

/-- The exact flattened-list decomposition around one chosen subword. -/
theorem positiveWord_flatten_decomposition {m : ℕ} (W : List (PositiveAdjacentWord m))
    (j : Fin W.length) :
    W.flatten = ((W.take j.val).flatten ++ W[j.val]) ++ (W.drop (j.val + 1)).flatten := by
  conv_lhs => rw [← List.take_append_drop (j.val + 1) W]
  rw [List.take_succ_eq_append_getElem j.isLt, List.flatten_append, List.flatten_append]
  simp

/-- Flattening retains the literal path on every subword interval, including both cuts. -/
theorem positiveGridWord_flatten_subword {m : ℕ} (W : List (PositiveAdjacentWord m))
    (j : Fin W.length) (k : Fin m) {t : ℝ}
    (ht : t ∈ Icc (((W.take j.val).flatten.length : ℕ) : ℝ)
      (((W.take j.val).flatten.length : ℝ) + (W[j.val].length : ℝ))) :
    positiveGridWord W.flatten k t =
      positiveGridWord W[j.val] ((PositiveAdjacentWord.permutation (W.take j.val).flatten).symm k)
        (t - (W.take j.val).flatten.length) := by
  rw [positiveWord_flatten_decomposition W j]
  exact positiveGridWord_append_context _ _ _ k ht

/-- Prefix labels inside a flattened subword are the product of the preceding
subwords' permutation and the local prefix permutation. -/
theorem positiveWordPrefix_flatten_subword {m : ℕ} (W : List (PositiveAdjacentWord m))
    (j : Fin W.length) {h : ℕ} (hh : h ≤ W[j.val].length) :
    positiveWordPrefix W.flatten ((W.take j.val).flatten.length + h) =
      PositiveAdjacentWord.permutation (W.take j.val).flatten * positiveWordPrefix W[j.val] h := by
  rw [positiveWord_flatten_decomposition W j,
    positiveWordPrefix_append_left _ _ (by simp only [List.length_append]; omega),
    positiveWordPrefix_append_offset]

/-- The sorted configurations determine every prefix of the flattened event word. -/
theorem positiveWord_flatten_take_permutation {m N : ℕ}
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (j : ℕ) (hj : j ≤ N) :
    σ 0 * PositiveAdjacentWord.permutation ((List.ofFn w).take j).flatten = σ ⟨j, by omega⟩ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjN : j < N := by omega
    have hjW : j < (List.ofFn w).length := by simpa only [List.length_ofFn] using hjN
    rw [List.take_succ_eq_append_getElem hjW, List.flatten_append, List.flatten_singleton]
    have happ : PositiveAdjacentWord.permutation (((List.ofFn w).take j).flatten ++
        (List.ofFn w)[j]) = PositiveAdjacentWord.permutation ((List.ofFn w).take j).flatten *
          PositiveAdjacentWord.permutation (List.ofFn w)[j] :=
      PositiveAdjacentWord.permutation_append _ _
    rw [happ, ← mul_assoc, ih (by omega)]
    have hget : (List.ofFn w)[j] = w ⟨j, hjN⟩ := by simp
    rw [hget]
    exact hp ⟨j, hjN⟩

/-- The inverse accumulated prefix transports initial sheet ranks to the exact
sorting permutation at the selected event. -/
theorem positiveWord_flatten_take_label {m N : ℕ}
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (j : Fin (N + 1)) (k : Fin m) :
    (PositiveAdjacentWord.permutation ((List.ofFn w).take j.val).flatten).symm
      ((σ 0).symm k) = (σ j).symm k := by
  have h := positiveWord_flatten_take_permutation σ w hp j.val (Nat.le_of_lt_succ j.isLt)
  have h' : σ 0 * PositiveAdjacentWord.permutation ((List.ofFn w).take j.val).flatten = σ j := h
  apply (σ j).injective
  rw [Equiv.apply_symm_apply, ← h']
  simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply]

/-- On the active time interval of any retained event, the flattened canonical
word is exactly its original subword with the original sheet labels. -/
theorem positiveGridWord_ofFn_subword {m N : ℕ}
    (σ : Fin (N + 1) → Equiv.Perm (Fin m)) (w : Fin N → PositiveAdjacentWord m)
    (hp : ∀ j, σ j.castSucc * (w j).permutation = σ j.succ)
    (j : Fin N) (k : Fin m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ((w j).length : ℝ)) :
    positiveGridWord (List.ofFn w).flatten ((σ 0).symm k)
      (((List.ofFn w).take j.val).flatten.length + t) =
        positiveGridWord (w j) ((σ j.castSucc).symm k) t := by
  let j' : Fin (List.ofFn w).length := ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩
  have hget : (List.ofFn w)[j'.val] = w j := by simp [j']
  have h := positiveGridWord_flatten_subword (List.ofFn w) j' ((σ 0).symm k)
    (t := (((List.ofFn w).take j.val).flatten.length : ℝ) + t)
    (by rw [hget]; constructor <;> linarith [ht.1, ht.2])
  have hlabel := positiveWord_flatten_take_label σ w hp j.castSucc k
  have hlabel' : (PositiveAdjacentWord.permutation ((List.ofFn w).take j.val).flatten).symm
      ((σ 0).symm k) = (σ j.castSucc).symm k := hlabel
  simp only [j', hget, add_sub_cancel_left] at h
  rw [hlabel'] at h
  exact h

end OnLeConjecture.KnotTheory
