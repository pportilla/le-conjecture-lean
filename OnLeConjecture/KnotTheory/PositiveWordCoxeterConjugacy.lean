/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordBraidEquiv

/-! # Centrality of the full twist and conjugacy of Coxeter words

This module proves the word statements of job J08 of the dependency audit (record M408). Write
`c = coxeterWord m` and `Δ² = fullTwistWord m = c ^ m`.

* `fullTwist_central_braidEquiv`: for every generator `i`, the words `u ++ i :: (Δ² ++ v)` and
  `u ++ Δ² ++ i :: v` are positive braid equivalent. The proof uses only far commutations and
  positive braid relations inside words. `fullTwist_central` is the corresponding statement for
  `PositiveWordConj`.
* `fullTwist_coxeter_conj`: if `2 ≤ m`, then every permutation `γ` of the Coxeter word satisfies
  `PositiveWordConj (Δ² ++ γ) (Δ² ++ c)`. The hypothesis `2 ≤ m` is necessary. For `m ≤ 1` every
  word is empty, and `PositiveWordConj [] []` is false (`fullTwist_coxeter_conj_iff`).

The written derivation is `docs/route-n/J08-coxeter-conjugacy.tex`. The centrality follows from
the relations `c σᵢ ≡ σᵢ₊₁ c` for `i + 1 < m - 1` and `c² σ_{m-2} ≡ σ₀ c²`. The conjugacy of
Coxeter words is first proved for far commutations and cyclic rotations of the Coxeter words
themselves (`farRotationEquiv_coxeterWord`), by induction on the number of letters. It is then
transferred to `PositiveWordConj`, where a rotated letter passes through `Δ²` by centrality.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory

/-! ### Initial and final segments of the Coxeter word -/

/-- Every letter among the first `k` letters `0, 1, …, k - 1` is smaller than `k`. -/
theorem mem_take_finRange {N k : ℕ} {x : Fin N} (hx : x ∈ (List.finRange N).take k) :
    x.val < k := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simp only [List.length_take, List.length_finRange] at hj
  simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast]
  omega

/-- Every letter after the first `k` letters is at least `k`. -/
theorem mem_drop_finRange {N k : ℕ} {x : Fin N} (hx : x ∈ (List.finRange N).drop k) :
    k ≤ x.val := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simp only [List.getElem_drop, List.getElem_finRange, Fin.val_cast]
  omega

/-- The letters of `0 1 ⋯ (N - 1)` from position `k < N` on start with the letter `k`. -/
theorem drop_finRange_eq_cons {N k : ℕ} (hk : k < N) :
    (List.finRange N).drop k = ⟨k, hk⟩ :: (List.finRange N).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hk)]
  congr 1
  exact Fin.ext (by simp)

/-- The first `k + 1` letters of `0 1 ⋯ (N - 1)` are the first `k` letters followed by `k`. -/
theorem take_finRange_succ {N k : ℕ} (hk : k < N) :
    (List.finRange N).take (k + 1) = (List.finRange N).take k ++ [⟨k, hk⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hk)]
  congr 1
  simp

/-- The letter `i + 1` when `i + 1 < m - 1`, and the letter `i` otherwise. Only the first case
occurs in the statements below. -/
def shiftLetter {m : ℕ} (i : Fin (m - 1)) : Fin (m - 1) :=
  if h : i.val + 1 < m - 1 then ⟨i.val + 1, h⟩ else i

/-- The value of `shiftLetter i` is `i + 1` when `i + 1 < m - 1`. -/
theorem shiftLetter_val {m : ℕ} {i : Fin (m - 1)} (h : i.val + 1 < m - 1) :
    (shiftLetter i).val = i.val + 1 := by
  simp [shiftLetter, h]

/-! ### Shifting letters through powers of the Coxeter word -/

/-- If `j = i + 1`, the Coxeter word followed by the letter `i` is positive braid equivalent to
the letter `j` followed by the Coxeter word, that is, `c σᵢ ≡ σᵢ₊₁ c`. -/
theorem coxeterWord_append_singleton {m : ℕ} (i j : Fin (m - 1)) (h : j.val = i.val + 1) :
    PositiveBraidEquiv (coxeterWord m ++ [i]) (j :: coxeterWord m) := by
  have hj := j.isLt
  have hc : coxeterWord m = (List.finRange (m - 1)).take i.val ++
      i :: j :: (List.finRange (m - 1)).drop (i.val + 1 + 1) := by
    have e : (⟨i.val + 1, by omega⟩ : Fin (m - 1)) = j := Fin.ext h.symm
    rw [coxeterWord]
    conv_lhs => rw [← List.take_append_drop i.val (List.finRange (m - 1))]
    rw [drop_finRange_eq_cons i.isLt, drop_finRange_eq_cons (k := i.val + 1) (by omega), Fin.eta,
      e]
  have hB : ∀ y ∈ (List.finRange (m - 1)).drop (i.val + 1 + 1),
      y.val + 2 ≤ i.val ∨ i.val + 2 ≤ y.val :=
    fun y hy => Or.inr (by have := mem_drop_finRange hy; omega)
  have hA : ∀ y ∈ (List.finRange (m - 1)).take i.val,
      y.val + 2 ≤ j.val ∨ j.val + 2 ≤ y.val :=
    fun y hy => Or.inl (by have := mem_take_finRange hy; omega)
  rw [hc]
  generalize (List.finRange (m - 1)).take i.val = A at hA ⊢
  generalize (List.finRange (m - 1)).drop (i.val + 1 + 1) = B at hB ⊢
  have h₁ : PositiveBraidEquiv (A ++ i :: j :: B ++ [i]) (A ++ [i, j, i] ++ B) := by
    have := (PositiveBraidEquiv.append_singleton_of_far B i hB).append_left (A ++ [i, j])
    simpa using this
  have h₂ : PositiveBraidEquiv (A ++ [i, j, i] ++ B) (A ++ [j, i, j] ++ B) :=
    PositiveBraidEquiv.braid A B i j h
  have h₃ : PositiveBraidEquiv (A ++ [j, i, j] ++ B) (j :: (A ++ i :: j :: B)) := by
    have := (PositiveBraidEquiv.append_singleton_of_far A j hA).append_right (i :: j :: B)
    simpa using this
  exact h₁.trans (h₂.trans h₃)

/-- For a word `w` whose letters are at most `m - 3`, the word `c w` is positive braid
equivalent to `w⁺ c`, where `w⁺ = w.map shiftLetter` adds one to every letter. -/
theorem coxeterWord_append_shift {m : ℕ} (w : PositiveAdjacentWord m)
    (hw : ∀ x ∈ w, x.val + 1 < m - 1) :
    PositiveBraidEquiv (coxeterWord m ++ w) (w.map shiftLetter ++ coxeterWord m) := by
  induction w with
  | nil => exact PositiveBraidEquiv.of_eq (by simp)
  | cons x w ih =>
    have hx := hw x List.mem_cons_self
    have h₁ : PositiveBraidEquiv (coxeterWord m ++ x :: w)
        (shiftLetter x :: (coxeterWord m ++ w)) := by
      have := (coxeterWord_append_singleton x (shiftLetter x) (shiftLetter_val hx)).append_right w
      simpa using this
    have h₂ := (ih fun y hy => hw y (List.mem_cons_of_mem x hy)).cons (shiftLetter x)
    simpa using h₁.trans h₂

/-- The word `c ^ (a + b)` is the concatenation of `c ^ a` and `c ^ b`. -/
theorem torusWord_add (m a b : ℕ) : torusWord m (a + b) = torusWord m a ++ torusWord m b := by
  simp only [torusWord, List.replicate_add, List.flatten_append]

/-- The word `c ^ 2` is `c c`. -/
theorem torusWord_two (m : ℕ) : torusWord m 2 = coxeterWord m ++ coxeterWord m := by
  simp [torusWord, List.replicate_succ]

/-- If `j = i + k`, the word `c ^ k` followed by the letter `i` is positive braid equivalent
to the letter `j` followed by `c ^ k`, that is, `c ^ k σᵢ ≡ σᵢ₊ₖ c ^ k`. -/
theorem torusWord_append_singleton {m : ℕ} (k : ℕ) (i j : Fin (m - 1)) (h : j.val = i.val + k) :
    PositiveBraidEquiv (torusWord m k ++ [i]) (j :: torusWord m k) := by
  induction k generalizing i with
  | zero =>
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    exact PositiveBraidEquiv.of_eq (by simp [torusWord])
  | succ k ih =>
    have hi : i.val + 1 < m - 1 := by have := j.isLt; omega
    let i' : Fin (m - 1) := ⟨i.val + 1, hi⟩
    have h₁ : PositiveBraidEquiv (torusWord m k ++ coxeterWord m ++ [i])
        (torusWord m k ++ [i'] ++ coxeterWord m) := by
      have := (coxeterWord_append_singleton i i' rfl).append_left (torusWord m k)
      simpa using this
    have h₂ := (ih i' (by simp [i']; omega)).append_right (coxeterWord m)
    rw [torusWord_succ]
    exact h₁.trans h₂

/-- If `i = 0` and `j = m - 2` is the last letter, the word `c c j` is positive braid
equivalent to `i c c`, that is, `c² σ_{m-2} ≡ σ₀ c²`. -/
theorem coxeterWord_wrap {m : ℕ} (i j : Fin (m - 1)) (hi : i.val = 0) (hj : j.val + 1 = m - 1) :
    PositiveBraidEquiv (coxeterWord m ++ coxeterWord m ++ [j])
      (i :: (coxeterWord m ++ coxeterWord m)) := by
  have hsnoc : coxeterWord m = (List.finRange (m - 1)).take j.val ++ [j] := by
    have h₁ : (List.finRange (m - 1)).take (j.val + 1) = List.finRange (m - 1) :=
      List.take_of_length_le (by simp [hj])
    rw [coxeterWord]
    conv_lhs => rw [← h₁]
    rw [take_finRange_succ j.isLt, Fin.eta]
  have hcons : coxeterWord m = i :: ((List.finRange (m - 1)).take j.val).map shiftLetter := by
    rw [coxeterWord]
    conv_lhs => rw [← List.drop_zero (l := List.finRange (m - 1))]
    rw [drop_finRange_eq_cons (k := 0) (by omega)]
    refine congrArg₂ List.cons (Fin.ext hi.symm) ?_
    apply List.ext_getElem
    · simp
      omega
    · intro n h₁ h₂
      have hn : n < j.val := by
        simp at h₂
        omega
      apply Fin.ext
      rw [List.getElem_map, shiftLetter_val]
      · simp
      · simp
        omega
  have hC : ∀ x ∈ (List.finRange (m - 1)).take j.val, x.val + 1 < m - 1 := fun x hx => by
    have := mem_take_finRange hx
    omega
  have hshift := ((coxeterWord_append_shift _ hC).append_right [j]).cons i
  calc coxeterWord m ++ coxeterWord m ++ [j]
      = i :: (((List.finRange (m - 1)).take j.val).map shiftLetter ++ coxeterWord m ++ [j]) := by
        nth_rw 1 [hcons]
        simp
    PositiveBraidEquiv _ (i :: (coxeterWord m ++ (List.finRange (m - 1)).take j.val ++ [j])) :=
        hshift.symm
    _ = i :: (coxeterWord m ++ coxeterWord m) := by
        rw [List.append_assoc, ← hsnoc]

/-- For every letter `i`, the word `c ^ (m - 1 + 1) i` is positive braid equivalent to
`i c ^ (m - 1 + 1)`. The exponent `m - 1 + 1` equals `m` whenever a letter exists. -/
theorem torusWord_strandCount_append_singleton {m : ℕ} (i : Fin (m - 1)) :
    PositiveBraidEquiv (torusWord m (m - 1 + 1) ++ [i]) (i :: torusWord m (m - 1 + 1)) := by
  have hi := i.isLt
  let first : Fin (m - 1) := ⟨0, by omega⟩
  let last : Fin (m - 1) := ⟨m - 1 - 1, by omega⟩
  have hsplit : torusWord m (m - 1 + 1) =
      torusWord m i.val ++ torusWord m 2 ++ torusWord m (m - 1 - 1 - i.val) := by
    rw [← torusWord_add, ← torusWord_add]
    congr 1
    omega
  have h₁ : PositiveBraidEquiv (torusWord m (m - 1 - 1 - i.val) ++ [i])
      (last :: torusWord m (m - 1 - 1 - i.val)) :=
    torusWord_append_singleton _ i last (by simp [last]; omega)
  have h₂ : PositiveBraidEquiv (torusWord m 2 ++ [last]) (first :: torusWord m 2) := by
    rw [torusWord_two]
    exact coxeterWord_wrap first last rfl (by simp [last]; omega)
  have h₃ : PositiveBraidEquiv (torusWord m i.val ++ [first]) (i :: torusWord m i.val) :=
    torusWord_append_singleton _ first i (by simp [first])
  rw [hsplit]
  calc torusWord m i.val ++ torusWord m 2 ++ torusWord m (m - 1 - 1 - i.val) ++ [i]
      = (torusWord m i.val ++ torusWord m 2) ++
          (torusWord m (m - 1 - 1 - i.val) ++ [i]) := by simp
    PositiveBraidEquiv _ ((torusWord m i.val ++ torusWord m 2) ++
          (last :: torusWord m (m - 1 - 1 - i.val))) := h₁.append_left _
    _ = torusWord m i.val ++ (torusWord m 2 ++ [last]) ++
          torusWord m (m - 1 - 1 - i.val) := by simp
    PositiveBraidEquiv _ (torusWord m i.val ++ (first :: torusWord m 2) ++
          torusWord m (m - 1 - 1 - i.val)) := h₂.append_middle _ _
    _ = (torusWord m i.val ++ [first]) ++
          (torusWord m 2 ++ torusWord m (m - 1 - 1 - i.val)) := by simp
    PositiveBraidEquiv _ ((i :: torusWord m i.val) ++
          (torusWord m 2 ++ torusWord m (m - 1 - 1 - i.val))) := h₃.append_right _
    _ = i :: (torusWord m i.val ++ torusWord m 2 ++ torusWord m (m - 1 - 1 - i.val)) := by
        simp

/-! ### Centrality of the full twist -/

/-- The full twist is nonempty when `2 ≤ m`, because its length is `m (m - 1)`. -/
theorem fullTwistWord_ne_nil {m : ℕ} (hm : 2 ≤ m) : fullTwistWord m ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [fullTwistWord, torusWord_length, List.length_nil] at hl
  rcases Nat.mul_eq_zero.mp hl with h | h <;> omega

/-- For every letter `i`, the word `Δ² i` is positive braid equivalent to `i Δ²`, that is,
`Δ² σᵢ ≡ σᵢ Δ²`. -/
theorem fullTwistWord_append_singleton {m : ℕ} (i : Fin (m - 1)) :
    PositiveBraidEquiv (fullTwistWord m ++ [i]) (i :: fullTwistWord m) := by
  have hm : m - 1 + 1 = m := by have := i.isLt; omega
  have h := torusWord_strandCount_append_singleton i
  rw [hm] at h
  exact h

/-- The full twist commutes with every generator inside an arbitrary word, by far commutations
and positive braid relations only. -/
theorem fullTwist_central_braidEquiv {m : ℕ} (u v : PositiveAdjacentWord m) (i : Fin (m - 1)) :
    PositiveBraidEquiv (u ++ i :: (fullTwistWord m ++ v)) (u ++ fullTwistWord m ++ i :: v) := by
  have h := (fullTwistWord_append_singleton i).symm.append_middle u v
  simpa using h

/-- The full twist commutes with every word inside an arbitrary word, by far commutations and
positive braid relations only. -/
theorem fullTwist_commute_braidEquiv {m : ℕ} (u x v : PositiveAdjacentWord m) :
    PositiveBraidEquiv (u ++ x ++ fullTwistWord m ++ v) (u ++ fullTwistWord m ++ x ++ v) := by
  induction x generalizing u with
  | nil => exact PositiveBraidEquiv.of_eq (by simp)
  | cons y x ih =>
    have h₁ := ih (u ++ [y])
    have h₂ := fullTwist_central_braidEquiv u (x ++ v) y
    simp only [List.append_assoc, List.cons_append, List.nil_append]
      at h₁ h₂ ⊢
    exact h₁.trans h₂

/-- Acceptance statement of J08: the full twist commutes with every generator inside an arbitrary
word, up to positive word conjugacy. The underlying chain consists of far commutations and
positive braid relations (`fullTwist_central_braidEquiv`). -/
theorem fullTwist_central {m : ℕ} (u v : PositiveAdjacentWord m) (i : Fin (m - 1)) :
    PositiveWordConj (u ++ i :: (fullTwistWord m ++ v)) (u ++ fullTwistWord m ++ i :: v) :=
  (fullTwist_central_braidEquiv u v i).positiveWordConj (by simp)

/-- The full twist commutes with every word inside an arbitrary word, up to positive word
conjugacy, when `2 ≤ m`. -/
theorem fullTwist_commute {m : ℕ} (hm : 2 ≤ m) (u x v : PositiveAdjacentWord m) :
    PositiveWordConj (u ++ x ++ fullTwistWord m ++ v) (u ++ fullTwistWord m ++ x ++ v) :=
  (fullTwist_commute_braidEquiv u x v).positiveWordConj (by simp [fullTwistWord_ne_nil hm])

/-! ### Far commutations and rotations of words -/

/-- One far commutation inside a word, or one cyclic rotation of a word moving its last letter
to the front. -/
inductive FarRotationStep {m : ℕ} : PositiveAdjacentWord m → PositiveAdjacentWord m → Prop
  | far (u v : PositiveAdjacentWord m) (i j : Fin (m - 1))
      (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
      FarRotationStep (u ++ i :: j :: v) (u ++ j :: i :: v)
  | rotate (u : PositiveAdjacentWord m) (i : Fin (m - 1)) : FarRotationStep (u ++ [i]) (i :: u)

/-- The equivalence relation on positive words generated by far commutations inside words and
cyclic rotations. -/
def FarRotationEquiv {m : ℕ} (u v : PositiveAdjacentWord m) : Prop :=
  Relation.EqvGen FarRotationStep u v

/-- A far commutation or a rotation permutes the letters of a word. -/
theorem FarRotationStep.perm {m : ℕ} {u v : PositiveAdjacentWord m} (h : FarRotationStep u v) :
    u.Perm v := by
  cases h with
  | far u v i j _ => exact List.Perm.append_left u (List.Perm.swap j i v)
  | rotate u i => exact List.perm_append_comm

namespace FarRotationEquiv

variable {m : ℕ} {u v w : PositiveAdjacentWord m}

/-- Far rotation equivalence is reflexive. -/
@[refl] theorem refl (u : PositiveAdjacentWord m) : FarRotationEquiv u u :=
  Relation.EqvGen.refl u

/-- Far rotation equivalence is symmetric. -/
@[symm] theorem symm (h : FarRotationEquiv u v) : FarRotationEquiv v u :=
  Relation.EqvGen.symm _ _ h

/-- Far rotation equivalence is transitive. -/
theorem trans (h₁ : FarRotationEquiv u v) (h₂ : FarRotationEquiv v w) : FarRotationEquiv u w :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

/-- A single far commutation or rotation is a far rotation equivalence. -/
theorem of_step (h : FarRotationStep u v) : FarRotationEquiv u v :=
  Relation.EqvGen.rel _ _ h

/-- Equal words are far rotation equivalent. -/
theorem of_eq (h : u = v) : FarRotationEquiv u v :=
  h ▸ refl u

/-- Transitivity of far rotation equivalence, for `calc` chains. -/
instance instTransFarRotationEquiv :
    Trans (@FarRotationEquiv m) (@FarRotationEquiv m) (@FarRotationEquiv m) :=
  ⟨trans⟩

/-- Far rotation equivalence is an equivalence relation. -/
theorem equivalence : Equivalence (@FarRotationEquiv m) :=
  ⟨refl, symm, trans⟩

/-- A far commutation inside a word. -/
theorem far (u v : PositiveAdjacentWord m) (i j : Fin (m - 1))
    (h : i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val) :
    FarRotationEquiv (u ++ i :: j :: v) (u ++ j :: i :: v) :=
  of_step (.far u v i j h)

/-- A cyclic rotation moving the last letter to the front. -/
theorem rotate (u : PositiveAdjacentWord m) (i : Fin (m - 1)) :
    FarRotationEquiv (u ++ [i]) (i :: u) :=
  of_step (.rotate u i)

/-- A property of pairs of words that is an equivalence relation and holds for every far
commutation and every rotation holds for every pair of far rotation equivalent words. -/
theorem rec_on_steps {p : PositiveAdjacentWord m → PositiveAdjacentWord m → Prop}
    (hp : Equivalence p) (hstep : ∀ u v, FarRotationStep u v → p u v)
    (h : FarRotationEquiv u v) : p u v := by
  unfold FarRotationEquiv at h
  induction h with
  | rel x y hxy => exact hstep x y hxy
  | refl x => exact hp.refl x
  | symm x y _ ih => exact hp.symm ih
  | trans x y z _ _ ih₁ ih₂ => exact hp.trans ih₁ ih₂

/-- Far rotation equivalent words are permutations of each other. -/
theorem perm (h : FarRotationEquiv u v) : u.Perm v :=
  rec_on_steps (p := fun u v => u.Perm v) ⟨List.Perm.refl, List.Perm.symm, List.Perm.trans⟩
    (fun _ _ hs => hs.perm) h

/-- A letter moves to the left past a word all of whose letters are far from it, inside an
arbitrary context. -/
theorem pass_far (a b w : PositiveAdjacentWord m) (x : Fin (m - 1))
    (hw : ∀ y ∈ w, y.val + 2 ≤ x.val ∨ x.val + 2 ≤ y.val) :
    FarRotationEquiv (a ++ w ++ x :: b) (a ++ x :: (w ++ b)) := by
  induction w generalizing a with
  | nil => exact of_eq (by simp)
  | cons y w ih =>
    have h₁ := ih (a ++ [y]) fun z hz => hw z (List.mem_cons_of_mem y hz)
    have h₂ := far a (w ++ b) y x (hw y List.mem_cons_self)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
      at h₁ h₂ ⊢
    exact h₁.trans h₂

/-- Rotation of a block: `α β` is far rotation equivalent to `β α`. -/
theorem append_comm (α β : PositiveAdjacentWord m) : FarRotationEquiv (α ++ β) (β ++ α) := by
  induction β generalizing α with
  | nil => exact of_eq (by simp)
  | cons b β ih =>
    have h₁ := ih (α ++ [b])
    have h₂ := rotate (β ++ α) b
    simp only [List.append_assoc, List.cons_append, List.nil_append]
      at h₁ h₂ ⊢
    exact h₁.trans h₂

end FarRotationEquiv

/-- A single far commutation or rotation of a word `δ` with pairwise distinct letters smaller
than `t` remains a far rotation equivalence after the letter `t` is appended. -/
theorem FarRotationStep.append_singleton_lift {m : ℕ} {δ δ' : PositiveAdjacentWord m}
    (h : FarRotationStep δ δ') (t : Fin (m - 1)) (hδ : ∀ x ∈ δ, x.val < t.val)
    (hnd : δ.Nodup) : FarRotationEquiv (δ ++ [t]) (δ' ++ [t]) := by
  cases h with
  | far u v i j hij =>
    have := FarRotationEquiv.far u (v ++ [t]) i j hij
    simpa using this
  | rotate u i =>
    have hi : i.val < t.val := hδ i (by simp)
    by_cases hfar : i.val + 2 ≤ t.val
    · have h₁ := FarRotationEquiv.far u [] i t (Or.inl hfar)
      have h₂ := FarRotationEquiv.rotate (u ++ [t]) i
      simp only [List.append_assoc, List.cons_append, List.nil_append]
        at h₁ h₂ ⊢
      exact h₁.trans h₂
    · have hiu : i ∉ u := by
        have hnd' : (i :: u).Nodup := List.perm_append_comm.nodup_iff.mp hnd
        exact (List.nodup_cons.mp hnd').1
      have hu : ∀ y ∈ u, y.val + 2 ≤ t.val ∨ t.val + 2 ≤ y.val := by
        intro y hy
        have hy' := hδ y (by simp [hy])
        have hne : y.val ≠ i.val := fun he => hiu (Fin.ext he ▸ hy)
        left
        omega
      have h₁ := FarRotationEquiv.rotate (u ++ [i]) t
      have h₂ := FarRotationEquiv.rotate (t :: u) i
      have h₃ := FarRotationEquiv.pass_far [i] [] u t hu
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
        at h₁ h₂ h₃ ⊢
      exact h₁.trans (h₂.trans h₃.symm)

/-- A far rotation equivalence between words `δ` and `δ'` remains a far rotation equivalence
after the letter `t` is appended, provided the letters of `δ` are pairwise distinct and smaller
than `t`. -/
theorem FarRotationEquiv.append_singleton_lift {m : ℕ} {δ δ' : PositiveAdjacentWord m}
    (h : FarRotationEquiv δ δ') (t : Fin (m - 1)) (hδ : ∀ x ∈ δ, x.val < t.val)
    (hnd : δ.Nodup) : FarRotationEquiv (δ ++ [t]) (δ' ++ [t]) := by
  let P : PositiveAdjacentWord m → Prop := fun δ => (∀ x ∈ δ, x.val < t.val) ∧ δ.Nodup
  have hP : ∀ {δ δ' : PositiveAdjacentWord m}, δ.Perm δ' → P δ → P δ' :=
    fun hp hδ => ⟨fun x hx => hδ.1 x (hp.mem_iff.mpr hx), hp.nodup_iff.mp hδ.2⟩
  have key : δ.Perm δ' ∧ (P δ → FarRotationEquiv (δ ++ [t]) (δ' ++ [t])) := by
    refine FarRotationEquiv.rec_on_steps
      (p := fun δ δ' => δ.Perm δ' ∧ (P δ → FarRotationEquiv (δ ++ [t]) (δ' ++ [t])))
      ⟨?_, ?_, ?_⟩ ?_ h
    · intro x
      exact ⟨List.Perm.refl x, fun _ => FarRotationEquiv.refl _⟩
    · intro x y hxy
      exact ⟨hxy.1.symm, fun hy => (hxy.2 (hP hxy.1.symm hy)).symm⟩
    · intro x y z hxy hyz
      exact ⟨hxy.1.trans hyz.1, fun hx => (hxy.2 hx).trans (hyz.2 (hP hxy.1 hx))⟩
    · intro x y hs
      exact ⟨hs.perm, fun hx => hs.append_singleton_lift t hx.1 hx.2⟩
  exact key.2 ⟨hδ, hnd⟩

/-! ### Conjugacy of Coxeter words -/

/-- Every permutation of the first `k` letters `0, 1, …, k - 1` is far rotation equivalent to the
word `0 1 ⋯ (k - 1)`. -/
theorem farRotationEquiv_take_finRange {m : ℕ} (k : ℕ) (hk : k ≤ m - 1)
    (γ : PositiveAdjacentWord m) (hγ : γ.Perm ((List.finRange (m - 1)).take k)) :
    FarRotationEquiv γ ((List.finRange (m - 1)).take k) := by
  induction k generalizing γ with
  | zero =>
    rw [List.take_zero] at hγ ⊢
    obtain rfl := List.perm_nil.mp hγ
    exact FarRotationEquiv.refl _
  | succ k ih =>
    have hk' : k < m - 1 := by omega
    rw [take_finRange_succ hk'] at hγ ⊢
    generalize ht : (⟨k, hk'⟩ : Fin (m - 1)) = t at hγ ⊢
    have htk : t.val = k := by rw [← ht]
    have htmem : t ∈ γ := hγ.symm.subset (by simp)
    obtain ⟨α, β, rfl⟩ := List.append_of_mem htmem
    have hrot : FarRotationEquiv (α ++ t :: β) (β ++ α ++ [t]) := by
      have := FarRotationEquiv.append_comm (α ++ [t]) β
      simpa using this
    have hδ : (β ++ α).Perm ((List.finRange (m - 1)).take k) :=
      (List.perm_append_right_iff [t]).mp (hrot.perm.symm.trans hγ)
    have hlt : ∀ x ∈ β ++ α, x.val < t.val := fun x hx => htk ▸ mem_take_finRange (hδ.subset hx)
    have hnd : (β ++ α).Nodup :=
      hδ.nodup_iff.mpr ((List.nodup_finRange _).sublist (List.take_sublist _ _))
    exact hrot.trans ((ih hk'.le (β ++ α) hδ).append_singleton_lift t hlt hnd)

/-- Every Coxeter word, that is, every permutation of the Coxeter word, is far rotation equivalent
to the Coxeter word. -/
theorem farRotationEquiv_coxeterWord {m : ℕ} (γ : PositiveAdjacentWord m)
    (hγ : γ.Perm (List.finRange (m - 1))) : FarRotationEquiv γ (coxeterWord m) := by
  have h : (List.finRange (m - 1)).take (m - 1) = List.finRange (m - 1) :=
    List.take_of_length_le (by simp)
  have := farRotationEquiv_take_finRange (m - 1) le_rfl γ (by rw [h]; exact hγ)
  rw [h] at this
  exact this

/-- If `2 ≤ m`, a far rotation equivalence of words `γ` and `γ'` yields a positive word
conjugacy of `Δ² γ` and `Δ² γ'`. A rotated letter passes through `Δ²` by `fullTwist_central`. -/
theorem FarRotationEquiv.fullTwist_positiveWordConj {m : ℕ} (hm : 2 ≤ m)
    {γ γ' : PositiveAdjacentWord m} (h : FarRotationEquiv γ γ') :
    PositiveWordConj (fullTwistWord m ++ γ) (fullTwistWord m ++ γ') := by
  refine FarRotationEquiv.rec_on_steps
    (p := fun γ γ' => PositiveWordConj (fullTwistWord m ++ γ) (fullTwistWord m ++ γ'))
    ⟨?_, ?_, ?_⟩ ?_ h
  · intro x
    exact PositiveWordConj.refl_of_ne_nil (by simp [fullTwistWord_ne_nil hm])
  · intro x y hxy
    exact hxy.symm
  · intro x y z h₁ h₂
    exact h₁.trans h₂
  · intro x y hs
    cases hs with
    | far u v i j hij => simpa using PositiveWordConj.far (fullTwistWord m ++ u) v i j hij
    | rotate u i =>
      have h₁ := PositiveWordConj.cyclic (fullTwistWord m ++ u) i
      have h₂ := fullTwist_central [] u i
      simp only [List.nil_append, List.append_assoc] at h₁ h₂ ⊢
      exact h₁.trans h₂

/-- Acceptance statement of J08, with the hypothesis `2 ≤ m`: for every permutation `γ` of the
Coxeter word, `Δ² γ` and `Δ² c` are conjugate positive words. -/
theorem fullTwist_coxeter_conj {m : ℕ} (γ : PositiveAdjacentWord m)
    (hγ : γ.Perm (List.finRange (m - 1))) (hm : 2 ≤ m) :
    PositiveWordConj (fullTwistWord m ++ γ) (fullTwistWord m ++ coxeterWord m) :=
  (farRotationEquiv_coxeterWord γ hγ).fullTwist_positiveWordConj hm

/-- If `2 ≤ m`, then for any two permutations `γ` and `γ'` of the Coxeter word, `Δ² γ` and
`Δ² γ'` are conjugate positive words. -/
theorem fullTwist_coxeter_conj_of_perm {m : ℕ} (γ γ' : PositiveAdjacentWord m)
    (hγ : γ.Perm (List.finRange (m - 1))) (hγ' : γ'.Perm (List.finRange (m - 1))) (hm : 2 ≤ m) :
    PositiveWordConj (fullTwistWord m ++ γ) (fullTwistWord m ++ γ') :=
  (fullTwist_coxeter_conj γ hγ hm).trans (fullTwist_coxeter_conj γ' hγ' hm).symm

/-- For `m ≤ 1` there is no generator, every word is empty, and no two words are conjugate. -/
theorem not_positiveWordConj_of_le_one {m : ℕ} (hm : m ≤ 1) (u v : PositiveAdjacentWord m) :
    ¬PositiveWordConj u v := by
  intro h
  apply h.ne_nil_left
  cases u with
  | nil => rfl
  | cons x _ => exact absurd x.isLt (by omega)

/-- The conclusion of `fullTwist_coxeter_conj` holds exactly when `2 ≤ m`. -/
theorem fullTwist_coxeter_conj_iff {m : ℕ} (γ : PositiveAdjacentWord m)
    (hγ : γ.Perm (List.finRange (m - 1))) :
    PositiveWordConj (fullTwistWord m ++ γ) (fullTwistWord m ++ coxeterWord m) ↔ 2 ≤ m := by
  refine ⟨fun h => ?_, fullTwist_coxeter_conj γ hγ⟩
  by_contra hm
  exact not_positiveWordConj_of_le_one (by omega) _ _ h

end OnLeConjecture.KnotTheory
