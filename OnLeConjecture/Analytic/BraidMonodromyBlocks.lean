/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyLift
public import OnLeConjecture.Analytic.BraidMonodromyShift

/-!
# Two separated blocks of moving strands

In the local factors of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`, subsection "Local factors, without a generic-Morse
projection") the sheets near a critical value split into groups occupying disjoint vertical
strips, and all groups move. This module proves that the path word of a family of `d + k` strands
whose first `d` strands stay to the left of a vertical line and whose last `k` strands stay to
the right of it is the product of the path word of the left block, placed on the first `d`
strands, and of the path word of the right block, placed on the last `k` strands. It generalizes
`IsPathWord.block` (static right block).

* `shiftSigned d w`: a signed word on `k` strands placed on the strands `d, …, d + k - 1`.
* `staticWord_eq_shiftSigned`: the word of the low strands in the recursion of the layered word
  is their shifted layered word.
* `layeredTransition_twoBlock`, `localWord_twoBlock`: the transition words and the local words of
  two separated blocks split into a lifted and a shifted part.
* `IsPathWord.twoBlock`: the path word of two separated blocks.
* `IsRepresentedByPositiveWord.twoBlock_signedBraidConj`: if the two blocks are represented by
  positive words `w_L` and `w_R`, every path word of the whole family is conjugate to
  `w_L` on the first `d` strands followed by `w_R` on the last `k` strands.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.KnotTheory

open SignedAdjacentWord

/-! ### Shifted signed words -/

/-- A signed word on `k` strands placed on the strands `d, …, d + k - 1` of `d + k` strands. -/
def shiftSigned (d : ℕ) {k : ℕ} (w : SignedAdjacentWord k) : SignedAdjacentWord (d + k) :=
  w.map fun a => ((⟨d + a.1.val, by have := a.1.isLt; omega⟩ : Fin (d + k - 1)), a.2)

section Shift

variable (d : ℕ) {k : ℕ}

@[simp] theorem shiftSigned_nil : shiftSigned d ([] : SignedAdjacentWord k) = [] := rfl

@[simp] theorem shiftSigned_append (u v : SignedAdjacentWord k) :
    shiftSigned d (u ++ v) = shiftSigned d u ++ shiftSigned d v := by
  simp [shiftSigned]

theorem shiftSigned_inv (w : SignedAdjacentWord k) :
    shiftSigned d (inv w) = inv (shiftSigned d w) := by
  simp [shiftSigned, inv, List.map_reverse]

theorem mem_shiftSigned {w : SignedAdjacentWord k} {b : Fin (d + k - 1) × ℤˣ}
    (hb : b ∈ shiftSigned d w) : d ≤ b.1.val := by
  simp only [shiftSigned, List.mem_map] at hb
  obtain ⟨a, -, rfl⟩ := hb
  simp

theorem shiftSigned_liftWordSucc (w : SignedAdjacentWord k) :
    shiftSigned d (liftWordSucc k w) = liftWordSucc (d + k) (shiftSigned d w) := by
  simp only [shiftSigned, liftWordSucc, List.map_map]
  rfl

theorem shiftSigned_descRun : ∀ (hi lo : ℕ), hi ≤ k →
    shiftSigned d (descRun k hi lo) = descRun (d + k) (d + hi) (d + lo)
  | hi, lo, hk => by
    by_cases h : lo < hi
    · rw [descRun_of_lt h (by omega), descRun_of_lt (n := d + k) (by omega) (by omega),
        shiftSigned_append, shiftSigned_descRun hi (lo + 1) hk, show d + (lo + 1) = d + lo + 1 by
          omega]
      rfl
    · rw [descRun_of_le (by omega), descRun_of_le (by omega)]
      rfl
  termination_by hi lo => hi - lo

theorem SignedBraidStep.shiftSigned {u v : SignedAdjacentWord k} (hs : SignedBraidStep u v) :
    SignedBraidStep (OnLeConjecture.KnotTheory.shiftSigned d u)
      (OnLeConjecture.KnotTheory.shiftSigned d v) := by
  cases hs with
  | cancel u v i e =>
    simpa [OnLeConjecture.KnotTheory.shiftSigned] using
      SignedBraidStep.cancel (OnLeConjecture.KnotTheory.shiftSigned d u)
        (OnLeConjecture.KnotTheory.shiftSigned d v)
        (⟨d + i.val, by have := i.isLt; omega⟩ : Fin (d + k - 1)) e
  | far u v i j e f hf =>
    simpa [OnLeConjecture.KnotTheory.shiftSigned] using
      SignedBraidStep.far (OnLeConjecture.KnotTheory.shiftSigned d u)
        (OnLeConjecture.KnotTheory.shiftSigned d v)
        (⟨d + i.val, by have := i.isLt; omega⟩ : Fin (d + k - 1))
        (⟨d + j.val, by have := j.isLt; omega⟩ : Fin (d + k - 1)) e f (by simp only; omega)
  | braid u v i j hj =>
    simpa [OnLeConjecture.KnotTheory.shiftSigned] using
      SignedBraidStep.braid (OnLeConjecture.KnotTheory.shiftSigned d u)
        (OnLeConjecture.KnotTheory.shiftSigned d v)
        (⟨d + i.val, by have := i.isLt; omega⟩ : Fin (d + k - 1))
        (⟨d + j.val, by have := j.isLt; omega⟩ : Fin (d + k - 1)) (by simp only; omega)

theorem SignedBraidEquiv.shiftSigned {u v : SignedAdjacentWord k} (he : SignedBraidEquiv u v) :
    SignedBraidEquiv (OnLeConjecture.KnotTheory.shiftSigned d u)
      (OnLeConjecture.KnotTheory.shiftSigned d v) := by
  induction he with
  | rel _ _ hs => exact SignedBraidEquiv.of_step (hs.shiftSigned d)
  | refl => exact SignedBraidEquiv.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Shift

/-- Lifted words commute with shifted words. -/
theorem liftSigned_shiftSigned_comm {d k : ℕ} (u : SignedAdjacentWord d)
    (v : SignedAdjacentWord k) :
    SignedBraidEquiv (shiftSigned d v ++ liftSigned (Nat.le_add_right d k) u)
      (liftSigned (Nat.le_add_right d k) u ++ shiftSigned d v) :=
  SignedBraidEquiv.far_comm _ _ fun a ha b hb => by
    have h1 := mem_shiftSigned d ha
    have h2 := mem_liftSigned _ hb
    omega

section TwoBlock

variable {α : Type*} [LinearOrder α]

/-- The word of the low strands in the recursion of the layered word is their shifted layered
word. -/
theorem staticWord_eq_shiftSigned (d : ℕ) : ∀ (k : ℕ) (cs : Fin k → α),
    staticWord d k cs = shiftSigned d (layeredWord k cs)
  | 0, _ => rfl
  | k + 1, cs => by
    rw [staticWord, layeredWord_succ, shiftSigned_append, shiftSigned_liftWordSucc,
      ← staticWord_eq_shiftSigned d k, shiftSigned_descRun d k _ le_rfl]

/-- **Transition words of two separated blocks.** -/
theorem layeredTransition_twoBlock {d k : ℕ} {c₁ c₂ : Fin (d + k) → α} (h₁ : Injective c₁)
    (h₂ : Injective c₂) (hl₁ : StaticLow d k c₁) (hl₂ : StaticLow d k c₂) :
    SignedBraidEquiv (inv (layeredWord (d + k) c₁) ++ layeredWord (d + k) c₂)
      (liftSigned (Nat.le_add_right d k)
          (inv (layeredWord d (c₁ ∘ Fin.castAdd k)) ++ layeredWord d (c₂ ∘ Fin.castAdd k)) ++
        shiftSigned d
          (inv (layeredWord k (c₁ ∘ Fin.natAdd d)) ++ layeredWord k (c₂ ∘ Fin.natAdd d))) := by
  rw [layeredWord_staticLow d k c₁ h₁ hl₁, layeredWord_staticLow d k c₂ h₂ hl₂,
    staticWord_eq_shiftSigned, staticWord_eq_shiftSigned, inv_append, liftSigned_append,
    liftSigned_inv, shiftSigned_append, shiftSigned_inv]
  set X := inv (liftSigned (Nat.le_add_right d k) (layeredWord d (c₁ ∘ Fin.castAdd k)))
  set Y := liftSigned (Nat.le_add_right d k) (layeredWord d (c₂ ∘ Fin.castAdd k))
  set U := inv (shiftSigned d (layeredWord k (c₁ ∘ Fin.natAdd d)))
  set V := shiftSigned d (layeredWord k (c₂ ∘ Fin.natAdd d))
  have hcomm : SignedBraidEquiv (U ++ (X ++ Y)) ((X ++ Y) ++ U) :=
    SignedBraidEquiv.far_comm _ _ fun a ha b hb => by
      have h1 : d ≤ a.1.val := by
        simp only [U, inv, List.mem_reverse, List.mem_map] at ha
        obtain ⟨a', ha', rfl⟩ := ha
        have := mem_shiftSigned d ha'
        exact this
      rcases List.mem_append.mp hb with hb | hb
      · have : b.1.val + 2 ≤ d := by
          simp only [X, inv, List.mem_reverse, List.mem_map] at hb
          obtain ⟨b', hb', rfl⟩ := hb
          have := mem_liftSigned _ hb'
          exact this
        omega
      · have := mem_liftSigned _ hb
        omega
  have h1 := hcomm.append_right V
  simp only [List.append_assoc] at h1 ⊢
  exact h1

end TwoBlock

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

/-- **Local words of two separated blocks.** If the first `d` points of `x` and `y` lie to the
left of the line `Re = x₀` and their last `k` points to the right of it, and `z` is injective,
the local word from `x` to `y` with center `z` is the lifted local word of the first `d` points
followed by the shifted local word of the last `k` points. -/
theorem localWord_twoBlock {d k : ℕ} {x₀ : ℝ} {z x y : Fin (d + k) → ℂ} (hz : Injective z)
    (hx : Injective x) (hy : Injective y) (hbx : IsBlockConfig d k x₀ x)
    (hby : IsBlockConfig d k x₀ y) :
    SignedBraidEquiv (localWord z x y)
      (liftSigned (Nat.le_add_right d k)
          (localWord (z ∘ Fin.castAdd k) (x ∘ Fin.castAdd k) (y ∘ Fin.castAdd k)) ++
        shiftSigned d (localWord (z ∘ Fin.natAdd d) (x ∘ Fin.natAdd d) (y ∘ Fin.natAdd d))) := by
  classical
  -- New heights: the right block below the left block, in the same relative order.
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, ∀ i : Fin d, m₀ ≤ (z (Fin.castAdd k i)).im := by
    rcases isEmpty_or_nonempty (Fin d) with hd | hd
    · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i : Fin d => (z (Fin.castAdd k i)).im
      exact ⟨_, hi₀⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℝ, ∀ j : Fin k, (z (Fin.natAdd d j)).im ≤ m₁ := by
    rcases isEmpty_or_nonempty (Fin k) with hk | hk
    · exact ⟨0, fun j => (IsEmpty.false j).elim⟩
    · obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j : Fin k => (z (Fin.natAdd d j)).im
      exact ⟨_, hj₀⟩
  set C := m₁ - m₀ + 1 with hC
  let cR : Fin k → Lex (ℝ × ℝ) := fun j =>
    toLex ((z (Fin.natAdd d j)).im - C, (z (Fin.natAdd d j)).re)
  let c' : Fin (d + k) → Lex (ℝ × ℝ) := Fin.addCases (fun i => heightKey (z (Fin.castAdd k i))) cR
  have hc'L : ∀ i, c' (Fin.castAdd k i) = heightKey (z (Fin.castAdd k i)) := fun i => by
    simp [c']
  have hc'R : ∀ j, c' (Fin.natAdd d j) = cR j := fun j => by simp [c']
  have hcR : ∀ j j', cR j < cR j' ↔ heightKey (z (Fin.natAdd d j)) < heightKey (z (Fin.natAdd d j'))
      := fun j j' => by
    simp only [cR, heightKey, Prod.Lex.toLex_lt_toLex]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · left; linarith
      · right; exact ⟨by linarith, h'⟩
    · rintro (h | ⟨h, h'⟩)
      · left; linarith
      · right; exact ⟨by rw [h], h'⟩
  have hcRinj : Injective cR := by
    intro j j' h
    have h1 := congrArg (fun p => (ofLex p).1) h
    have h2 := congrArg (fun p => (ofLex p).2) h
    simp only [cR, ofLex_toLex, sub_left_inj] at h1 h2
    exact Fin.natAdd_injective k d (hz (Complex.ext h2 h1))
  have hlowc : ∀ i j, c' (Fin.natAdd d j) < c' (Fin.castAdd k i) := fun i j => by
    rw [hc'L, hc'R]
    simp only [cR, heightKey, Prod.Lex.toLex_lt_toLex]
    left
    have := hm₀ i
    have := hm₁ j
    linarith
  have hc'inj : Injective c' := by
    intro p q hpq
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left i' =>
        rw [hc'L, hc'L] at hpq
        exact congrArg _ ((Fin.castAdd_injective d k) (hz (heightKey_injective hpq)))
      | right j' => exact absurd hpq (hlowc i j').ne'
    | right j =>
      induction q using Fin.addCases with
      | left i' => exact absurd hpq (hlowc i' j).ne
      | right j' =>
        rw [hc'R, hc'R] at hpq
        exact congrArg _ (hcRinj hpq)
  have hπ := configSort_block hx hbx
  have hρ := configSort_block hy hby
  -- The inverted pairs lie in one block.
  have hagree : ∀ p q, (configSort x).symm p < (configSort x).symm q →
      (configSort y).symm q < (configSort y).symm p →
      ((heightKey ∘ z) p < (heightKey ∘ z) q ↔ c' p < c' q) := by
    intro p q h1 h2
    rw [hπ] at h1
    rw [hρ] at h2
    induction p using Fin.addCases with
    | left i =>
      induction q using Fin.addCases with
      | left i' => simp [hc'L]
      | right j' =>
        exfalso
        simp only [blockPerm_symm_castAdd, blockPerm_symm_natAdd, Fin.lt_def, Fin.val_natAdd,
          Fin.val_castAdd] at h2
        have := ((configSort (y ∘ Fin.castAdd k)).symm i).isLt
        omega
    | right j =>
      induction q using Fin.addCases with
      | left i' =>
        exfalso
        simp only [blockPerm_symm_castAdd, blockPerm_symm_natAdd, Fin.lt_def, Fin.val_natAdd,
          Fin.val_castAdd] at h1
        have := ((configSort (x ∘ Fin.castAdd k)).symm i').isLt
        omega
      | right j' =>
        simp only [Function.comp_apply, hc'R]
        exact (hcR j j').symm
  have h1 := layeredTransition_congr_any (heightKey_injective.comp hz) hc'inj (configSort x)
    (configSort y) hagree
  have hl₁ : StaticLow d k (c' ∘ ⇑(configSort x)) := fun i j => by
    simp only [Function.comp_apply, hπ, blockPerm_castAdd, blockPerm_natAdd]
    exact hlowc _ _
  have hl₂ : StaticLow d k (c' ∘ ⇑(configSort y)) := fun i j => by
    simp only [Function.comp_apply, hρ, blockPerm_castAdd, blockPerm_natAdd]
    exact hlowc _ _
  have h2 := layeredTransition_twoBlock (hc'inj.comp (configSort x).injective)
    (hc'inj.comp (configSort y).injective) hl₁ hl₂
  have eL : ∀ w : Fin (d + k) → ℂ, IsBlockConfig d k x₀ w → Injective w →
      (c' ∘ ⇑(configSort w)) ∘ Fin.castAdd k = heightKey ∘ (z ∘ Fin.castAdd k) ∘
        ⇑(configSort (w ∘ Fin.castAdd k)) := fun w hw hwi => by
    funext i
    simp only [Function.comp_apply, configSort_block hwi hw, blockPerm_castAdd, hc'L]
  have eR : ∀ w : Fin (d + k) → ℂ, IsBlockConfig d k x₀ w → Injective w →
      (c' ∘ ⇑(configSort w)) ∘ Fin.natAdd d = cR ∘ ⇑(configSort (w ∘ Fin.natAdd d)) :=
    fun w hw hwi => by
      funext j
      simp only [Function.comp_apply, configSort_block hwi hw, blockPerm_natAdd, hc'R]
  rw [eL x hbx hx, eL y hby hy, eR x hbx hx, eR y hby hy] at h2
  -- The heights of the right block can be replaced by its actual heights.
  have h3 := layeredTransition_congr_any hcRinj
    (heightKey_injective.comp (hz.comp (Fin.natAdd_injective k d)))
    (configSort (x ∘ Fin.natAdd d)) (configSort (y ∘ Fin.natAdd d))
    fun j j' _ _ => by simpa using hcR j j'
  unfold localWord
  refine h1.trans (h2.trans ((SignedBraidEquiv.refl _).append (h3.shiftSigned d)))

/-! ### Path words of two separated blocks -/

/-- **The path word of two separated blocks.** Let the first `d` strands of `K` stay to the left
of the line `Re = x₀` and its last `k` strands to the right of it during `[u, v]`. If `W_L` and
`W_R` are path words of the two blocks, the lifted word of `W_L` followed by the shifted word of
`W_R` is a path word of `K`. -/
theorem IsPathWord.twoBlock {d k : ℕ} {K : Fin (d + k) → ℝ → ℂ} {x₀ u v : ℝ}
    (hinj : ∀ t ∈ Icc u v, Injective fun p => K p t)
    (hsep : ∀ t ∈ Icc u v, IsBlockConfig d k x₀ fun p => K p t)
    {WL : SignedAdjacentWord d} {WR : SignedAdjacentWord k}
    (hL : IsPathWord (fun i => K (Fin.castAdd k i)) u v WL)
    (hR : IsPathWord (fun j => K (Fin.natAdd d j)) u v WR) :
    IsPathWord K u v (liftSigned (Nat.le_add_right d k) WL ++ shiftSigned d WR) := by
  obtain ⟨δL, hδL, hL⟩ := hL
  obtain ⟨δR, hδR, hR⟩ := hR
  refine ⟨min δL δR, lt_min hδL hδR, fun t N P => ?_⟩
  have key : ∀ M ≤ N, SignedBraidEquiv (chainWord (fun a p => K p (t a)) M)
      (liftSigned (Nat.le_add_right d k) (chainWord (fun a i => K (Fin.castAdd k i) (t a)) M) ++
        shiftSigned d (chainWord (fun a j => K (Fin.natAdd d j) (t a)) M)) := by
    intro M
    induction M with
    | zero => intro _; simpa using SignedBraidEquiv.refl ([] : SignedAdjacentWord (d + k))
    | succ M ih =>
      intro hM
      have hloc := localWord_twoBlock (hinj _ (P.mem_Icc (a := M) (by omega)))
        (hinj _ (P.mem_Icc (a := M) (by omega))) (hinj _ (P.mem_Icc hM))
        (hsep _ (P.mem_Icc (a := M) (by omega))) (hsep _ (P.mem_Icc hM))
      rw [chainWord_succ, chainWord_succ, chainWord_succ, liftSigned_append, shiftSigned_append]
      refine ((ih (by omega)).append hloc).trans ?_
      set A := liftSigned (Nat.le_add_right d k)
        (chainWord (fun a i => K (Fin.castAdd k i) (t a)) M)
      set B := shiftSigned d (chainWord (fun a j => K (Fin.natAdd d j) (t a)) M)
      set a' := liftSigned (Nat.le_add_right d k)
        (localWord (fun i => K (Fin.castAdd k i) (t M)) (fun i => K (Fin.castAdd k i) (t M))
          fun i => K (Fin.castAdd k i) (t (M + 1)))
      set b' := shiftSigned d
        (localWord (fun j => K (Fin.natAdd d j) (t M)) (fun j => K (Fin.natAdd d j) (t M))
          fun j => K (Fin.natAdd d j) (t (M + 1)))
      have hc := liftSigned_shiftSigned_comm (d := d) (k := k)
        (localWord (fun i => K (Fin.castAdd k i) (t M)) (fun i => K (Fin.castAdd k i) (t M))
          fun i => K (Fin.castAdd k i) (t (M + 1)))
        (chainWord (fun a j => K (Fin.natAdd d j) (t a)) M)
      have := ((hc.append_left A).append_right b')
      simpa [List.append_assoc, Function.comp_def] using this
  refine (key N le_rfl).trans ((hL t N (P.mono (min_le_left _ _))).liftSigned _ |>.append
    ((hR t N (P.mono (min_le_right _ _))).shiftSigned d))

/-- Words with letters below `d - 1` commute with words with letters at least `d`. -/
theorem far_comm_of_bounds {d k : ℕ} {A B : SignedAdjacentWord (d + k)}
    (hA : ∀ a ∈ A, a.1.val + 2 ≤ d) (hB : ∀ b ∈ B, d ≤ b.1.val) :
    SignedBraidEquiv (A ++ B) (B ++ A) :=
  SignedBraidEquiv.far_comm _ _ fun a ha b hb => by
    have := hA a ha; have := hB b hb; omega

theorem mem_inv_iff_bound {m : ℕ} {P : ℕ → Prop} {A : SignedAdjacentWord m}
    (hA : ∀ a ∈ A, P a.1.val) : ∀ a ∈ inv A, P a.1.val := by
  intro a ha
  simp only [inv, List.mem_reverse, List.mem_map] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  exact hA a' ha'

/-- A product of a lifted and a shifted conjugate is a conjugate of the product. -/
theorem conj_twoBlock {d k : ℕ} (x wl : SignedAdjacentWord d) (y wr : SignedAdjacentWord k) :
    SignedBraidEquiv
      (liftSigned (Nat.le_add_right d k) (x ++ wl ++ inv x) ++ shiftSigned d (y ++ wr ++ inv y))
      (conjugateWord (liftSigned (Nat.le_add_right d k) x ++ shiftSigned d y)
        (liftSigned (Nat.le_add_right d k) wl ++ shiftSigned d wr)) := by
  have hl : ∀ w : SignedAdjacentWord d, ∀ a ∈ liftSigned (Nat.le_add_right d k) w,
      a.1.val + 2 ≤ d := fun w a ha => mem_liftSigned _ ha
  have hs : ∀ w : SignedAdjacentWord k, ∀ b ∈ shiftSigned d w, d ≤ b.1.val :=
    fun w b hb => mem_shiftSigned d hb
  simp only [liftSigned_append, shiftSigned_append, liftSigned_inv, shiftSigned_inv,
    conjugateWord, inv_append]
  have hilx := mem_inv_iff_bound (P := fun i => i + 2 ≤ d) (hl x)
  have hisy := mem_inv_iff_bound (P := fun i => d ≤ i) (hs y)
  set lx := liftSigned (Nat.le_add_right d k) x
  set lw := liftSigned (Nat.le_add_right d k) wl
  set sy := shiftSigned d y
  set sw := shiftSigned d wr
  have hB : ∀ b ∈ sy ++ sw ++ inv sy, d ≤ b.1.val := by
    intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact hs y b hb
    · exact hs wr b hb
    · exact hisy b hb
  have s1 := far_comm_of_bounds hilx hB
  have s2 := far_comm_of_bounds (hl wl) (hs y)
  have e1 := (s1.append_left lw).append_left lx
  have e2 := (s2.append_right (sw ++ inv sy ++ inv lx)).append_left lx
  simp only [List.append_assoc] at e1 e2 ⊢
  exact e1.trans e2

/-- **Two represented blocks.** If the left block of `d` strands and the right block of `k`
strands, separated by the line `Re = x₀`, are represented through closed braids by the positive
words `w_L` and `w_R`, every path word of the whole family is conjugate to `w_L` on the first
`d` strands followed by `w_R` on the last `k` strands. -/
theorem IsRepresentedByPositiveWord.twoBlock_signedBraidConj {d k : ℕ}
    {K : Fin (d + k) → ℝ → ℂ} {x₀ u v : ℝ} {wL : PositiveAdjacentWord d}
    {wR : PositiveAdjacentWord k}
    (hL : IsRepresentedByPositiveWord (fun i => K (Fin.castAdd k i)) u v wL)
    (hR : IsRepresentedByPositiveWord (fun j => K (Fin.natAdd d j)) u v wR)
    (hinj : ∀ t ∈ Icc u v, Injective fun p => K p t)
    (hsep : ∀ t ∈ Icc u v, IsBlockConfig d k x₀ fun p => K p t)
    {W : SignedAdjacentWord (d + k)} (hW : IsPathWord K u v W) :
    SignedBraidConj W
      (liftPositiveWord (Nat.le_add_right d k) wL ++ shiftSigned d wR.toSigned) := by
  obtain ⟨WL, hWL, hcL⟩ := hL.exists_isPathWord_signedBraidConj
  obtain ⟨WR, hWR, hcR⟩ := hR.exists_isPathWord_signedBraidConj
  have hlt : u < v := by obtain ⟨π, hiso⟩ := hL; exact hiso.left.lt
  have h1 := hW.unique hlt (hWL.twoBlock hinj hsep hWR)
  obtain ⟨x, hx⟩ := hcL.exists_conjugator
  obtain ⟨y, hy⟩ := hcR.exists_conjugator
  have h2 := (hx.liftSigned (Nat.le_add_right d k)).append (hy.shiftSigned d)
  rw [← liftSigned_toSigned]
  exact (h1.trans (h2.trans (conj_twoBlock x wL.toSigned y wR.toSigned))).toConj.trans
    (SignedBraidConj.conjugate_left _ _)

end OnLeConjecture.Analytic
