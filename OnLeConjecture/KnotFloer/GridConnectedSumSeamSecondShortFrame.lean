/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondFactorOneStepProjection
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepComplete

/-!
# Coordinates of the remaining second-factor rectangles

A remaining second-factor rectangle wraps in columns, its two row endpoints
are positive, and its top row is smaller than its bottom row. The zero
preimage of the source factor lies strictly between its side columns.
Conversely, these conditions and a nonempty first block give membership.

The file also records the retained source rows used by the explicit
correction paths, a construction of oriented rectangles from column swaps,
matching sources with three southwest columns, an emptiness criterion, and
extensionality of one- and two-transition correction paths by their sides.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

section Remaining
variable (x : GridState (n + 1)) (z w : GridState (m + 1))

/-- A remaining rectangle requires a nonempty first block. -/
theorem seamSecondRemaining_pos (ρ : SeamSecondRemainingRectangle x z w) : 0 < n := by
  obtain ⟨c, _, _⟩ := (seamSecondFactorRectangle_not_isEmpty_iff x ρ.val ρ.property.1).mp
    ρ.property.2.1
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) c.isLt

/-- A remaining rectangle wraps in columns and has rows `0 < top < bottom`. -/
theorem seamSecondRemaining_rows (ρ : SeamSecondRemainingRectangle x z w) :
    ρ.val.right < ρ.val.left ∧ 0 < ρ.val.top.val ∧ ρ.val.top.val < ρ.val.bottom.val := by
  have hcol := seamSecondRemainingRectangle_wraps x z w ρ
  have hb : ρ.val.bottom.val ≠ 0 := fun h => ρ.property.2.2.1 (Fin.ext h)
  have ht : ρ.val.top.val ≠ 0 := fun h => ρ.property.2.2.2 (Fin.ext h)
  refine ⟨hcol, by omega, ?_⟩
  by_contra hlt
  have hne : ρ.val.bottom.val ≠ ρ.val.top.val := fun h => ρ.val.bottom_ne_top (Fin.ext h)
  obtain ⟨c, _, hrow⟩ := (seamSecondFactorRectangle_not_isEmpty_iff x ρ.val ρ.property.1).mp
    ρ.property.2.1
  rw [seamSecondFactorRow_of_ne_zero x _ ρ.property.2.2.1,
    seamSecondFactorRow_of_ne_zero x _ ρ.property.2.2.2, Grid.mem_cIoo] at hrow
  have hx := (x c.castSucc).isLt
  have h2 := hrow.2
  split_ifs at h2 with hif
  · simp only [seamRight_val, seamLeft_val] at h2
    omega
  · simp only [seamRight_val] at hif
    omega

/-- The zero preimage of the source factor lies strictly between the two side columns. -/
theorem seamSecondRemaining_zero_between (ρ : SeamSecondRemainingRectangle x z w) :
    ρ.val.right.val < (z.toPerm.symm 0).val ∧ (z.toPerm.symm 0).val < ρ.val.left.val := by
  obtain ⟨hcol, htop, hlt⟩ := seamSecondRemaining_rows x z w ρ
  have hcol' := Fin.lt_def.mp hcol
  have hz : z (z.toPerm.symm 0) = 0 := z.toPerm.apply_symm_apply 0
  have hcl : (z.toPerm.symm 0).val ≠ ρ.val.left.val := by
    intro h
    apply ρ.property.2.2.1
    rw [bottom_def, ← Fin.ext h, hz]
  have hcr : (z.toPerm.symm 0).val ≠ ρ.val.right.val := by
    intro h
    apply ρ.property.2.2.2
    rw [top_def, ← Fin.ext h, hz]
  have hnot := (isEmpty_iff_forall_notMem_cIoo ρ.val).mp ρ.property.1 (z.toPerm.symm 0)
  by_contra hh
  apply hnot
  · rw [Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨ρ.val.left_ne_right, by omega⟩
  · rw [hz, Grid.mem_cIoo, if_neg (by omega)]
    exact ⟨ρ.val.bottom_ne_top, Or.inr (by simp only [Fin.val_zero]; omega)⟩

/-- Outside the closed column interval, the source rows lie strictly between top and bottom. -/
theorem seamSecondRemaining_outside (ρ : SeamSecondRemainingRectangle x z w) (d : Fin (m + 1))
    (hd : d.val < ρ.val.right.val ∨ ρ.val.left.val < d.val) :
    ρ.val.top.val < (z d).val ∧ (z d).val < ρ.val.bottom.val := by
  obtain ⟨hcol, htop, hlt⟩ := seamSecondRemaining_rows x z w ρ
  have hcol' := Fin.lt_def.mp hcol
  have hdl : d ≠ ρ.val.left := by intro h; rw [h] at hd; omega
  have hdr : d ≠ ρ.val.right := by intro h; rw [h] at hd; omega
  have hnot := (isEmpty_iff_forall_notMem_cIoo ρ.val).mp ρ.property.1 d
    (by rw [Grid.mem_cIoo, if_neg (by omega)]; exact ⟨ρ.val.left_ne_right, by omega⟩)
  rw [Grid.mem_cIoo, if_neg (by omega)] at hnot
  have h1 : (z d).val ≠ ρ.val.bottom.val := fun h =>
    hdl (z.toPerm.injective (Fin.ext (h.trans (congrArg Fin.val (bottom_def ρ.val)))))
  have h2 : (z d).val ≠ ρ.val.top.val := fun h =>
    hdr (z.toPerm.injective (Fin.ext (h.trans (congrArg Fin.val (top_def ρ.val)))))
  simp only [ne_eq, ρ.val.bottom_ne_top, not_false_eq_true, true_and, not_or, not_lt] at hnot
  omega

end Remaining

/-- An empty wrapping factor rectangle with rows `0 < top < bottom` is a remaining rectangle
whenever the first block is nonempty. -/
theorem seamSecondRemaining_of_rows (x : GridState (n + 1)) {z w : GridState (m + 1)}
    (ρ : GridRectangleBetween z w) (he : ρ.IsEmpty) (hn : 0 < n)
    (hcol : ρ.right < ρ.left) (htop : 0 < ρ.top.val) (hlt : ρ.top.val < ρ.bottom.val) :
    ρ.IsEmpty ∧ ¬ (seamSecondFactorRectangle x ρ).IsEmpty ∧ ρ.bottom ≠ 0 ∧ ρ.top ≠ 0 := by
  have hb : ρ.bottom ≠ 0 := by
    intro h
    rw [h] at hlt
    exact Nat.not_lt_zero _ hlt
  have ht : ρ.top ≠ 0 := by
    intro h
    rw [h] at htop
    exact Nat.lt_irrefl 0 htop
  refine ⟨he, ?_, hb, ht⟩
  apply (seamSecondFactorRectangle_not_isEmpty_iff x ρ he).mpr
  refine ⟨⟨0, hn⟩, seamSecondShort_firstColumn_mem _ _ _ hcol, ?_⟩
  rw [seamSecondFactorRow_of_ne_zero x _ hb, seamSecondFactorRow_of_ne_zero x _ ht,
    Grid.mem_cIoo, if_neg (by simp only [seamRight_val]; omega)]
  refine ⟨fun h => ρ.bottom_ne_top (seamRight_injective h), Or.inr ?_⟩
  have hx := (x (Fin.castSucc (⟨0, hn⟩ : Fin n))).isLt
  simp only [seamLeft_val, seamRight_val]
  omega

section Frame
variable (x : GridState (n + 1)) (z w : GridState (m + 1))
  (ρ : SeamSecondRemainingRectangle x z w)

/-- The retained source row at the right side column. -/
theorem seamSecondShort_source_right :
    (seamState x z (seamRight n m ρ.val.right)).val = n + ρ.val.top.val := by
  rw [seamState_right_of_ne_zero x z _ ρ.property.2.2.2]
  rfl

/-- The retained source row at the left side column. -/
theorem seamSecondShort_source_left :
    (seamState x z (seamRight n m ρ.val.left)).val = n + ρ.val.bottom.val := by
  rw [seamState_right_of_ne_zero x z _ ρ.property.2.2.1]
  rfl

/-- The retained source row at the zero preimage column. -/
theorem seamSecondShort_source_zero :
    seamState x z (seamRight n m (z.toPerm.symm 0)) = seamLeft n m (x (Fin.last n)) :=
  seamState_right_of_zero x z _ (z.toPerm.apply_symm_apply 0)

/-- Outside the closed interval of side columns, every retained source row is at most `n` or
strictly between the two high endpoint rows. -/
theorem seamSecondShort_source_tame (c : Fin (n + m + 1))
    (hc : c.val < n + ρ.val.right.val ∨ n + ρ.val.left.val < c.val) :
    (seamState x z c).val ≤ n ∨
      (n + ρ.val.top.val < (seamState x z c).val ∧
        (seamState x z c).val < n + ρ.val.bottom.val) := by
  rcases seamColumn_cases_strict c with ⟨a, rfl⟩ | ⟨d, rfl⟩
  · left
    rw [seamState_left_castSucc, seamLeft_val]
    exact Nat.le_of_lt_succ (x a.castSucc).isLt
  · right
    simp only [seamRight_val] at hc
    have hd : d.val < ρ.val.right.val ∨ ρ.val.left.val < d.val := by omega
    obtain ⟨h1, h2⟩ := seamSecondRemaining_outside x z w ρ d hd
    have hz : z d ≠ 0 := by
      intro h
      rw [h] at h1
      exact Nat.not_lt_zero _ h1
    rw [seamState_right_of_ne_zero x z d hz, seamRight_val]
    omega

/-- The retained target is the swap of the source at the two side columns. -/
theorem seamSecondShort_target :
    seamState x w = (seamState x z).swapColumns (seamRight n m ρ.val.left)
      (seamRight n m ρ.val.right) :=
  (seamSecondFactorRectangle x ρ.val).target_eq_swapColumns

/-- Every low second-block row of the retained source lies in the zero preimage column. -/
theorem seamSecondShort_source_low (c : Fin (n + m + 1)) (hc : n ≤ c.val)
    (hv : (seamState x z c).val ≤ n) : c = seamRight n m (z.toPerm.symm 0) := by
  have hm : c ∈ seamSouthwestColumns (seamState x z) :=
    (mem_seamSouthwestColumns _ _).mpr ⟨hc, hv⟩
  rw [seamState_southwest_singleton] at hm
  exact Finset.mem_singleton.mp hm

/-- The coordinate facts about a remaining rectangle used by the explicit paths. -/
theorem seamSecondShort_frame :
    0 < n ∧ n ≤ (seamRight n m ρ.val.right).val ∧
      (seamRight n m ρ.val.right).val < (seamRight n m (z.toPerm.symm 0)).val ∧
      (seamRight n m (z.toPerm.symm 0)).val < (seamRight n m ρ.val.left).val ∧
      0 < ρ.val.top.val ∧ ρ.val.top.val < ρ.val.bottom.val ∧
      (seamState x z (seamRight n m ρ.val.right)).val = n + ρ.val.top.val ∧
      (seamState x z (seamRight n m ρ.val.left)).val = n + ρ.val.bottom.val ∧
      (seamState x z (seamRight n m (z.toPerm.symm 0))).val = (x (Fin.last n)).val ∧
      (∀ c : Fin (n + m + 1), c.val < (seamRight n m ρ.val.right).val ∨
          (seamRight n m ρ.val.left).val < c.val →
        (seamState x z c).val ≤ n ∨
          (n + ρ.val.top.val < (seamState x z c).val ∧
            (seamState x z c).val < n + ρ.val.bottom.val)) ∧
      (∀ c : Fin (n + m + 1), n ≤ c.val → (seamState x z c).val ≤ n →
        c = seamRight n m (z.toPerm.symm 0)) ∧
      seamState x w = (seamState x z).swapColumns (seamRight n m ρ.val.left)
        (seamRight n m ρ.val.right) := by
  have hzero := seamSecondRemaining_zero_between x z w ρ
  have hrows := seamSecondRemaining_rows x z w ρ
  refine ⟨seamSecondRemaining_pos x z w ρ, by simp only [seamRight_val]; omega,
    by simp only [seamRight_val]; omega, by simp only [seamRight_val]; omega, hrows.2.1,
    hrows.2.2, seamSecondShort_source_right x z w ρ, seamSecondShort_source_left x z w ρ,
    by rw [seamSecondShort_source_zero x z, seamLeft_val], ?_,
    seamSecondShort_source_low x z, seamSecondShort_target x z w ρ⟩
  intro c hc
  exact seamSecondShort_source_tame x z w ρ c (by simpa only [seamRight_val] using hc)

end Frame

/-- Values of a state after the two overlapping swaps `(a b)` and then `(b c)`. -/
theorem seamSecondShort_cycle_apply {k : ℕ} (s : GridState k) {a b c : Fin k}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (s.swapColumns a b).swapColumns b c a = s b ∧
      (s.swapColumns a b).swapColumns b c b = s c ∧
      (s.swapColumns a b).swapColumns b c c = s a ∧
      ∀ d, d ≠ a → d ≠ b → d ≠ c → (s.swapColumns a b).swapColumns b c d = s d := by
  simp only [GridState.swapColumns_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  · intro d ha hb hc
    rw [Equiv.swap_apply_of_ne_of_ne hb hc, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Values of a state after two disjoint swaps `(a b)` and then `(c d)`. -/
theorem seamSecondShort_doubleSwap_apply {k : ℕ} (s : GridState k) {a b c d : Fin k}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (s.swapColumns a b).swapColumns c d a = s b ∧
      (s.swapColumns a b).swapColumns c d b = s a ∧
      (s.swapColumns a b).swapColumns c d c = s d ∧
      (s.swapColumns a b).swapColumns c d d = s c ∧
      ∀ e, e ≠ a → e ≠ b → e ≠ c → e ≠ d → (s.swapColumns a b).swapColumns c d e = s e := by
  simp only [GridState.swapColumns_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne hbc hbd, Equiv.swap_apply_right]
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  · rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  · intro e ha hb hc hd
    rw [Equiv.swap_apply_of_ne_of_ne hc hd, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A first-block preimage of a row value other than the last row value. -/
theorem seamSecondShort_pivot_value (x : GridState (n + 1)) (z : GridState (m + 1))
    (a : Fin (n + 1)) (ha : x (Fin.last n) ≠ a) :
    (seamLeft n m (x.toPerm.symm a)).val < n ∧
      seamState x z (seamLeft n m (x.toPerm.symm a)) = seamLeft n m a := by
  have hlt := seamSecondShort_inverse_lt x a ha
  refine ⟨hlt, ?_⟩
  have hne : x.toPerm.symm a ≠ Fin.last n := by
    intro h
    rw [h] at hlt
    exact Nat.lt_irrefl n hlt
  rw [seamShortLift_seamState_left_ne_last x z _ hne]
  exact congrArg (seamLeft n m) (x.toPerm.apply_symm_apply a)

/-- The oriented rectangle with prescribed sides from a state to one of its column swaps.
Its sides are definitionally the prescribed columns. -/
def seamSecondShortRect {k : ℕ} {u v : GridState k} (a b : Fin k) (hab : a ≠ b)
    (h : v = u.swapColumns a b) : GridRectangleBetween u v where
  left := a
  right := b
  left_ne_right := hab
  map_left := by subst h; simp [GridState.swapColumns_apply]
  map_right := by subst h; simp [GridState.swapColumns_apply]
  map_of_ne c ha hb := by
    subst h
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne ha hb]

/-- A rectangle is empty if its column interior has only rows at most `n` or in `[K, H]`, and
its row interior is the rows above `H` or the rows strictly between `n` and `K`. -/
theorem seamSecondShort_isEmpty {k : ℕ} {u v : GridState k} (R : GridRectangleBetween u v)
    (K H : ℕ) (hnK : n < K) (hKH : K < H)
    (hrows : (R.bottom.val = H ∧ R.top.val = 0) ∨ (R.bottom.val = n ∧ R.top.val = K))
    (htame : ∀ c ∈ Grid.cIoo R.left R.right,
      (u c).val ≤ n ∨ (K ≤ (u c).val ∧ (u c).val ≤ H)) : R.IsEmpty := by
  apply (isEmpty_iff_forall_notMem_cIoo R).mpr
  intro c hc hrow
  have ht := htame c hc
  rw [Grid.mem_cIoo] at hrow
  have h2 := hrow.2
  rcases hrows with ⟨hb, htp⟩ | ⟨hb, htp⟩
  · rw [hb, htp, if_neg (by omega)] at h2
    omega
  · rw [hb, htp, if_pos (by omega)] at h2
    omega

/-- The first two of three increasing southwest columns are the selected pair. -/
theorem seamSecondShort_first_of_triple (v : SeamComplement n m) (P Q S : Fin (n + m + 1))
    (hs : seamSouthwestColumns v.val = {P, Q, S}) (hPQ : P < Q) (hQS : Q < S) :
    seamComplementFirst v = P ∧ seamComplementSecond v = Q := by
  have hfirst : seamComplementFirst v = P := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hs]
    refine ⟨by simp, ?_⟩
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl
    · exact le_rfl
    · exact hPQ.le
    · exact (hPQ.trans hQS).le
  refine ⟨hfirst, ?_⟩
  apply (Finset.min'_eq_iff _ _ _).mpr
  rw [hfirst, hs]
  refine ⟨Finset.mem_erase.mpr ⟨hPQ.ne.symm, by simp⟩, ?_⟩
  intro b hb
  obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | rfl | rfl
  · exact False.elim (hne h)
  · exact le_rfl
  · exact hQS.le

/-- A matching source with three southwest columns and increasing first two rows. -/
def seamSecondShort_sourceOfTriple (w : GridState (n + m + 1)) (P Q S : Fin (n + m + 1))
    (hs : seamSouthwestColumns w = {P, Q, S}) (hPQ : P < Q) (hQS : Q < S)
    (hrows : (w P).val < (w Q).val) : SeamMatchingSource n m := by
  have hcomp : ¬ SeamPairSector w := not_pairSector_of_two_le_southwest_card w (by
    rw [hs]
    calc 2 = ({P, Q} : Finset (Fin (n + m + 1))).card := (Finset.card_pair hPQ.ne).symm
      _ ≤ _ := Finset.card_le_card (by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc ⊢
        tauto))
  let v : SeamComplement n m := ⟨w, hcomp⟩
  refine ⟨v, ?_⟩
  change (w (seamComplementFirst v)).val < (w (seamComplementSecond v)).val
  obtain ⟨h1, h2⟩ := seamSecondShort_first_of_triple v P Q S hs hPQ hQS
  rw [h1, h2]
  exact hrows

/-- The matching target of a three-column source swaps its first two southwest columns. -/
theorem seamSecondShort_sourceOfTriple_partner (w : GridState (n + m + 1))
    (P Q S : Fin (n + m + 1)) (hs : seamSouthwestColumns w = {P, Q, S}) (hPQ : P < Q)
    (hQS : Q < S) (hrows : (w P).val < (w Q).val) :
    (seamComplementPartner (seamSecondShort_sourceOfTriple w P Q S hs hPQ hQS hrows).val).val =
      w.swapColumns P Q := by
  change w.swapColumns (seamComplementFirst _) (seamComplementSecond _) = _
  obtain ⟨h1, h2⟩ := seamSecondShort_first_of_triple
    (seamSecondShort_sourceOfTriple w P Q S hs hPQ hQS hrows).val P Q S hs hPQ hQS
  rw [h1, h2]

/-- A one-transition correction path from its three rectangles. -/
def seamSecondShortPathOne {p q : SeamRetainedIndex n m} (s₀ s₁ : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s₀.val).val)
    (he : e.IsEmpty)
    (r : GridRectangleBetween s₀.val.val (seamComplementPartner s₁.val).val)
    (h₀₁ : s₀ ≠ s₁) (hr : r.IsEmpty)
    (f : GridRectangleBetween s₁.val.val (seamState q.1 q.2)) (hf : f.IsEmpty) :
    SeamCorrectionPath 1 p q :=
  ⟨s₀, s₁, ⟨e, he⟩, ⟨s₁, ⟨r, h₀₁, hr⟩, ⟨(), rfl⟩⟩, ⟨f, hf⟩⟩

/-- A two-transition correction path from its four rectangles. -/
def seamSecondShortPathTwo {p q : SeamRetainedIndex n m} (s₀ s₁ s₂ : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner s₀.val).val)
    (he : e.IsEmpty)
    (r : GridRectangleBetween s₀.val.val (seamComplementPartner s₁.val).val)
    (h₀₁ : s₀ ≠ s₁) (hr : r.IsEmpty)
    (t : GridRectangleBetween s₁.val.val (seamComplementPartner s₂.val).val)
    (h₁₂ : s₁ ≠ s₂) (ht : t.IsEmpty)
    (f : GridRectangleBetween s₂.val.val (seamState q.1 q.2)) (hf : f.IsEmpty) :
    SeamCorrectionPath 2 p q :=
  ⟨s₀, s₂, ⟨e, he⟩, ⟨s₁, ⟨r, h₀₁, hr⟩, ⟨s₂, ⟨t, h₁₂, ht⟩, ⟨(), rfl⟩⟩⟩, ⟨f, hf⟩⟩

/-- A one-transition correction path is determined by the sides of its three rectangles. -/
theorem seamSecondShortPathOne_ext {p q : SeamRetainedIndex n m}
    (a b : SeamCorrectionPath 1 p q)
    (heL : a.2.2.1.val.left = b.2.2.1.val.left)
    (heR : a.2.2.1.val.right = b.2.2.1.val.right)
    (hrL : a.2.2.2.1.2.1.val.left = b.2.2.2.1.2.1.val.left)
    (hrR : a.2.2.2.1.2.1.val.right = b.2.2.2.1.2.1.val.right)
    (hfL : a.2.2.2.2.val.left = b.2.2.2.2.val.left)
    (hfR : a.2.2.2.2.val.right = b.2.2.2.2.val.right) : a = b := by
  rcases a with ⟨x, y, e, ⟨y₁, r, ⟨⟨⟩, hy⟩⟩, f⟩
  rcases b with ⟨x', y', e', ⟨y₁', r', ⟨⟨⟩, hy'⟩⟩, f'⟩
  dsimp only at heL heR hrL hrR hfL hfR
  have hy₁ : y₁ = y := hy
  have hy₁' : y₁' = y' := hy'
  subst hy₁
  subst hy₁'
  have hx : x = x' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [e.val.target_eq_swapColumns, e'.val.target_eq_swapColumns]
    rw [heL, heR]
  have hyy : y₁ = y₁' := by
    apply Subtype.ext
    apply Subtype.ext
    rw [f.val.source_eq_swapColumns, f'.val.source_eq_swapColumns]
    rw [hfL, hfR]
  subst hx
  subst hyy
  have he : e = e' := Subtype.ext (GridRectangleBetween.ext heL heR)
  have hr : r = r' := Subtype.ext (GridRectangleBetween.ext hrL hrR)
  have hf : f = f' := Subtype.ext (GridRectangleBetween.ext hfL hfR)
  subst he
  subst hr
  subst hf
  rfl

/-- A two-transition correction path is determined by the sides of its four rectangles. -/
theorem seamSecondShortPathTwo_ext {p q : SeamRetainedIndex n m}
    (a b : SeamCorrectionPath 2 p q)
    (heL : a.2.2.1.val.left = b.2.2.1.val.left)
    (heR : a.2.2.1.val.right = b.2.2.1.val.right)
    (hrL : a.2.2.2.1.2.1.val.left = b.2.2.2.1.2.1.val.left)
    (hrR : a.2.2.2.1.2.1.val.right = b.2.2.2.1.2.1.val.right)
    (htL : a.2.2.2.1.2.2.2.1.val.left = b.2.2.2.1.2.2.2.1.val.left)
    (htR : a.2.2.2.1.2.2.2.1.val.right = b.2.2.2.1.2.2.2.1.val.right)
    (hfL : a.2.2.2.2.val.left = b.2.2.2.2.val.left)
    (hfR : a.2.2.2.2.val.right = b.2.2.2.2.val.right) : a = b := by
  rcases a with ⟨x, z, e, ⟨y, r, ⟨z₁, t, ⟨⟨⟩, hz⟩⟩⟩, f⟩
  rcases b with ⟨x', z', e', ⟨y', r', ⟨z₁', t', ⟨⟨⟩, hz'⟩⟩⟩, f'⟩
  dsimp only at heL heR hrL hrR htL htR hfL hfR
  have hz₁ : z₁ = z := hz
  have hz₁' : z₁' = z' := hz'
  subst hz₁
  subst hz₁'
  have hx : x = x' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [e.val.target_eq_swapColumns, e'.val.target_eq_swapColumns]
    rw [heL, heR]
  have hzz : z₁ = z₁' := by
    apply Subtype.ext
    apply Subtype.ext
    rw [f.val.source_eq_swapColumns, f'.val.source_eq_swapColumns]
    rw [hfL, hfR]
  subst hx
  subst hzz
  have hyy : y = y' := by
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    apply Subtype.ext
    rw [r.val.target_eq_swapColumns, r'.val.target_eq_swapColumns]
    rw [hrL, hrR]
  subst hyy
  have he : e = e' := Subtype.ext (GridRectangleBetween.ext heL heR)
  have hr : r = r' := Subtype.ext (GridRectangleBetween.ext hrL hrR)
  have ht : t = t' := Subtype.ext (GridRectangleBetween.ext htL htR)
  have hf : f = f' := Subtype.ext (GridRectangleBetween.ext hfL hfR)
  subst he
  subst hr
  subst ht
  subst hf
  rfl

end OnLeConjecture.KnotFloer.GridFull
