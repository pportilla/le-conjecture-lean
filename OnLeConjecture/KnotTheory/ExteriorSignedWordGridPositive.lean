/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.ExteriorSignedWordGrid
public import OnLeConjecture.KnotTheory.PositiveWordGridAdmissible
public import OnLeConjecture.KnotFloer.GridConnectedSumIterated

/-!
# Admissible positive word grids are signed word grids

The base case of `SignedWordGridRelationsStatement` (written proof of Statement E,
`statement_E_complete_proof.tex`, Section 7): the selected grid `wordGrid w` of a positive word,
and more generally every grid admissible for `w` in the sense of `IsAdmissibleWordGrid`, is a
signed word grid of `w.toSigned` (`isSignedWordGrid_of_isAdmissibleWordGrid`), after the cast of
its size along `w.toSigned.length = w.length`.

The heights agree: the arc row `w[j] + (1/2, 0, 1)_c` of the admissible convention is half the
doubled outgoing height of the signed convention, and similarly for incoming corners. The only
point to check is that the horizontal matching of the admissible convention, a sorted cyclic
successor on the occurrences of each rank, joins every incoming corner to the nearest outgoing
corner of the same height on its left (`positiveMatching_symm_gap_le`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

variable {m : ℕ}

/-! ### Cyclic gaps -/

theorem cyclicGap_of_lt {L a b : ℕ} (hab : a < b) (hb : b < L) :
    (b + L - a) % L = b - a := by
  rw [show b + L - a = (b - a) + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem cyclicGap_of_gt {L a b : ℕ} (hba : b < a) (ha : a < L) :
    (b + L - a) % L = b + L - a :=
  Nat.mod_eq_of_lt (by omega)

/-! ### Heights of a positive word -/

/-- The doubled outgoing height of a corner of a positive word. -/
def posOHeight2 (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3) : ℕ :=
  ![2 * w[p.1.val].val + 1, 2 * w[p.1.val].val, 2 * w[p.1.val].val + 2] p.2

/-- The doubled incoming height of a corner of a positive word. -/
def posXHeight2 (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3) : ℕ :=
  ![2 * w[p.1.val].val, 2 * w[p.1.val].val + 2, 2 * w[p.1.val].val + 1] p.2

theorem arcRow_eq_posOHeight2 (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3) :
    positiveRectilinearWordArcRow w p = (posOHeight2 w p : ℝ) / 2 := by
  rcases p with ⟨j, c⟩
  rw [positiveRectilinearWordArcRow_eq]
  fin_cases c <;> simp [posOHeight2] <;> ring

theorem xCornerRow_eq_posXHeight2 (w : PositiveAdjacentWord m) (p : Fin w.length × Fin 3) :
    (positiveRectilinearWordXCorner w p.1 p.2).2 = (posXHeight2 w p : ℝ) / 2 := by
  rcases p with ⟨j, c⟩
  simp only [positiveRectilinearWordXCorner]
  fin_cases c <;>
    norm_num [posXHeight2, positiveGridRectilinearRows, positiveGridRectilinearDiagram,
      Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val_two] <;> ring

theorem posOHeight2_lt_iff (w : PositiveAdjacentWord m) (p q : Fin w.length × Fin 3) :
    posOHeight2 w p < posOHeight2 w q ↔
      positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q := by
  rw [arcRow_eq_posOHeight2, arcRow_eq_posOHeight2, div_lt_div_iff_of_pos_right (by norm_num)]
  exact_mod_cast Iff.rfl

theorem posOHeight2_matching_symm (w : PositiveAdjacentWord m) (q : Fin w.length × Fin 3) :
    posOHeight2 w ((positiveRectilinearWordMatching w).symm q) = posXHeight2 w q := by
  have h := positiveRectilinearWordArcRow_incoming w q
  rw [arcRow_eq_posOHeight2, xCornerRow_eq_posXHeight2] at h
  have h2 : (posOHeight2 w ((positiveRectilinearWordMatching w).symm q) : ℝ) =
      posXHeight2 w q := by linarith
  exact_mod_cast h2

/-! ### The matching joins nearest corners -/

/-- The cyclic distance from the column of `p` to the column of `q`. -/
def posGap (w : PositiveAdjacentWord m) (p q : Fin w.length × Fin 3) : ℕ :=
  ((finProdFinEquiv q).val + w.length * 3 - (finProdFinEquiv p).val) % (w.length * 3)

theorem finProdFinEquiv_val3 {L : ℕ} (p : Fin L × Fin 3) :
    (finProdFinEquiv p).val = p.2.val + 3 * p.1.val := by
  simp [finProdFinEquiv_apply_val]

/-- The column of the outgoing corner of an occurrence of the rank `r`. -/
def outCol (w : PositiveAdjacentWord m) (r : Fin m) (o : Fin w.length) : ℕ :=
  3 * o.val + if r = adjacentLower w[o.val] then 1 else 2

theorem outgoingArc_symm_inr (w : PositiveAdjacentWord m) (r : Fin m)
    (o : PositiveRectilinearRowOccurrences w r) :
    (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, o⟩) =
      (o.val, if r = adjacentLower w[o.val.val] then 1 else 2) := rfl

theorem incomingArc_symm_lower (w : PositiveAdjacentWord m) (j : Fin w.length) :
    (positiveRectilinearIncomingArc w).symm
        (Sum.inr ⟨adjacentLower w[j.val], ⟨j, Or.inl rfl⟩⟩) = (j, 0) := by
  apply (positiveRectilinearIncomingArc w).injective
  rw [Equiv.apply_symm_apply, positiveRectilinearIncomingArc_zero]

theorem incomingArc_symm_upper (w : PositiveAdjacentWord m) (j : Fin w.length) :
    (positiveRectilinearIncomingArc w).symm
        (Sum.inr ⟨adjacentUpper w[j.val], ⟨j, Or.inr rfl⟩⟩) = (j, 1) := by
  apply (positiveRectilinearIncomingArc w).injective
  rw [Equiv.apply_symm_apply, positiveRectilinearIncomingArc_one]

theorem adjacentLower_ne_adjacentUpper' (i : Fin (m - 1)) :
    adjacentLower i ≠ adjacentUpper i := by
  intro h
  have := congrArg Fin.val h
  simp at this

/-- An outgoing corner of doubled height `2 r` is the outgoing corner of an occurrence of `r`. -/
theorem eq_outgoing_of_posOHeight2 (w : PositiveAdjacentWord m) (r : Fin m)
    (p : Fin w.length × Fin 3) (hp : posOHeight2 w p = 2 * r.val) :
    ∃ h : r = adjacentLower w[p.1.val] ∨ r = adjacentUpper w[p.1.val],
      p = (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, ⟨p.1, h⟩⟩) := by
  rcases p with ⟨j, c⟩
  fin_cases c
  · simp [posOHeight2] at hp
    omega
  · have hr : r = adjacentLower w[j.val] := Fin.ext (by simp [posOHeight2] at hp; simp; omega)
    refine ⟨Or.inl hr, ?_⟩
    rw [outgoingArc_symm_inr]
    simp [hr]
  · have hr : r = adjacentUpper w[j.val] := Fin.ext (by simp [posOHeight2] at hp; simp; omega)
    refine ⟨Or.inr hr, ?_⟩
    rw [outgoingArc_symm_inr]
    have hne : r ≠ adjacentLower w[j.val] := by
      rw [hr]; exact (adjacentLower_ne_adjacentUpper' _).symm
    simp [hne]

theorem outCol_lt (w : PositiveAdjacentWord m) (r : Fin m) {o₁ o₂ : Fin w.length}
    (h : o₁ < o₂) : outCol w r o₁ < outCol w r o₂ := by
  have : o₁.val < o₂.val := h
  unfold outCol
  split_ifs <;> omega

theorem outCol_lt_size (w : PositiveAdjacentWord m) (r : Fin m) (o : Fin w.length) :
    outCol w r o < w.length * 3 := by
  have := o.isLt
  unfold outCol
  split_ifs <;> omega

theorem positiveMatching_symm_gap_le_zero (w : PositiveAdjacentWord m) (j : Fin w.length)
    (p : Fin w.length × Fin 3) (hp : posOHeight2 w p = posXHeight2 w (j, 0)) :
    posGap w ((positiveRectilinearWordMatching w).symm (j, 0)) (j, 0) ≤ posGap w p (j, 0) := by
  classical
  have hjL := j.isLt
  set r := adjacentLower w[j.val] with hr
  let oj : PositiveRectilinearRowOccurrences w r := ⟨j, Or.inl rfl⟩
  set j₀ := (positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r)).symm oj
    with hj₀
  have hsucc : positiveRectilinearSortedSuccessor _ j₀ = oj := by rw [hj₀]; simp
  have hM : (positiveRectilinearWordMatching w).symm (j, 0) =
      (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, j₀⟩) := by
    rw [Equiv.symm_apply_eq, positiveRectilinearWordMatching_occurrence, hsucc]
    exact (incomingArc_symm_lower w j).symm
  have hpq : posOHeight2 w p = 2 * r.val := by rw [hp]; simp [posXHeight2, hr]
  obtain ⟨hocc, hpe⟩ := eq_outgoing_of_posOHeight2 w r p hpq
  set o' : PositiveRectilinearRowOccurrences w r := ⟨p.1, hocc⟩ with ho'
  have hcolq : (finProdFinEquiv ((j, 0) : Fin w.length × Fin 3)).val = 3 * j.val := by
    rw [finProdFinEquiv_val3]; simp
  have hcol : ∀ o : PositiveRectilinearRowOccurrences w r,
      (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, o⟩))).val =
        outCol w r o.val := by
    intro o
    rw [outgoingArc_symm_inr, finProdFinEquiv_val3, outCol]
    split_ifs <;> simp <;> ring
  have hinj : outCol w r j = 3 * j.val + 1 := by simp [outCol, hr]
  rw [hM, hpe]
  unfold posGap
  rw [hcolq, hcol, hcol]
  have hsize₀ := outCol_lt_size w r j₀.val
  have hsize' := outCol_lt_size w r o'.val
  rcases positiveRectilinearSortedSuccessor_next _ j₀ with ⟨hlt, hleast⟩ | ⟨hle, hall⟩
  · rw [hsucc] at hlt hleast
    have hlt' : j₀.val < j := hlt
    have h0 : outCol w r j₀.val < 3 * j.val := by
      have := hlt'; unfold outCol; split_ifs <;> omega
    rw [cyclicGap_of_lt h0 (by omega)]
    by_cases hoj : o'.val < j
    · have hle' : o'.val ≤ j₀.val := by
        by_contra hcon
        have := hleast o' (lt_of_not_ge hcon)
        exact absurd (this : j ≤ o'.val) (not_le_of_gt hoj)
      have h1 : outCol w r o'.val ≤ outCol w r j₀.val := by
        rcases lt_or_eq_of_le hle' with h | h
        · exact (outCol_lt w r h).le
        · rw [h]
      have h2 : outCol w r o'.val < 3 * j.val := lt_of_le_of_lt h1 h0
      rw [cyclicGap_of_lt h2 (by omega)]
      omega
    · have h1 : 3 * j.val < outCol w r o'.val := by
        rcases lt_or_eq_of_le (not_lt.mp hoj) with h | h
        · have := outCol_lt w r h; omega
        · rw [← h]; omega
      rw [cyclicGap_of_gt h1 hsize']
      omega
  · rw [hsucc] at hle hall
    have hle' : j ≤ j₀.val := hle
    have h0 : 3 * j.val < outCol w r j₀.val := by
      have : j.val ≤ j₀.val.val := hle'; unfold outCol; split_ifs <;> omega
    rw [cyclicGap_of_gt h0 hsize₀]
    obtain ⟨hlo, hhi⟩ := hall o'
    have hlo' : j ≤ o'.val := hlo
    have hhi' : o'.val ≤ j₀.val := hhi
    have h1 : 3 * j.val < outCol w r o'.val := by
      have : j.val ≤ o'.val.val := hlo'; unfold outCol; split_ifs <;> omega
    have h2 : outCol w r o'.val ≤ outCol w r j₀.val := by
      rcases lt_or_eq_of_le hhi' with h | h
      · exact (outCol_lt w r h).le
      · rw [h]
    rw [cyclicGap_of_gt h1 hsize']
    omega

theorem positiveMatching_symm_gap_le_one (w : PositiveAdjacentWord m) (j : Fin w.length)
    (p : Fin w.length × Fin 3) (hp : posOHeight2 w p = posXHeight2 w (j, 1)) :
    posGap w ((positiveRectilinearWordMatching w).symm (j, 1)) (j, 1) ≤ posGap w p (j, 1) := by
  classical
  have hjL := j.isLt
  set r := adjacentUpper w[j.val] with hr
  let oj : PositiveRectilinearRowOccurrences w r := ⟨j, Or.inr rfl⟩
  set j₀ := (positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r)).symm oj
    with hj₀
  have hsucc : positiveRectilinearSortedSuccessor _ j₀ = oj := by rw [hj₀]; simp
  have hM : (positiveRectilinearWordMatching w).symm (j, 1) =
      (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, j₀⟩) := by
    rw [Equiv.symm_apply_eq, positiveRectilinearWordMatching_occurrence, hsucc]
    exact (incomingArc_symm_upper w j).symm
  have hpq : posOHeight2 w p = 2 * r.val := by rw [hp]; simp [posXHeight2, hr]; ring
  obtain ⟨hocc, hpe⟩ := eq_outgoing_of_posOHeight2 w r p hpq
  set o' : PositiveRectilinearRowOccurrences w r := ⟨p.1, hocc⟩ with ho'
  have hcolq : (finProdFinEquiv ((j, 1) : Fin w.length × Fin 3)).val = 3 * j.val + 1 := by
    rw [finProdFinEquiv_val3]; simp; ring
  have hcol : ∀ o : PositiveRectilinearRowOccurrences w r,
      (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, o⟩))).val =
        outCol w r o.val := by
    intro o
    rw [outgoingArc_symm_inr, finProdFinEquiv_val3, outCol]
    split_ifs <;> simp <;> ring
  have hinj : outCol w r j = 3 * j.val + 2 := by
    have hne : r ≠ adjacentLower w[j.val] := by
      rw [hr]; exact (adjacentLower_ne_adjacentUpper' _).symm
    simp [outCol, hne]
  rw [hM, hpe]
  unfold posGap
  rw [hcolq, hcol, hcol]
  have hsize₀ := outCol_lt_size w r j₀.val
  have hsize' := outCol_lt_size w r o'.val
  rcases positiveRectilinearSortedSuccessor_next _ j₀ with ⟨hlt, hleast⟩ | ⟨hle, hall⟩
  · rw [hsucc] at hlt hleast
    have hlt' : j₀.val < j := hlt
    have h0 : outCol w r j₀.val < 3 * j.val + 1 := by
      have := hlt'; unfold outCol; split_ifs <;> omega
    rw [cyclicGap_of_lt h0 (by omega)]
    by_cases hoj : o'.val < j
    · have hle' : o'.val ≤ j₀.val := by
        by_contra hcon
        have := hleast o' (lt_of_not_ge hcon)
        exact absurd (this : j ≤ o'.val) (not_le_of_gt hoj)
      have h1 : outCol w r o'.val ≤ outCol w r j₀.val := by
        rcases lt_or_eq_of_le hle' with h | h
        · exact (outCol_lt w r h).le
        · rw [h]
      have h2 : outCol w r o'.val < 3 * j.val + 1 := lt_of_le_of_lt h1 h0
      rw [cyclicGap_of_lt h2 (by omega)]
      omega
    · have h1 : 3 * j.val + 1 < outCol w r o'.val := by
        rcases lt_or_eq_of_le (not_lt.mp hoj) with h | h
        · have := outCol_lt w r h; omega
        · rw [← h]; omega
      rw [cyclicGap_of_gt h1 hsize']
      omega
  · rw [hsucc] at hle hall
    have hle' : j ≤ j₀.val := hle
    have h0 : 3 * j.val + 1 < outCol w r j₀.val := by
      rcases lt_or_eq_of_le hle' with h | h
      · have := outCol_lt w r h; omega
      · rw [← h]; omega
    rw [cyclicGap_of_gt h0 hsize₀]
    obtain ⟨hlo, hhi⟩ := hall o'
    have hlo' : j ≤ o'.val := hlo
    have hhi' : o'.val ≤ j₀.val := hhi
    have h1 : 3 * j.val + 1 < outCol w r o'.val := by
      rcases lt_or_eq_of_le hlo' with h | h
      · have := outCol_lt w r h; omega
      · rw [← h]; omega
    have h2 : outCol w r o'.val ≤ outCol w r j₀.val := by
      rcases lt_or_eq_of_le hhi' with h | h
      · exact (outCol_lt w r h).le
      · rw [h]
    rw [cyclicGap_of_gt h1 hsize']
    omega

theorem posOHeight2_one (w : PositiveAdjacentWord m) (j : Fin w.length) :
    posOHeight2 w (j, 1) = 2 * w[j.val].val := rfl

theorem posOHeight2_two (w : PositiveAdjacentWord m) (j : Fin w.length) :
    posOHeight2 w (j, 2) = 2 * w[j.val].val + 2 := rfl

theorem posXHeight2_two (w : PositiveAdjacentWord m) (j : Fin w.length) :
    posXHeight2 w (j, 2) = 2 * w[j.val].val + 1 := rfl

theorem positiveMatching_symm_gap_le_two (w : PositiveAdjacentWord m) (j : Fin w.length)
    (p : Fin w.length × Fin 3) (hp : posOHeight2 w p = posXHeight2 w (j, 2)) :
    posGap w ((positiveRectilinearWordMatching w).symm (j, 2)) (j, 2) ≤ posGap w p (j, 2) := by
  have hjL := j.isLt
  have hM : (positiveRectilinearWordMatching w).symm (j, 2) = (j, 0) := by
    rw [Equiv.symm_apply_eq, positiveRectilinearWordMatching_middle]
  rw [hM]
  rcases p with ⟨j', c'⟩
  rw [posXHeight2_two] at hp
  have hc' : c' = 0 := by
    fin_cases c'
    · rfl
    · exfalso
      change posOHeight2 w (j', 1) = _ at hp
      rw [posOHeight2_one] at hp
      omega
    · exfalso
      change posOHeight2 w (j', 2) = _ at hp
      rw [posOHeight2_two] at hp
      omega
  subst hc'
  have hj'L := j'.isLt
  unfold posGap
  simp only [finProdFinEquiv_val3, Fin.isValue, Fin.val_two, Fin.val_zero]
  rw [cyclicGap_of_lt (by omega) (by omega)]
  rcases lt_trichotomy j'.val j.val with h | h | h
  · rw [cyclicGap_of_lt (by omega) (by omega)]; omega
  · rw [cyclicGap_of_lt (by omega) (by omega)]; omega
  · rw [cyclicGap_of_gt (by omega) (by omega)]; omega

/-- The horizontal matching joins every incoming corner to the nearest outgoing corner of the same
height on its left. -/
theorem positiveMatching_symm_gap_le (w : PositiveAdjacentWord m) (q p : Fin w.length × Fin 3)
    (hp : posOHeight2 w p = posXHeight2 w q) :
    posGap w ((positiveRectilinearWordMatching w).symm q) q ≤ posGap w p q := by
  rcases q with ⟨j, c⟩
  fin_cases c
  · exact positiveMatching_symm_gap_le_zero w j p hp
  · exact positiveMatching_symm_gap_le_one w j p hp
  · exact positiveMatching_symm_gap_le_two w j p hp

/-! ### Transfer to the signed convention -/

theorem gridCast_O_val {n n' : ℕ} (h : n = n') (G : GridDiagram n) (i : Fin n') :
    ((KnotFloer.GridFull.gridCast h G).O i).val = (G.O (Fin.cast h.symm i)).val := by
  subst h
  rfl

theorem gridCast_X_val {n n' : ℕ} (h : n = n') (G : GridDiagram n) (i : Fin n') :
    ((KnotFloer.GridFull.gridCast h G).X i).val = (G.X (Fin.cast h.symm i)).val := by
  subst h
  rfl

theorem length_toSigned (w : PositiveAdjacentWord m) : w.toSigned.length = w.length :=
  List.length_map _

theorem toSigned_getElem (w : PositiveAdjacentWord m) (j : Fin w.toSigned.length) :
    w.toSigned[j.val] = (w[j.val]'(by rw [← length_toSigned]; exact j.isLt), 1) := by
  simp [PositiveAdjacentWord.toSigned]

/-- The corners of `w.toSigned` as corners of `w`. -/
def toSignedCorner (w : PositiveAdjacentWord m) (p : Fin w.toSigned.length × Fin 3) :
    Fin w.length × Fin 3 :=
  (Fin.cast (length_toSigned w) p.1, p.2)

theorem oHeight2_toSigned (w : PositiveAdjacentWord m) (p : Fin w.toSigned.length × Fin 3) :
    w.toSigned.oHeight2 p = posOHeight2 w (toSignedCorner w p) := by
  simp only [SignedAdjacentWord.oHeight2, toSigned_getElem, signedOHeight2, if_true,
    posOHeight2, toSignedCorner, Fin.val_cast]

theorem xHeight2_toSigned (w : PositiveAdjacentWord m) (p : Fin w.toSigned.length × Fin 3) :
    w.toSigned.xHeight2 p = posXHeight2 w (toSignedCorner w p) := by
  simp only [SignedAdjacentWord.xHeight2, toSigned_getElem, signedXHeight2, if_true,
    posXHeight2, toSignedCorner, Fin.val_cast]

theorem finProdFinEquiv_toSignedCorner (w : PositiveAdjacentWord m)
    (p : Fin w.toSigned.length × Fin 3) :
    (finProdFinEquiv (toSignedCorner w p)).val = (finProdFinEquiv p).val := by
  simp [toSignedCorner]

theorem cornerGap_toSigned (w : PositiveAdjacentWord m) (p q : Fin w.toSigned.length × Fin 3) :
    w.toSigned.cornerGap p q = posGap w (toSignedCorner w p) (toSignedCorner w q) := by
  simp only [SignedAdjacentWord.cornerGap, posGap, finProdFinEquiv_toSignedCorner,
    length_toSigned]

theorem toSignedCorner_surjective (w : PositiveAdjacentWord m) :
    Function.Surjective (toSignedCorner w) := by
  intro p
  exact ⟨(Fin.cast (length_toSigned w).symm p.1, p.2), by simp [toSignedCorner]⟩

theorem size_toSigned (w : PositiveAdjacentWord m) : w.length * 3 = w.toSigned.length * 3 := by
  rw [length_toSigned]

/-- **Admissible positive grids are signed word grids.** -/
theorem isSignedWordGrid_of_isAdmissibleWordGrid (w : PositiveAdjacentWord m)
    (G : GridDiagram (w.length * 3)) (hG : IsAdmissibleWordGrid w G) :
    IsSignedWordGrid w.toSigned (KnotFloer.GridFull.gridCast (size_toSigned w) G) := by
  have hO : ∀ p : Fin w.toSigned.length × Fin 3,
      ((KnotFloer.GridFull.gridCast (size_toSigned w) G).O (finProdFinEquiv p)).val =
        (G.O (finProdFinEquiv (toSignedCorner w p))).val := by
    intro p
    rw [gridCast_O_val]
    congr 2
  have hX : ∀ p : Fin w.toSigned.length × Fin 3,
      ((KnotFloer.GridFull.gridCast (size_toSigned w) G).X (finProdFinEquiv p)).val =
        (G.X (finProdFinEquiv (toSignedCorner w p))).val := by
    intro p
    rw [gridCast_X_val]
    congr 2
  refine ⟨fun p q hpq => ?_, fun q => ?_⟩
  · rw [oHeight2_toSigned, oHeight2_toSigned, posOHeight2_lt_iff] at hpq
    have := hG.O_lt_of_arcRow_lt _ _ hpq
    rw [Fin.lt_def, hO, hO]
    exact this
  · obtain ⟨p, hp⟩ := toSignedCorner_surjective w
      ((positiveRectilinearWordMatching w).symm (toSignedCorner w q))
    refine ⟨p, ?_, fun p' hp' => ?_, ?_⟩
    · rw [oHeight2_toSigned, xHeight2_toSigned, hp, posOHeight2_matching_symm]
    · rw [cornerGap_toSigned, cornerGap_toSigned, hp]
      rw [oHeight2_toSigned, xHeight2_toSigned] at hp'
      exact positiveMatching_symm_gap_le w _ _ hp'
    · apply Fin.ext
      rw [hX, hO, hp, hG.X_eq]

/-- The selected word grid is a signed word grid of the positive word. -/
theorem isSignedWordGrid_wordGrid (w : PositiveAdjacentWord m) :
    IsSignedWordGrid w.toSigned (KnotFloer.GridFull.gridCast (size_toSigned w) (wordGrid w)) :=
  isSignedWordGrid_of_isAdmissibleWordGrid w _ (wordGrid_isAdmissible w)

end OnLeConjecture.KnotTheory
