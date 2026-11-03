/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridAdmissibleDeletion
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Diagram.Components
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # The number of components of a word grid

Let `w` be a positive word of length `L` on `m` strands. The component permutation of an
admissible grid of `w` is the horizontal matching `M = positiveRectilinearWordMatching w` of the
corners of `w`, transported to the native columns by `finProdFinEquiv`
(`IsAdmissibleWordGrid.componentPerm_eq`). Hence the number of components of the grid is the
number of orbits of `M` (`IsAdmissibleWordGrid.componentCount_eq`).

Each corner carries the label of the strand passing through it
(`positiveRectilinearCornerLabel`): the label of the corner `(h, c)` is the initial position of
the strand which, after the first `h` letters, lies at the lower rank of letter `h` (for `c = 0`
and `c = 2`) or at its upper rank (for `c = 1`). Following one arc either keeps the label and
moves to a later column, or it is the arc from the last occurrence of a rank `r` to its first
occurrence, and then it replaces the label `π r` by `r`, where `π` is the permutation of `w`.

When every rank occurs, the labels identify the orbits of `M` with the orbits of `π`
(`positiveRectilinearWordMatching_sameCycle_iff`). This proves record M414 of the dependency
audit (`wordGrid_componentCount`): the number of components of the word grid equals the number
of cycles of the word permutation, fixed points included. The written proof is Section 2 of
`docs/route-n/J09-word-grid-moves.tex`. All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti Equiv

/-- If a surjection `F` identifies the relation `SameCycle σ` with the pullback of
`SameCycle τ`, then `σ` and `τ` have the same number of orbits. -/
theorem orbitCount_eq_of_sameCycle_iff {α β : Type*} {σ : Perm α} {τ : Perm β} (F : α → β)
    (hF : Function.Surjective F) (h : ∀ x y, σ.SameCycle x y ↔ τ.SameCycle (F x) (F y)) :
    orbitCount σ = orbitCount τ := by
  rw [orbitCount_def, orbitCount_def]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map F fun x y hxy => (h x y).mp hxy) ⟨?_, ?_⟩)
  · intro a b hab
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    exact Quotient.sound ((h x y).mpr (Quotient.exact hab))
  · intro b
    induction b using Quotient.inductionOn with | h y => ?_
    obtain ⟨x, rfl⟩ := hF y
    exact ⟨Quotient.mk _ x, rfl⟩

/-- The cycle count of a signed word is the number of orbits of its permutation. -/
theorem SignedAdjacentWord.cycleCount_eq_orbitCount {m : ℕ} (w : SignedAdjacentWord m) :
    w.cycleCount = orbitCount w.permutation := by
  classical
  rw [orbitCount_def, Nat.card_eq_fintype_card]
  unfold SignedAdjacentWord.cycleCount
  exact Fintype.card_congr' rfl

namespace IsAdmissibleWordGrid

variable {m : ℕ} {w : PositiveAdjacentWord m} {G : GridDiagram (w.length * 3)}

/-- The component permutation of an admissible grid is the horizontal matching of the corners,
transported to the native columns. -/
theorem componentPerm_eq (hG : IsAdmissibleWordGrid w G) :
    G.componentPerm = finProdFinEquiv.permCongr (positiveRectilinearWordMatching w) := by
  ext1 c
  rw [GridDiagram.componentPerm_apply_eq_iff, Equiv.permCongr_apply,
    hG.X_finProdFinEquiv_matching, Equiv.apply_symm_apply]

/-- The number of components of an admissible grid is the number of orbits of the horizontal
matching. -/
theorem componentCount_eq (hG : IsAdmissibleWordGrid w G) :
    G.componentCount = orbitCount (positiveRectilinearWordMatching w) := by
  rw [GridDiagram.componentCount_eq_orbitCount, hG.componentPerm_eq,
    Equiv.orbitCount_permCongr]

end IsAdmissibleWordGrid

section Labels

variable {m : ℕ} (w : PositiveAdjacentWord m)

/-- The strand label of a corner. The label of `(h, c)` is the initial position of the strand at
the upper rank of letter `h` after `h` letters if `c = 1`, and at its lower rank otherwise. -/
def positiveRectilinearCornerLabel (p : Fin w.length × Fin 3) : Fin m :=
  positiveWordPrefix w p.1.val
    (if p.2 = 1 then adjacentUpper w[p.1.val] else adjacentLower w[p.1.val])

/-- After a letter, its lower rank carries the strand that was at its upper rank. -/
theorem positiveWordPrefix_succ_lower (j : Fin w.length) :
    positiveWordPrefix w (j.val + 1) (adjacentLower w[j.val]) =
      positiveWordPrefix w j.val (adjacentUpper w[j.val]) := by
  rw [positiveWordPrefix_succ w j.val j.isLt, Perm.mul_apply]
  congr 1
  simp only [adjacentSwap, adjacentLower, adjacentUpper, Equiv.swap_apply_left]

/-- After a letter, its upper rank carries the strand that was at its lower rank. -/
theorem positiveWordPrefix_succ_upper (j : Fin w.length) :
    positiveWordPrefix w (j.val + 1) (adjacentUpper w[j.val]) =
      positiveWordPrefix w j.val (adjacentLower w[j.val]) := by
  rw [positiveWordPrefix_succ w j.val j.isLt, Perm.mul_apply]
  congr 1
  simp only [adjacentSwap, adjacentLower, adjacentUpper, Equiv.swap_apply_right]

/-- The label of the corner where the arc of an occurrence `q` of the rank `r` leaves. -/
theorem positiveRectilinearCornerLabel_outgoing (r : Fin m)
    (q : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearCornerLabel w ((positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩)) =
      positiveWordPrefix w (q.val.val + 1) r := by
  rw [positiveRectilinearOutgoingArc_symm_inr]
  obtain ⟨j, hj⟩ := q
  unfold positiveRectilinearCornerLabel
  rcases hj with rfl | rfl
  · simp only [if_true, positiveWordPrefix_succ_lower]
  · have hne : adjacentUpper w[j.val] ≠ adjacentLower w[j.val] := by
      simp [Fin.ext_iff]
    simp only [if_neg hne, show (2 : Fin 3) ≠ 1 by decide, if_false,
      positiveWordPrefix_succ_upper]

/-- The label of the corner where the arc of the rank `r` enters its occurrence `q`. -/
theorem positiveRectilinearCornerLabel_incoming (r : Fin m)
    (q : PositiveRectilinearRowOccurrences w r) :
    positiveRectilinearCornerLabel w ((positiveRectilinearIncomingArc w).symm (Sum.inr ⟨r, q⟩)) =
      positiveWordPrefix w q.val.val r := by
  rw [positiveRectilinearIncomingArc_symm_inr]
  obtain ⟨j, hj⟩ := q
  unfold positiveRectilinearCornerLabel
  rcases hj with rfl | rfl
  · simp only [if_true, show (0 : Fin 3) ≠ 1 by decide, if_false]
  · have hne : adjacentUpper w[j.val] ≠ adjacentLower w[j.val] := by
      simp [Fin.ext_iff]
    simp only [if_neg hne, if_true]

/-- No letter after the last occurrence of a rank changes the label at that rank. -/
theorem positiveWordPrefix_of_forall_le (r : Fin m) (q : PositiveRectilinearRowOccurrences w r)
    (hq : ∀ b : PositiveRectilinearRowOccurrences w r, b ≤ q) :
    positiveWordPrefix w (q.val.val + 1) r = w.permutation r := by
  rw [← positiveWordPrefix_length]
  apply positiveRectilinearWordPrefix_constant w r q.val.isLt (le_refl _)
  intro k hk _
  constructor
  · intro he
    have hh := hq ⟨k, Or.inl he⟩
    exact absurd hh (not_le.mpr (show q.val.val < k.val by omega))
  · intro he
    have hh := hq ⟨k, Or.inr he⟩
    exact absurd hh (not_le.mpr (show q.val.val < k.val by omega))

/-- No letter before the first occurrence of a rank changes the label at that rank. -/
theorem positiveWordPrefix_of_forall_ge (r : Fin m) (q : PositiveRectilinearRowOccurrences w r)
    (hq : ∀ b : PositiveRectilinearRowOccurrences w r, q ≤ b) :
    positiveWordPrefix w q.val.val r = r := by
  have hh := positiveRectilinearWordPrefix_constant w r (Nat.zero_le q.val.val)
    q.val.isLt.le (fun k _ hkq => ?_)
  · simpa only [positiveWordPrefix_zero, Equiv.Perm.one_apply] using hh.symm
  · constructor
    · intro he
      have hqk := hq ⟨k, Or.inl he⟩
      exact absurd hqk (not_le.mpr (show k.val < q.val.val from hkq))
    · intro he
      have hqk := hq ⟨k, Or.inr he⟩
      exact absurd hqk (not_le.mpr (show k.val < q.val.val from hkq))

/-- A corner is a wrap corner when its arc does not end in a later column. -/
def IsPositiveRectilinearWrapCorner (p : Fin w.length × Fin 3) : Prop :=
  (finProdFinEquiv (positiveRectilinearWordMatching w p)).val ≤ (finProdFinEquiv p).val

/-- Following one arc that ends in a later column keeps the label. -/
theorem positiveRectilinearCornerLabel_matching_of_not_wrap (p : Fin w.length × Fin 3)
    (hp : ¬IsPositiveRectilinearWrapCorner w p) :
    positiveRectilinearCornerLabel w (positiveRectilinearWordMatching w p) =
      positiveRectilinearCornerLabel w p := by
  obtain ⟨a, rfl⟩ := (positiveRectilinearOutgoingArc w).symm.surjective p
  rcases a with j | ⟨r, q⟩
  · rw [show (positiveRectilinearOutgoingArc w).symm (Sum.inl j) = (j, 0) from rfl,
      positiveRectilinearWordMatching_middle]
    simp [positiveRectilinearCornerLabel]
  · rw [positiveRectilinearWordMatching_outgoingArc_symm_inr,
      positiveRectilinearCornerLabel_incoming, positiveRectilinearCornerLabel_outgoing]
    unfold IsPositiveRectilinearWrapCorner at hp
    rw [positiveRectilinearWordMatching_outgoingArc_symm_inr] at hp
    rcases positiveRectilinearWordMatching_labels w r q with ⟨_, h⟩ | ⟨hle, _⟩
    · exact h.symm
    · exfalso
      apply hp
      rw [positiveRectilinearIncomingArc_symm_inr, positiveRectilinearOutgoingArc_symm_inr]
      have hle' : (positiveRectilinearSortedSuccessor _ q).val.val ≤ q.val.val := hle
      simp only [finProdFinEquiv_apply_val]
      have h1 : ∀ P : Prop, [Decidable P] → (if P then (0 : Fin 3) else 1).val ≤ 1 := by
        intro P _; split_ifs <;> simp
      have h2 : ∀ P : Prop, [Decidable P] → 1 ≤ (if P then (1 : Fin 3) else 2).val := by
        intro P _; split_ifs <;> simp
      rcases Nat.lt_or_ge (positiveRectilinearSortedSuccessor _ q).val.val q.val.val with hlt | hge
      · have := h1 (r = adjacentLower w[(positiveRectilinearSortedSuccessor _ q).val.val])
        have := h2 (r = adjacentLower w[q.val.val])
        omega
      · have heq : positiveRectilinearSortedSuccessor _ q = q :=
          Subtype.ext (Fin.ext (le_antisymm hle' hge))
        rw [heq]
        split_ifs <;> simp

/-- A wrap corner leaves the last occurrence of a rank `r`, it has label `π r`, and its arc ends
at a corner of label `r`. -/
theorem exists_of_isPositiveRectilinearWrapCorner (p : Fin w.length × Fin 3)
    (hp : IsPositiveRectilinearWrapCorner w p) :
    ∃ (r : Fin m) (q : PositiveRectilinearRowOccurrences w r),
      p = (positiveRectilinearOutgoingArc w).symm (Sum.inr ⟨r, q⟩) ∧
      (∀ b : PositiveRectilinearRowOccurrences w r, b ≤ q) ∧
      positiveRectilinearCornerLabel w p = w.permutation r ∧
      positiveRectilinearCornerLabel w (positiveRectilinearWordMatching w p) = r := by
  obtain ⟨a, rfl⟩ := (positiveRectilinearOutgoingArc w).symm.surjective p
  rcases a with j | ⟨r, q⟩
  · exfalso
    unfold IsPositiveRectilinearWrapCorner at hp
    rw [show (positiveRectilinearOutgoingArc w).symm (Sum.inl j) = (j, 0) from rfl,
      positiveRectilinearWordMatching_middle] at hp
    simp at hp
  · rcases positiveRectilinearSortedSuccessor_next (PositiveRectilinearRowOccurrences w r) q with
      ⟨hlt, _⟩ | ⟨_, hbounds⟩
    · exfalso
      unfold IsPositiveRectilinearWrapCorner at hp
      rw [positiveRectilinearWordMatching_outgoingArc_symm_inr,
        positiveRectilinearIncomingArc_symm_inr, positiveRectilinearOutgoingArc_symm_inr] at hp
      have hlt' : q.val.val < (positiveRectilinearSortedSuccessor _ q).val.val := hlt
      simp only [finProdFinEquiv_apply_val] at hp
      have h3 : ∀ P : Prop, [Decidable P] → (if P then (1 : Fin 3) else 2).val ≤ 2 := by
        intro P _; split_ifs <;> simp
      have := h3 (r = adjacentLower w[q.val.val])
      omega
    · refine ⟨r, q, rfl, fun b => (hbounds b).2, ?_, ?_⟩
      · rw [positiveRectilinearCornerLabel_outgoing]
        exact positiveWordPrefix_of_forall_le w r q fun b => (hbounds b).2
      · rw [positiveRectilinearWordMatching_outgoingArc_symm_inr,
          positiveRectilinearCornerLabel_incoming]
        exact positiveWordPrefix_of_forall_ge w r _ fun b => (hbounds b).1

/-- A wrap corner is determined by its label. -/
theorem isPositiveRectilinearWrapCorner_injective {p p' : Fin w.length × Fin 3}
    (hp : IsPositiveRectilinearWrapCorner w p) (hp' : IsPositiveRectilinearWrapCorner w p')
    (h : positiveRectilinearCornerLabel w p = positiveRectilinearCornerLabel w p') : p = p' := by
  obtain ⟨r, q, rfl, hq, hl, _⟩ := exists_of_isPositiveRectilinearWrapCorner w p hp
  obtain ⟨r', q', rfl, hq', hl', _⟩ := exists_of_isPositiveRectilinearWrapCorner w _ hp'
  rw [hl, hl'] at h
  obtain rfl : r = r' := w.permutation.injective h
  obtain rfl : q = q' := le_antisymm (hq' q) (hq q')
  rfl

/-- From every corner, following arcs reaches a wrap corner with the same label. -/
theorem exists_pow_isPositiveRectilinearWrapCorner (p : Fin w.length × Fin 3) :
    ∃ n : ℕ, IsPositiveRectilinearWrapCorner w ((positiveRectilinearWordMatching w ^ n) p) ∧
      positiveRectilinearCornerLabel w ((positiveRectilinearWordMatching w ^ n) p) =
        positiveRectilinearCornerLabel w p := by
  induction hk : w.length * 3 - (finProdFinEquiv p).val using Nat.strong_induction_on
    generalizing p with
  | _ k ih =>
    by_cases hp : IsPositiveRectilinearWrapCorner w p
    · exact ⟨0, by simpa using hp, by simp⟩
    · have hlt : (finProdFinEquiv p).val <
          (finProdFinEquiv (positiveRectilinearWordMatching w p)).val := not_le.mp hp
      have hbound := (finProdFinEquiv (positiveRectilinearWordMatching w p)).isLt
      obtain ⟨n, hn, hl⟩ := ih _ (by omega) (positiveRectilinearWordMatching w p) rfl
      refine ⟨n + 1, ?_, ?_⟩
      · rwa [pow_succ, Perm.mul_apply]
      · rw [pow_succ, Perm.mul_apply, hl,
          positiveRectilinearCornerLabel_matching_of_not_wrap w p hp]

/-- One arc moves the label inside one orbit of the word permutation. -/
theorem sameCycle_cornerLabel_matching (p : Fin w.length × Fin 3) :
    w.permutation.SameCycle (positiveRectilinearCornerLabel w p)
      (positiveRectilinearCornerLabel w (positiveRectilinearWordMatching w p)) := by
  by_cases hp : IsPositiveRectilinearWrapCorner w p
  · obtain ⟨r, _, _, _, hl, hm⟩ := exists_of_isPositiveRectilinearWrapCorner w p hp
    rw [hl, hm]
    exact Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ r)
  · rw [positiveRectilinearCornerLabel_matching_of_not_wrap w p hp]

/-- If every rank occurs in `w`, two corners lie in the same orbit of the horizontal matching
exactly when their labels lie in the same orbit of the word permutation. -/
theorem positiveRectilinearWordMatching_sameCycle_iff (x y : Fin w.length × Fin 3) :
    (positiveRectilinearWordMatching w).SameCycle x y ↔
      w.permutation.SameCycle (positiveRectilinearCornerLabel w x)
        (positiveRectilinearCornerLabel w y) := by
  -- Equal labels give the same orbit.
  have heq : ∀ x y, positiveRectilinearCornerLabel w x = positiveRectilinearCornerLabel w y →
      (positiveRectilinearWordMatching w).SameCycle x y := by
    intro x y hxy
    obtain ⟨n, hn, hl⟩ := exists_pow_isPositiveRectilinearWrapCorner w x
    obtain ⟨n', hn', hl'⟩ := exists_pow_isPositiveRectilinearWrapCorner w y
    have hz := isPositiveRectilinearWrapCorner_injective w hn hn' (by rw [hl, hl', hxy])
    have h1 : (positiveRectilinearWordMatching w).SameCycle x
        ((positiveRectilinearWordMatching w ^ n) x) :=
      Perm.sameCycle_pow_right.mpr (Perm.SameCycle.refl _ _)
    have h2 : (positiveRectilinearWordMatching w).SameCycle y
        ((positiveRectilinearWordMatching w ^ n') y) :=
      Perm.sameCycle_pow_right.mpr (Perm.SameCycle.refl _ _)
    rw [hz] at h1
    exact h1.trans h2.symm
  -- The orbit of `x` contains every backward iterate of its label.
  have hback : ∀ k : ℕ, ∃ x', (positiveRectilinearWordMatching w).SameCycle x x' ∧
      positiveRectilinearCornerLabel w x' =
        (w.permutation⁻¹ ^ k) (positiveRectilinearCornerLabel w x) := by
    intro k
    induction k with
    | zero => exact ⟨x, Perm.SameCycle.refl _ _, by simp⟩
    | succ k ih =>
      obtain ⟨x', hx', hl⟩ := ih
      obtain ⟨n, hn, hln⟩ := exists_pow_isPositiveRectilinearWrapCorner w x'
      obtain ⟨r, _, _, _, hlr, hmr⟩ := exists_of_isPositiveRectilinearWrapCorner w _ hn
      refine ⟨positiveRectilinearWordMatching w ((positiveRectilinearWordMatching w ^ n) x'),
        hx'.trans (Perm.sameCycle_apply_right.mpr
          (Perm.sameCycle_pow_right.mpr (Perm.SameCycle.refl _ _))), ?_⟩
      rw [hmr, pow_succ', Perm.mul_apply, ← hl, ← hln, hlr]
      simp
  constructor
  · intro hxy
    obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
    clear hxy
    induction n with
    | zero => exact Perm.SameCycle.refl _ _
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (sameCycle_cornerLabel_matching w _)
  · intro hxy
    obtain ⟨k, hk⟩ := (Perm.sameCycle_inv.mpr hxy).exists_nat_pow_eq
    obtain ⟨x', hx', hl⟩ := hback k
    exact hx'.trans (heq x' y (by rw [hl, hk]))

end Labels

/-- If `m ≥ 2` and every generator occurs in `w`, the horizontal matching and the word permutation
have the same number of orbits. -/
theorem positiveRectilinearWordMatching_orbitCount {m : ℕ} (hm : 2 ≤ m)
    {w : PositiveAdjacentWord m} (hw : w.toSigned.generatorIndices = Finset.univ) :
    orbitCount (positiveRectilinearWordMatching w) = orbitCount w.permutation := by
  refine orbitCount_eq_of_sameCycle_iff (positiveRectilinearCornerLabel w) ?_
    (positiveRectilinearWordMatching_sameCycle_iff w)
  intro l
  have hne := positiveRectilinearWord_all_rows_occur hm w hw l
  obtain ⟨q, -, hq⟩ := Finset.exists_min_image Finset.univ (fun b => b)
    (Finset.univ_nonempty_iff.mpr hne)
  refine ⟨(positiveRectilinearIncomingArc w).symm (Sum.inr ⟨l, q⟩), ?_⟩
  rw [positiveRectilinearCornerLabel_incoming]
  exact positiveWordPrefix_of_forall_ge w l q fun b => hq b (Finset.mem_univ b)

/-- **Record M414.** If `m ≥ 2` and every generator occurs in the positive word `w`, the selected
grid of `w` has as many components as the permutation of `w` has cycles, fixed points
included. -/
theorem wordGrid_componentCount {m : ℕ} (hm : 2 ≤ m) {w : PositiveAdjacentWord m}
    (hw : w.toSigned.generatorIndices = Finset.univ) :
    (wordGrid w).componentCount = w.toSigned.cycleCount := by
  rw [(wordGrid_isAdmissible w).componentCount_eq, positiveRectilinearWordMatching_orbitCount hm hw,
    SignedAdjacentWord.cycleCount_eq_orbitCount]
  rfl

end OnLeConjecture.KnotTheory
