/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordNormalForms
public import OnLeConjecture.KnotTheory.GridMoveRecognition

/-! # Admissible grids of positive words

Let `w` be a positive word of length `L`. Its corners are the pairs `(h, c)` with `h < L` and
`c < 3`, and the corner `(h, c)` lies in the native column `3 h + c` (`finProdFinEquiv`). Every
corner starts exactly one horizontal arc, so arcs are indexed by corners, and
`positiveRectilinearWordMatching w` sends the corner where an arc starts to the corner where it
ends. The unperturbed row of the arc leaving `(h, c)` is `w[h] + 1/2`, `w[h]` or `w[h] + 1` for
`c = 0, 1, 2` (`positiveRectilinearWordArcRow_eq`).

A grid diagram `G` of size `3 L` is admissible for `w` (`IsAdmissibleWordGrid w G`) when, writing
`R a = G.O (finProdFinEquiv a)` for the row of the arc leaving the corner `a`,

* the `X`-marking of the column of `a` lies in the row of the arc arriving at `a`, that is,
  `G.X (finProdFinEquiv a) = R (M⁻¹ a)` for the matching `M`, and
* `R` strictly preserves the order of the unperturbed arc rows.

These are exactly the two properties of the selected grid `wordGrid w` (`wordGrid_isAdmissible`),
and of every grid produced by `exists_positiveRectilinearWordGrid`
(`isAdmissibleWordGrid_of_row`).

## Main results

* `positiveRectilinearWord_noninterleaving_of_arcRow_eq`: two arcs with the same unperturbed row
  have non-interleaving column endpoints. For half-integer rows the arcs belong to different
  letters, and for integer rows the arcs join consecutive occurrences of the same rank.
* `IsAdmissibleWordGrid.arcRow_eq_of_between`: an arc whose grid row lies strictly between the
  rows of two arcs with the same unperturbed row has that unperturbed row too.
* `IsAdmissibleWordGrid.rowHeight_eq`: two admissible grids of the same word have the same
  unperturbed row in each grid row.
* `IsAdmissibleWordGrid.movesTo`: any two admissible grids of the same word are related by row
  commutations. In particular every admissible grid is related to `wordGrid w` by grid moves
  (`IsAdmissibleWordGrid.movesTo_wordGrid`).

All results are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory

open TauCeti

/-- The unperturbed row of the arc leaving a corner. -/
theorem positiveRectilinearWordArcRow_eq {m : ℕ} (w : PositiveAdjacentWord m)
    (j : Fin w.length) (c : Fin 3) :
    positiveRectilinearWordArcRow w (j, c) =
      ![(w[j.val].val : ℝ) + 1 / 2, (w[j.val].val : ℝ), (w[j.val].val : ℝ) + 1] c := by
  change positiveGridRectilinearRows w[j.val] (Equiv.swap 0 1 c) = _
  fin_cases c <;> norm_num [positiveGridRectilinearRows, Equiv.swap_apply_def,
    Fin.ext_iff, Matrix.cons_val_two]

/-- The real horizontal coordinate of the column with a given native index. -/
def positiveRectilinearWordColumnReal {m : ℕ} (w : PositiveAdjacentWord m)
    (k : Fin (w.length * 3)) : ℝ :=
  positiveRectilinearWordColumn w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The real horizontal coordinate is strictly increasing in the native column index. -/
theorem positiveRectilinearWordColumnReal_strictMono {m : ℕ} (w : PositiveAdjacentWord m) :
    StrictMono (positiveRectilinearWordColumnReal w) := by
  intro x y hxy
  have h := positiveRectilinearWordColumn_index_lt w (finProdFinEquiv.symm x)
    (finProdFinEquiv.symm y) (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hxy)
  exact h

/-- The real horizontal coordinate of the native column of a corner. -/
theorem positiveRectilinearWordColumnReal_finProdFinEquiv {m : ℕ} (w : PositiveAdjacentWord m)
    (a : Fin w.length × Fin 3) :
    positiveRectilinearWordColumnReal w (finProdFinEquiv a) =
      positiveRectilinearWordColumn w a.1 a.2 := by
  simp [positiveRectilinearWordColumnReal]

/-- Under a strictly increasing real coordinate, membership in an open cyclic interval gives
cyclic betweenness of the coordinates. -/
theorem positiveRectilinearCyclicBetween_of_mem_cIoo {n : ℕ} {f : Fin n → ℝ}
    (hf : StrictMono f) {a b x : Fin n} (h : x ∈ Grid.cIoo a b) :
    PositiveRectilinearCyclicBetween (f a) (f b) (f x) := by
  rw [Grid.mem_cIoo] at h
  obtain ⟨_, h⟩ := h
  unfold PositiveRectilinearCyclicBetween
  have hlt : ∀ y z : Fin n, f y < f z ↔ y.val < z.val := fun y z => by
    rw [hf.lt_iff_lt, Fin.lt_def]
  simp only [hlt]
  exact h

/-- A half-integer is not an integer. -/
theorem positiveWordGrid_natCast_add_half_ne (i r : ℕ) : (i : ℝ) + 1 / 2 ≠ r := by
  intro h
  have hh : ((2 * i + 1 : ℕ) : ℝ) = ((2 * r : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn : 2 * i + 1 = 2 * r := Nat.cast_injective hh
  omega

/-- A corner of local column one or two starts an integer-row arc, whose unperturbed row is its
rank. -/
theorem exists_positiveRectilinearOutgoingArc_eq_inr {m : ℕ} (w : PositiveAdjacentWord m)
    (a : Fin w.length × Fin 3) (ha : a.2 ≠ 0) :
    ∃ (r : Fin m) (j : PositiveRectilinearRowOccurrences w r),
      positiveRectilinearOutgoingArc w a = Sum.inr ⟨r, j⟩ ∧
        positiveRectilinearWordArcRow w a = (r.val : ℝ) := by
  obtain ⟨h, c⟩ := a
  fin_cases c
  · exact absurd rfl ha
  · refine ⟨adjacentLower w[h.val], ⟨h, Or.inl rfl⟩, rfl, ?_⟩
    rw [positiveRectilinearWordArcRow_eq]
    simp
  · refine ⟨adjacentUpper w[h.val], ⟨h, Or.inr rfl⟩, rfl, ?_⟩
    rw [positiveRectilinearWordArcRow_eq]
    simp

/-- The arc leaving a corner starts at the column of that corner. -/
theorem positiveRectilinearHorizontalArcStart_outgoingArc {m : ℕ} (w : PositiveAdjacentWord m)
    (a : Fin w.length × Fin 3) :
    positiveRectilinearHorizontalArcStart w (positiveRectilinearOutgoingArc w a) =
      positiveRectilinearWordColumn w a.1 a.2 := by
  simp [positiveRectilinearHorizontalArcStart]

/-- The arc leaving a corner ends at the column of the matched corner. -/
theorem positiveRectilinearHorizontalArcEnd_outgoingArc {m : ℕ} (w : PositiveAdjacentWord m)
    (a : Fin w.length × Fin 3) :
    positiveRectilinearHorizontalArcEnd w (positiveRectilinearOutgoingArc w a) =
      positiveRectilinearWordColumn w (positiveRectilinearWordMatching w a).1
        (positiveRectilinearWordMatching w a).2 :=
  rfl

/-- Neither endpoint of an integer-row arc of rank `r` lies strictly inside an arc of the same
rank, in the cyclic order of the native columns. -/
theorem positiveRectilinearWord_integerArc_endpoints_notMem {m : ℕ}
    (w : PositiveAdjacentWord m) (r : Fin m) (j k : PositiveRectilinearRowOccurrences w r)
    (a b : Fin w.length × Fin 3) (ha : positiveRectilinearOutgoingArc w a = Sum.inr ⟨r, j⟩)
    (hb : positiveRectilinearOutgoingArc w b = Sum.inr ⟨r, k⟩) :
    finProdFinEquiv b ∉ Grid.cIoo (finProdFinEquiv a)
        (finProdFinEquiv (positiveRectilinearWordMatching w a)) ∧
      finProdFinEquiv (positiveRectilinearWordMatching w b) ∉ Grid.cIoo (finProdFinEquiv a)
        (finProdFinEquiv (positiveRectilinearWordMatching w a)) := by
  have hf := positiveRectilinearWordColumnReal_strictMono w
  have hstart : positiveRectilinearWordColumnReal w (finProdFinEquiv a) =
      positiveRectilinearHorizontalArcStart w (Sum.inr ⟨r, j⟩) := by
    rw [← ha, positiveRectilinearHorizontalArcStart_outgoingArc,
      positiveRectilinearWordColumnReal_finProdFinEquiv]
  have hend : positiveRectilinearWordColumnReal w
      (finProdFinEquiv (positiveRectilinearWordMatching w a)) =
      positiveRectilinearHorizontalArcEnd w (Sum.inr ⟨r, j⟩) := by
    rw [← ha, positiveRectilinearHorizontalArcEnd_outgoingArc,
      positiveRectilinearWordColumnReal_finProdFinEquiv]
  have hlt := positiveRectilinearIntegerRowIn_lt_out w r
  constructor
  · intro hmem
    have hc := positiveRectilinearCyclicBetween_of_mem_cIoo hf hmem
    rw [hstart, hend] at hc
    have hx : positiveRectilinearWordColumnReal w (finProdFinEquiv b) ∈
        Set.Icc (positiveRectilinearIntegerRowIn w r k)
          (positiveRectilinearIntegerRowOut w r k) := by
      rw [positiveRectilinearWordColumnReal_finProdFinEquiv,
        ← positiveRectilinearHorizontalArcStart_outgoingArc, hb,
        positiveRectilinearHorizontalArcStart_integer]
      exact ⟨(hlt k).le, le_rfl⟩
    exact positiveRectilinearIntegerRow_arc_excludes_occurrence w r j k hx hc
  · intro hmem
    have hc := positiveRectilinearCyclicBetween_of_mem_cIoo hf hmem
    rw [hstart, hend] at hc
    set k' := positiveRectilinearSortedSuccessor (PositiveRectilinearRowOccurrences w r) k
    have hx : positiveRectilinearWordColumnReal w
        (finProdFinEquiv (positiveRectilinearWordMatching w b)) ∈
        Set.Icc (positiveRectilinearIntegerRowIn w r k')
          (positiveRectilinearIntegerRowOut w r k') := by
      rw [positiveRectilinearWordColumnReal_finProdFinEquiv,
        ← positiveRectilinearHorizontalArcEnd_outgoingArc, hb,
        positiveRectilinearHorizontalArcEnd_integer]
      exact ⟨le_rfl, (hlt k').le⟩
    exact positiveRectilinearIntegerRow_arc_excludes_occurrence w r j k' hx hc

/-- Two horizontal arcs with the same unperturbed row have non-interleaving column endpoints. -/
theorem positiveRectilinearWord_noninterleaving_of_arcRow_eq {m : ℕ}
    (w : PositiveAdjacentWord m) (a b : Fin w.length × Fin 3)
    (h : positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b) :
    Grid.Noninterleaving (finProdFinEquiv a) (finProdFinEquiv (positiveRectilinearWordMatching w a))
      (finProdFinEquiv b) (finProdFinEquiv (positiveRectilinearWordMatching w b)) := by
  by_cases ha : a.2 = 0
  · by_cases hb : b.2 = 0
    · obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at ha hb
      subst ha hb
      rw [positiveRectilinearWordMatching_middle, positiveRectilinearWordMatching_middle]
      have ha1 := a1.isLt
      have hb1 := b1.isLt
      unfold Grid.Noninterleaving
      simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, finProdFinEquiv_apply_val]
      split_ifs <;> omega
    · exfalso
      obtain ⟨r, j, _, hr⟩ := exists_positiveRectilinearOutgoingArc_eq_inr w b hb
      obtain ⟨a1, a2⟩ := a
      simp only at ha
      subst ha
      rw [hr, positiveRectilinearWordArcRow_eq] at h
      exact positiveWordGrid_natCast_add_half_ne _ _ (by simpa using h)
  · by_cases hb : b.2 = 0
    · exfalso
      obtain ⟨r, j, _, hr⟩ := exists_positiveRectilinearOutgoingArc_eq_inr w a ha
      obtain ⟨b1, b2⟩ := b
      simp only at hb
      subst hb
      rw [hr, positiveRectilinearWordArcRow_eq] at h
      exact positiveWordGrid_natCast_add_half_ne _ _ (by simpa using h.symm)
    · obtain ⟨r, j, hj, hr⟩ := exists_positiveRectilinearOutgoingArc_eq_inr w a ha
      obtain ⟨r', k, hk, hr'⟩ := exists_positiveRectilinearOutgoingArc_eq_inr w b hb
      have hrr : r = r' := by
        rw [hr, hr'] at h
        exact Fin.ext (by exact_mod_cast h)
      subst hrr
      obtain ⟨h1, h2⟩ := positiveRectilinearWord_integerArc_endpoints_notMem w r j k a b hj hk
      obtain ⟨h3, h4⟩ := positiveRectilinearWord_integerArc_endpoints_notMem w r k j b a hk hj
      exact ⟨iff_of_false h3 h4, iff_of_false h1 h2⟩

/-- A grid diagram of size `3 |w|` is admissible for the positive word `w` when, with the column
`3 h + c` of the corner `(h, c)` and the row `R a = G.O (finProdFinEquiv a)` of the arc leaving
the corner `a`, the `X`-marking of each column lies in the row of the arc arriving there, and
the rows strictly preserve the order of the unperturbed arc rows. -/
structure IsAdmissibleWordGrid {m : ℕ} (w : PositiveAdjacentWord m)
    (G : GridDiagram (w.length * 3)) : Prop where
  X_eq : ∀ a, G.X (finProdFinEquiv a) =
    G.O (finProdFinEquiv ((positiveRectilinearWordMatching w).symm a))
  O_lt_of_arcRow_lt : ∀ a b,
    positiveRectilinearWordArcRow w a < positiveRectilinearWordArcRow w b →
      G.O (finProdFinEquiv a) < G.O (finProdFinEquiv b)

/-- The selected grid of a word is admissible. -/
theorem wordGrid_isAdmissible {m : ℕ} (w : PositiveAdjacentWord m) :
    IsAdmissibleWordGrid w (wordGrid w) :=
  ⟨wordGrid_X_eq w, fun _ _ h => wordGrid_O_lt_of_arcRow_lt w h⟩

/-- A grid with the marking equations and the row order of `exists_positiveRectilinearWordGrid`
is admissible. -/
theorem isAdmissibleWordGrid_of_row {m : ℕ} (w : PositiveAdjacentWord m)
    (G : GridDiagram (w.length * 3)) (g : Fin w.length × Fin 3 → ℝ)
    (row : Fin (w.length * 3) → ℝ) (hrow : StrictMono row)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) = g ((positiveRectilinearWordMatching w).symm p))
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) :
    IsAdmissibleWordGrid w G where
  X_eq a := hrow.injective (by rw [hX, hO])
  O_lt_of_arcRow_lt a b h := by
    rw [← hrow.lt_iff_lt, hO, hO]
    exact horder a b h

namespace IsAdmissibleWordGrid

variable {m : ℕ} {w : PositiveAdjacentWord m} {G : GridDiagram (w.length * 3)}

/-- The unperturbed row of the arc whose markings occupy a given grid row. -/
def rowHeight (G : GridDiagram (w.length * 3)) (r : Fin (w.length * 3)) : ℝ :=
  positiveRectilinearWordArcRow w (finProdFinEquiv.symm (G.O.transpose r))

/-- The `X`-marking in the column of the corner where the arc leaving `a` ends lies in the row of
that arc. -/
theorem X_finProdFinEquiv_matching (hG : IsAdmissibleWordGrid w G) (a : Fin w.length × Fin 3) :
    G.X (finProdFinEquiv (positiveRectilinearWordMatching w a)) = G.O (finProdFinEquiv a) := by
  rw [hG.X_eq, Equiv.symm_apply_apply]

/-- In an admissible grid, an arc whose row lies strictly between the rows of two arcs with the
same unperturbed row has that unperturbed row too. -/
theorem arcRow_eq_of_between (hG : IsAdmissibleWordGrid w G) {a b c : Fin w.length × Fin 3}
    (hab : positiveRectilinearWordArcRow w a = positiveRectilinearWordArcRow w b)
    (hc : G.O (finProdFinEquiv a) < G.O (finProdFinEquiv c) ∧
        G.O (finProdFinEquiv c) < G.O (finProdFinEquiv b) ∨
      G.O (finProdFinEquiv b) < G.O (finProdFinEquiv c) ∧
        G.O (finProdFinEquiv c) < G.O (finProdFinEquiv a)) :
    positiveRectilinearWordArcRow w c = positiveRectilinearWordArcRow w a := by
  rcases lt_trichotomy (positiveRectilinearWordArcRow w c) (positiveRectilinearWordArcRow w a)
    with h | h | h
  · have h1 := hG.O_lt_of_arcRow_lt _ _ h
    have h2 := hG.O_lt_of_arcRow_lt _ _ (hab ▸ h)
    rcases hc with hc | hc
    · exact absurd (h1.trans hc.1) (lt_irrefl _)
    · exact absurd (h2.trans hc.1) (lt_irrefl _)
  · exact h
  · have h1 := hG.O_lt_of_arcRow_lt _ _ h
    have h2 := hG.O_lt_of_arcRow_lt _ _ (hab ▸ h)
    rcases hc with hc | hc
    · exact absurd (h2.trans hc.2) (lt_irrefl _)
    · exact absurd (h1.trans hc.2) (lt_irrefl _)

/-- In an admissible grid, the unperturbed row of the arc in a grid row is monotone in the row. -/
theorem rowHeight_monotone (hG : IsAdmissibleWordGrid w G) : Monotone (rowHeight (w := w) G) := by
  intro r r' hrr'
  by_contra hlt
  rw [not_le] at hlt
  have h := hG.O_lt_of_arcRow_lt _ _ hlt
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, GridState.apply_transpose_apply,
    GridState.apply_transpose_apply] at h
  exact absurd hrr' (not_le.mpr h)

/-- Two admissible grids of the same word have the same unperturbed row in each grid row. -/
theorem rowHeight_eq {G' : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G)
    (hG' : IsAdmissibleWordGrid w G') : rowHeight (w := w) G' = rowHeight (w := w) G := by
  let π : Equiv.Perm (Fin (w.length * 3)) := G'.O.toPerm.symm.trans G.O.toPerm
  have hcomp : rowHeight (w := w) G' = rowHeight (w := w) G ∘ π := by
    funext r
    simp only [rowHeight, Function.comp_apply, π, Equiv.trans_apply, GridState.transpose_apply,
      Equiv.symm_apply_apply]
  have hperm : (List.ofFn (rowHeight (w := w) G')).Perm (List.ofFn (rowHeight (w := w) G)) := by
    rw [hcomp]
    exact Equiv.Perm.ofFn_comp_perm π _
  have hsort := List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hG'.rowHeight_monotone)
    (List.sortedLE_ofFn_iff.mpr hG.rowHeight_monotone) hperm
  exact List.ofFn_injective hsort

/-- Any two admissible grids of the same word are related by row commutations. -/
theorem movesTo {G' : GridDiagram (w.length * 3)} (hG : IsAdmissibleWordGrid w G)
    (hG' : IsAdmissibleWordGrid w G') : G.MovesTo G' := by
  let σ : Equiv.Perm (Fin (w.length * 3)) := G.O.toPerm.symm.trans G'.O.toPerm
  have hσO : ∀ c, σ (G.O c) = G'.O c := fun c => by
    change G'.O.toPerm (G.O.toPerm.symm (G.O.toPerm c)) = G'.O.toPerm c
    rw [Equiv.symm_apply_apply]
  have hrel : G' = G.relabelRows σ := by
    ext1
    · exact GridState.ext fun c => by
        rw [GridDiagram.relabelRows_O, GridState.relabelRows_apply, hσO]
    · refine GridState.ext fun c => ?_
      rw [GridDiagram.relabelRows_X, GridState.relabelRows_apply]
      obtain ⟨a, rfl⟩ := finProdFinEquiv.surjective c
      rw [hG.X_eq, hG'.X_eq, hσO]
  rw [hrel]
  apply GridDiagram.movesTo_relabelRows_of_monotone G (rowHeight (w := w) G) hG.rowHeight_monotone
  · intro r r' hrr'
    change Grid.Noninterleaving (G.O.transpose r) (G.X.transpose r) (G.O.transpose r')
      (G.X.transpose r')
    obtain ⟨a, ha⟩ := finProdFinEquiv.surjective (G.O.transpose r)
    obtain ⟨a', ha'⟩ := finProdFinEquiv.surjective (G.O.transpose r')
    have hXa : G.X.transpose r = finProdFinEquiv (positiveRectilinearWordMatching w a) := by
      rw [GridState.transpose_apply, Equiv.symm_apply_eq]
      change r = G.X (finProdFinEquiv (positiveRectilinearWordMatching w a))
      rw [hG.X_finProdFinEquiv_matching, ha, GridState.apply_transpose_apply]
    have hXa' : G.X.transpose r' = finProdFinEquiv (positiveRectilinearWordMatching w a') := by
      rw [GridState.transpose_apply, Equiv.symm_apply_eq]
      change r' = G.X (finProdFinEquiv (positiveRectilinearWordMatching w a'))
      rw [hG.X_finProdFinEquiv_matching, ha', GridState.apply_transpose_apply]
    rw [← ha, ← ha', hXa, hXa']
    apply positiveRectilinearWord_noninterleaving_of_arcRow_eq
    simpa only [rowHeight, ← ha, ← ha', Equiv.symm_apply_apply] using hrr'
  · intro r
    rw [← congrFun (rowHeight_eq hG hG') (σ r)]
    simp only [rowHeight, σ, Equiv.trans_apply, GridState.transpose_apply]
    change positiveRectilinearWordArcRow w (finProdFinEquiv.symm
      (G'.O.toPerm.symm (G'.O.toPerm (G.O.toPerm.symm r)))) = _
    rw [Equiv.symm_apply_apply]

/-- Every admissible grid of a word is related by grid moves to the selected grid of the
word. -/
theorem movesTo_wordGrid (hG : IsAdmissibleWordGrid w G) : G.MovesTo (wordGrid w) :=
  hG.movesTo (wordGrid_isAdmissible w)

end IsAdmissibleWordGrid

end OnLeConjecture.KnotTheory
