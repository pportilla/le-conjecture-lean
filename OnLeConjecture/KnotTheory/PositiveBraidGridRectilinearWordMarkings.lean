/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRectilinearWordCrossings
public import OnLeConjecture.KnotTheory.FiniteRowSeparation
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # Grid markings from the word's cyclic horizontal arcs

An arc is indexed by its outgoing `O` corner. Its incoming `X` corner receives
exactly the same perturbed row. Sorting those separated arc rows constructs
both permutation markings of a native grid diagram. This construction records
actual corner coordinates and cyclic incidence. It does not assert an ambient
isotopy from the original braid to the diagram.
-/

@[expose] public noncomputable section

open Set

namespace OnLeConjecture.KnotTheory

/-- The row at the outgoing corner, used to perturb each whole horizontal arc once. -/
def positiveRectilinearWordArcRow {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) : ℝ := (positiveRectilinearWordOCorner w p.1 p.2).2

/-- The incoming row is the row of the unique preceding horizontal arc. -/
theorem positiveRectilinearWordArcRow_incoming {m : ℕ} (w : PositiveAdjacentWord m)
    (p : Fin w.length × Fin 3) :
    positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm p) =
      (positiveRectilinearWordXCorner w p.1 p.2).2 := by
  simpa only [positiveRectilinearWordArcRow, Equiv.apply_symm_apply] using
    positiveRectilinearWordMatching_row w ((positiveRectilinearWordMatching w).symm p)

/-- The standard product indexing preserves the literal order of all vertical columns. -/
theorem positiveRectilinearWordColumn_index_lt {m : ℕ} (w : PositiveAdjacentWord m)
    (p q : Fin w.length × Fin 3) (hpq : finProdFinEquiv p < finProdFinEquiv q) :
    positiveRectilinearWordColumn w p.1 p.2 < positiveRectilinearWordColumn w q.1 q.2 := by
  change p.2.val + 3 * p.1.val < q.2.val + 3 * q.1.val at hpq
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · exact positiveRectilinearWordColumn_lt w h p.2 q.2
  · have hh : p.2 < q.2 := by
      have hval := congrArg Fin.val h
      have hp := p.2.isLt
      have hq := q.2.isLt
      omega
    dsimp only [positiveRectilinearWordColumn]
    rw [h]
    exact add_lt_add_right (positiveGridRectilinearColumns_strictMono hh) _
  · have hp := p.2.isLt
    have hq := q.2.isLt
    have hval : q.1.val < p.1.val := h
    omega

/-- Distinct arc heights give a grid whose markings are the exact separated word corners.
The real row embedding is strictly increasing in the native finite grid row coordinate. -/
theorem exists_positiveRectilinearWordGrid_of_injective {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (hg : Function.Injective g) :
    ∃ (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ),
      StrictMono row ∧
      (∀ p, row (G.O (finProdFinEquiv p)) = g p) ∧
      (∀ p, row (G.X (finProdFinEquiv p)) =
        g ((positiveRectilinearWordMatching w).symm p)) := by
  classical
  let eG := Equiv.ofInjective g hg
  let : Fintype (Set.range g) := Fintype.ofEquiv _ eG
  have hc : Fintype.card (Set.range g) = w.length * 3 := by
    rw [← Fintype.card_congr eG]
    simp
  let e := monoEquivOfFin (Set.range g) hc
  let h : (Fin w.length × Fin 3) ≃ Fin (w.length * 3) := eG.trans e.symm.toEquiv
  let O : Equiv.Perm (Fin (w.length * 3)) := finProdFinEquiv.symm.trans h
  let X : Equiv.Perm (Fin (w.length * 3)) := finProdFinEquiv.symm.trans
    ((positiveRectilinearWordMatching w).symm.trans h)
  let G : TauCeti.GridDiagram (w.length * 3) :=
    { O := ⟨O⟩
      X := ⟨X⟩
      disjoint := by
        intro c he
        have hh := h.injective he
        change finProdFinEquiv.symm c =
          (positiveRectilinearWordMatching w).symm (finProdFinEquiv.symm c) at hh
        have hfix : positiveRectilinearWordMatching w (finProdFinEquiv.symm c) =
            finProdFinEquiv.symm c := by
          simpa only [Equiv.apply_symm_apply] using
            congrArg (positiveRectilinearWordMatching w) hh
        exact positiveRectilinearWordMatching_ne_self w _ hfix }
  refine ⟨G, fun r => (e r).val, ?_, ?_, ?_⟩
  · intro r s hrs
    exact e.strictMono hrs
  · intro p
    change (e (h (finProdFinEquiv.symm (finProdFinEquiv p)))).val = g p
    simp [h, eG]
  · intro p
    change (e (h ((positiveRectilinearWordMatching w).symm
      (finProdFinEquiv.symm (finProdFinEquiv p))))).val = _
    simp [h, eG]

/-- The full finite set of corners admits arbitrarily small distinct arc rows and native
permutation markings. Original strict row comparisons are retained. -/
theorem exists_positiveRectilinearWordGrid {m : ℕ} (w : PositiveAdjacentWord m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : Fin w.length × Fin 3 → ℝ)
      (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ),
      Function.Injective g ∧
      (∀ p, |g p - positiveRectilinearWordArcRow w p| < ε) ∧
      (∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
        g p < g q) ∧
      StrictMono row ∧
      (∀ p, row (G.O (finProdFinEquiv p)) = g p) ∧
      (∀ p, row (G.X (finProdFinEquiv p)) =
        g ((positiveRectilinearWordMatching w).symm p)) := by
  obtain ⟨g, hg, hclose, horder⟩ := exists_injective_row_perturbation
    (positiveRectilinearWordArcRow w) hε
  obtain ⟨G, row, hrow, hO, hX⟩ := exists_positiveRectilinearWordGrid_of_injective w g hg
  exact ⟨g, G, row, hg, hclose, horder, hrow, hO, hX⟩

/-- Perturbing a whole arc preserves both of its endpoint heights exactly. -/
theorem positiveRectilinearWordGrid_horizontal_matching {m : ℕ}
    (w : PositiveAdjacentWord m) (G : TauCeti.GridDiagram (w.length * 3))
    (row : Fin (w.length * 3) → ℝ) (hrow : Function.Injective row)
    (g : Fin w.length × Fin 3 → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p)) (p : Fin w.length × Fin 3) :
    G.O (finProdFinEquiv p) = G.X (finProdFinEquiv (positiveRectilinearWordMatching w p)) := by
  apply hrow
  rw [hO, hX, Equiv.symm_apply_apply]

/-- Strict vertical interior incidences persist under the separated row assignment. -/
theorem positiveRectilinearWordGrid_preserves_crossing_rows {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) (p q : Fin w.length × Fin 3)
    (hcross : (positiveRectilinearWordXCorner w p.1 p.2).2 <
        positiveRectilinearWordArcRow w q ∧
      positiveRectilinearWordArcRow w q < (positiveRectilinearWordOCorner w p.1 p.2).2) :
    g ((positiveRectilinearWordMatching w).symm p) < g q ∧ g q < g p := by
  constructor
  · apply horder
    simpa only [positiveRectilinearWordArcRow_incoming] using hcross.1
  · exact horder _ _ hcross.2

/-- The known upper-over-lower crossing in each letter survives the row perturbation. -/
theorem positiveRectilinearWordGrid_letter_crossing {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) (j : Fin w.length) :
    g (j, 1) < g (j, 0) ∧
      g (j, 0) < g ((positiveRectilinearWordMatching w).symm (j, 1)) := by
  constructor
  · apply horder
    change positiveGridRectilinearRows w[j.val] (positiveGridRectilinearDiagram.O 1) <
      positiveGridRectilinearRows w[j.val] (positiveGridRectilinearDiagram.O 0)
    norm_num [positiveGridRectilinearRows, positiveGridRectilinearDiagram,
      Equiv.swap_apply_def, Fin.ext_iff]
  · apply horder
    rw [positiveRectilinearWordArcRow_incoming]
    change positiveGridRectilinearRows w[j.val] (positiveGridRectilinearDiagram.O 0) <
      positiveGridRectilinearRows w[j.val] (positiveGridRectilinearDiagram.X 1)
    norm_num [positiveGridRectilinearRows, positiveGridRectilinearDiagram,
      Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val_two]

private theorem row_comparison_iff {α : Type*} (f g : α → ℝ)
    (horder : ∀ a b, f a < f b → g a < g b) {a b : α} (hne : f a ≠ f b) :
    g a < g b ↔ f a < f b := by
  constructor
  · intro h
    by_contra hn
    have hr : f b < f a := lt_of_le_of_ne (le_of_not_gt hn) hne.symm
    exact (not_lt_of_gt (horder b a hr)) h
  · exact horder a b

/-- Converting an arc back to its outgoing corner recovers the same unperturbed row. -/
theorem positiveRectilinearWordArcRow_outgoing {m : ℕ} (w : PositiveAdjacentWord m)
    (a : PositiveRectilinearHorizontalArc w) :
    positiveRectilinearWordArcRow w ((positiveRectilinearOutgoingArc w).symm a) =
      positiveRectilinearHorizontalArcRow w a := by
  rw [positiveRectilinearWordArcRow, ← positiveRectilinearOutgoingArc_row]
  simp

/-- Along the interior of each horizontal arc, separated rows preserve the exact vertical
crossing test in both orientations. The endpoint exclusion is proved from the word. -/
theorem positiveRectilinearWordGrid_crossing_rows_iff {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) (a : PositiveRectilinearHorizontalArc w) (p : Fin w.length × Fin 3)
    (hx : PositiveRectilinearCyclicBetween (positiveRectilinearHorizontalArcStart w a)
      (positiveRectilinearHorizontalArcEnd w a) (positiveRectilinearWordColumn w p.1 p.2)) :
    ((g ((positiveRectilinearWordMatching w).symm p) <
        g ((positiveRectilinearOutgoingArc w).symm a) ∧
      g ((positiveRectilinearOutgoingArc w).symm a) < g p) ∨
     (g p < g ((positiveRectilinearOutgoingArc w).symm a) ∧
      g ((positiveRectilinearOutgoingArc w).symm a) <
        g ((positiveRectilinearWordMatching w).symm p))) ↔
    (((positiveRectilinearWordXCorner w p.1 p.2).2 < positiveRectilinearHorizontalArcRow w a ∧
      positiveRectilinearHorizontalArcRow w a < (positiveRectilinearWordOCorner w p.1 p.2).2) ∨
     ((positiveRectilinearWordOCorner w p.1 p.2).2 < positiveRectilinearHorizontalArcRow w a ∧
      positiveRectilinearHorizontalArcRow w a < (positiveRectilinearWordXCorner w p.1 p.2).2)) := by
  have hn := positiveRectilinearHorizontalArc_endpoint_ne w a p hx
  have hX : positiveRectilinearWordArcRow w ((positiveRectilinearWordMatching w).symm p) ≠
      positiveRectilinearWordArcRow w ((positiveRectilinearOutgoingArc w).symm a) := by
    simpa only [positiveRectilinearWordArcRow_incoming,
      positiveRectilinearWordArcRow_outgoing] using hn.1
  have hO : positiveRectilinearWordArcRow w p ≠
      positiveRectilinearWordArcRow w ((positiveRectilinearOutgoingArc w).symm a) := by
    rw [positiveRectilinearWordArcRow_outgoing]
    exact hn.2
  rw [row_comparison_iff _ g horder hX, row_comparison_iff _ g horder hO.symm,
    row_comparison_iff _ g horder hO, row_comparison_iff _ g horder hX.symm]
  simp only [positiveRectilinearWordArcRow_incoming, positiveRectilinearWordArcRow_outgoing]
  rfl

/-- Separating the horizontal arc rows introduces no extra crossings: the complete cyclic
corner diagram still has exactly the designated crossing of each positive letter. -/
theorem positiveRectilinearWordGrid_crossing_iff {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) (a : PositiveRectilinearHorizontalArc w) (p : Fin w.length × Fin 3) :
    (PositiveRectilinearCyclicBetween (positiveRectilinearHorizontalArcStart w a)
      (positiveRectilinearHorizontalArcEnd w a) (positiveRectilinearWordColumn w p.1 p.2) ∧
      ((g ((positiveRectilinearWordMatching w).symm p) <
          g ((positiveRectilinearOutgoingArc w).symm a) ∧
        g ((positiveRectilinearOutgoingArc w).symm a) < g p) ∨
       (g p < g ((positiveRectilinearOutgoingArc w).symm a) ∧
        g ((positiveRectilinearOutgoingArc w).symm a) <
          g ((positiveRectilinearWordMatching w).symm p)))) ↔
      ∃ j : Fin w.length, a = Sum.inl j ∧ p = (j, 1) := by
  rw [← positiveRectilinearHorizontalArc_crossing_iff w a p]
  exact and_congr_right fun hx => positiveRectilinearWordGrid_crossing_rows_iff w g horder a p hx

/-- The actual native permutation markings have exactly those same crossings in their
strictly increasing real row coordinates. -/
theorem positiveRectilinearWordGrid_native_crossing_iff {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) (G : TauCeti.GridDiagram (w.length * 3))
    (row : Fin (w.length * 3) → ℝ) (hrow : StrictMono row)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (a : PositiveRectilinearHorizontalArc w) (p : Fin w.length × Fin 3) :
    (PositiveRectilinearCyclicBetween (positiveRectilinearHorizontalArcStart w a)
      (positiveRectilinearHorizontalArcEnd w a) (positiveRectilinearWordColumn w p.1 p.2) ∧
      ((G.X (finProdFinEquiv p) <
          G.O (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm a)) ∧
        G.O (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm a)) <
          G.O (finProdFinEquiv p)) ∨
       (G.O (finProdFinEquiv p) <
          G.O (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm a)) ∧
        G.O (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm a)) <
          G.X (finProdFinEquiv p)))) ↔
      ∃ j : Fin w.length, a = Sum.inl j ∧ p = (j, 1) := by
  have hr (x y : Fin (w.length * 3)) : x < y ↔ row x < row y := hrow.lt_iff_lt.symm
  simp only [hr, hO, hX]
  exact positiveRectilinearWordGrid_crossing_iff w g horder a p

/-- Every preserved crossing has positive determinant in the vertical-over-horizontal
convention: the upper vertical segment points down and the horizontal arc points right. -/
theorem positiveRectilinearWordGrid_crossing_determinant_pos {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    (horder : ∀ p q, positiveRectilinearWordArcRow w p < positiveRectilinearWordArcRow w q →
      g p < g q) (j : Fin w.length) :
    0 < (positiveRectilinearWordColumn w j 2 - positiveRectilinearWordColumn w j 0) *
      (g ((positiveRectilinearWordMatching w).symm (j, 1)) - g (j, 1)) := by
  have hr := positiveRectilinearWordGrid_letter_crossing w g horder j
  apply mul_pos
  · norm_num [positiveRectilinearWordColumn, positiveGridRectilinearColumns, Matrix.cons_val_two]
  · exact sub_pos.mpr (lt_trans hr.1 hr.2)

/-- When every adjacent generator occurs and there are at least two strands, every integer
rank belongs to the constructed cyclic horizontal arcs. -/
theorem positiveRectilinearWord_all_rows_occur {m : ℕ} (hm : 2 ≤ m)
    (w : PositiveAdjacentWord m) (hgen : w.toSigned.generatorIndices = Finset.univ)
    (r : Fin m) : Nonempty (PositiveRectilinearRowOccurrences w r) := by
  have hmem (i : Fin (m - 1)) : i ∈ w := by
    have hi : i ∈ w.toSigned.generatorIndices := by rw [hgen]; simp
    simpa [SignedAdjacentWord.generatorIndices, PositiveAdjacentWord.toSigned,
      List.map_map] using hi
  by_cases hr : r.val < m - 1
  · let i : Fin (m - 1) := ⟨r.val, hr⟩
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (hmem i)
    refine ⟨⟨⟨j, hj⟩, Or.inl ?_⟩⟩
    change r = adjacentLower w[j]
    rw [he]
  · let i : Fin (m - 1) := ⟨r.val - 1, by omega⟩
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp (hmem i)
    refine ⟨⟨⟨j, hj⟩, Or.inr ?_⟩⟩
    change r = adjacentUpper w[j]
    rw [he]
    apply Fin.ext
    change r.val = r.val - 1 + 1
    omega

end OnLeConjecture.KnotTheory
