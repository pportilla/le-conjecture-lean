/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveWordGridMovesMacros

/-!
# The shared-endpoint exchange of two columns

The first elementary rule of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 7, "Two elementary grid rules"): two consecutive columns
`A, B` with `(O_A, X_A) = (r, p)` and `X_B = r` can be exchanged by grid moves, although their
segments share the row `r`. Moving the row `r` next to `p` and destabilizing deletes `A` and `r`;
the same destabilization applies to the exchanged order `B, A`, with the same result
(`movesTo_swapCols_shared_up`, `movesTo_swapCols_shared_down`). The marked inverse cancellation
(Section 8) uses this rule to move a protected block past the column at an end of its own arc.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open TauCeti OnLeConjecture.KnotTheory LabeledGrid

variable {n : ℕ} {C R : Type*}

theorem perm_swap_middle (l₁ l₂ : List C) (a b : C) :
    (l₁ ++ b :: a :: l₂).Perm (l₁ ++ a :: b :: l₂) :=
  List.Perm.append_left _ (List.Perm.swap a b l₂)

/-- **Shared-endpoint exchange, row `X_A` above `r`.** -/
theorem movesTo_swapCols_shared_up [DecidableEq R] (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C}
    {m₁ mid m₂ : List R} {a b : C} {r p : R} (hcols : G.cols = l₁ ++ a :: b :: l₂)
    (hrows : G.rows = m₁ ++ r :: (mid ++ p :: m₂)) (hOa : G.O a = r) (hXa : G.X a = p)
    (hXb : G.X b = r) (hOb : G.O b ≠ p) (hmid : ∀ x ∈ mid, x ≠ G.O b) :
    G.toGrid.MovesTo
      (G.withCols (l₁ ++ b :: a :: l₂) (hcols ▸ perm_swap_middle l₁ l₂ a b)).toGrid := by
  classical
  set G₂ := G.withCols (l₁ ++ b :: a :: l₂) (hcols ▸ perm_swap_middle l₁ l₂ a b) with hG₂
  obtain ⟨G', hc', hr', hO', hX', hm'⟩ :=
    G.exists_mergeX_up (Or.inl hcols) hrows hOa hXa hXb hOb hmid
  obtain ⟨G'', hc'', hr'', hO'', hX'', hm''⟩ :=
    G₂.exists_mergeX_up (c := a) (d := b) (Or.inr rfl) hrows hOa hXa hXb hOb hmid
  have he : G'.toGrid = G''.toGrid := toGrid_eq_of_data _ _ (hc'.trans hc''.symm)
    (hr'.trans hr''.symm) (fun c _ => by rw [hO', hO'']; rfl)
    (fun c _ => by rw [hX', hX'']; rfl)
  rw [he] at hm'
  exact hm'.trans hm''.symm

/-- **Shared-endpoint exchange, row `X_A` below `r`.** -/
theorem movesTo_swapCols_shared_down [DecidableEq R] (G : LabeledGrid (n + 1) C R) {l₁ l₂ : List C}
    {m₁ mid m₂ : List R} {a b : C} {r p : R} (hcols : G.cols = l₁ ++ a :: b :: l₂)
    (hrows : G.rows = m₁ ++ p :: (mid ++ r :: m₂)) (hOa : G.O a = r) (hXa : G.X a = p)
    (hXb : G.X b = r) (hOb : G.O b ≠ p) (hmid : ∀ x ∈ mid, x ≠ G.O b) :
    G.toGrid.MovesTo
      (G.withCols (l₁ ++ b :: a :: l₂) (hcols ▸ perm_swap_middle l₁ l₂ a b)).toGrid := by
  classical
  set G₂ := G.withCols (l₁ ++ b :: a :: l₂) (hcols ▸ perm_swap_middle l₁ l₂ a b) with hG₂
  obtain ⟨G', hc', hr', hO', hX', hm'⟩ :=
    G.exists_mergeX_down (Or.inl hcols) hrows hOa hXa hXb hOb hmid
  obtain ⟨G'', hc'', hr'', hO'', hX'', hm''⟩ :=
    G₂.exists_mergeX_down (c := a) (d := b) (Or.inr rfl) hrows hOa hXa hXb hOb hmid
  have he : G'.toGrid = G''.toGrid := toGrid_eq_of_data _ _ (hc'.trans hc''.symm)
    (hr'.trans hr''.symm) (fun c _ => by rw [hO', hO'']; rfl)
    (fun c _ => by rw [hX', hX'']; rfl)
  rw [he] at hm'
  exact hm'.trans hm''.symm

end OnLeConjecture.KnotTheory.MarkedCancel
