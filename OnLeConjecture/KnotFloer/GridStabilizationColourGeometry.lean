/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationColourWeights

/-!
# The O columns of the short matching paths of a stabilization

For the stabilization `A = G.stabilizeX s.castSucc (G.X s).castSucc s`, every two-rectangle
matching path consists of an entry `e` and an exit `f`, and every three-rectangle matching path
of an entry `e`, an advancing middle rectangle `m` and an exit `f`. The reconstructed center
rectangle `ρ` of the path (`stabilizationMatchingTwoPathRectangle`,
`stabilizationMatchingThreePathRectangle`) contains the inserted center in its interior.

This file proves that the `O` columns of the pieces of a path are pairwise disjoint and that
their union is the set of `O` columns of `ρ` with the new column `s.castSucc` removed
(`OColumns_stabilizationMatchingTwoPath`, `OColumns_stabilizationMatchingThreePath`). The pieces
cover `ρ` except for its squares in the new row. The new `O` marking is the only `O` marking in
that row, so only the new column is lost.

Consequently every weight that is multiplicative over disjoint column sets takes the same value on
a path and on the new-column deletion of its rectangle. The Maslov computation of
`GridStabilizationMatchingWeights` gives the corresponding identity of cardinalities only.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-! ### Cyclic intervals -/

section CyclicIntervals

variable {N : ℕ}

theorem cIco_split_iff {L m R c : Fin N} (hm : m ∈ Grid.cIoo L R) :
    c ∈ Grid.cIco L R ↔ c ∈ Grid.cIco L m ∨ c ∈ Grid.cIco m R := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

theorem not_mem_cIco_of_mem_cIco_split {L m R c : Fin N} (hm : m ∈ Grid.cIoo L R)
    (hc : c ∈ Grid.cIco L m) : c ∉ Grid.cIco m R := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff] at *
  split_ifs at * <;> omega

variable {n : ℕ} {q : Fin n}

theorem cIco_castSucc_iff {t o : Fin (n + 1)} (h : q.succ ∈ Grid.cIoo q.castSucc t) :
    o ∈ Grid.cIco q.castSucc t ↔ o = q.castSucc ∨ o ∈ Grid.cIco q.succ t := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at *
  split_ifs at * <;> omega

theorem castSucc_not_mem_cIco_succ {t : Fin (n + 1)} (h : q.succ ∈ Grid.cIoo q.castSucc t) :
    q.castSucc ∉ Grid.cIco q.succ t := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at *
  split_ifs at * <;> omega

theorem cIco_three_iff {B t o : Fin (n + 1)} (h : q.succ ∈ Grid.cIoo B t) :
    o ∈ Grid.cIco B t ↔
      o ∈ Grid.cIco B q.castSucc ∨ o = q.castSucc ∨ o ∈ Grid.cIco q.succ t := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at h ⊢
  split_ifs at h ⊢ <;> omega

theorem not_mem_cIco_succ_of_mem_cIco_castSucc {B t o : Fin (n + 1)}
    (h : q.succ ∈ Grid.cIoo B t) (ho : o ∈ Grid.cIco B q.castSucc) :
    o ∉ Grid.cIco q.succ t := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at h ho ⊢
  split_ifs at h ho ⊢ <;> omega

theorem castSucc_not_mem_cIco_three {B t : Fin (n + 1)} (h : q.succ ∈ Grid.cIoo B t) :
    q.castSucc ∉ Grid.cIco B q.castSucc ∧ q.castSucc ∉ Grid.cIco q.succ t := by
  simp only [Grid.mem_cIoo, Grid.mem_cIco, ne_eq, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ] at h ⊢
  constructor <;> split_ifs at h ⊢ <;> omega

end CyclicIntervals

/-! ### Membership in the O columns of a rectangle -/

theorem mem_OColumns_rectangleBetween {N : ℕ} (H : GridDiagram N) {x y : GridState N}
    (r : GridRectangleBetween x y) (c : Fin N) :
    c ∈ H.OColumns r.toGridRectangle ↔
      c ∈ Grid.cIco r.left r.right ∧ H.O c ∈ Grid.cIco r.bottom r.top := by
  rw [GridDiagram.mem_OColumns, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows]
  rfl

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) {x y : GridState n}

set_option quotPrecheck false in
local notation "𝔸" => G.stabilizeX s.castSucc (G.X s).castSucc s

theorem stabilizeX_O_apply_eq_newRow_iff (c : Fin (n + 1)) :
    (𝔸).O c = (G.X s).castSucc ↔ c = s.castSucc := by
  rw [GridDiagram.stabilizeX_O]
  exact GridDiagram.stabilizeX_O_eq_castSucc_iff G s c

/-- The O columns of a two-rectangle matching path are disjoint and cover the reconstructed
rectangle except for the new column. -/
theorem OColumns_stabilizationMatchingTwoPath (p : StabilizationMatchingTwoPath G s x y) :
    Disjoint ((𝔸).OColumns p.2.1.val.toGridRectangle)
        ((𝔸).OColumns p.2.2.val.toGridRectangle) ∧
      (𝔸).OColumns p.2.1.val.toGridRectangle ∪
          (𝔸).OColumns p.2.2.val.toGridRectangle =
        ((𝔸).OColumns
          (stabilizationMatchingTwoPathRectangle G s p).toGridRectangle).erase s.castSucc := by
  classical
  have hprop := stabilizationMatchingTwoPathRectangle_properties G s p
  obtain ⟨z, ⟨e, he⟩, ⟨f, hf⟩⟩ := p
  have es := stabilizationMatchingEntry_shape G s x z e he
  have fs := stabilizationMatchingExit_shape G s z y f hf
  set ρ := stabilizationMatchingTwoPathRectangle G s ⟨z, ⟨e, he⟩, ⟨f, hf⟩⟩ with hρ
  have hL : ρ.left = z.val.transpose (G.X s).succ := rfl
  have hR : ρ.right = z.val.transpose (G.X s).castSucc := rfl
  have hB : ρ.bottom = (G.X s).castSucc := hprop.2.2
  have hT : ρ.top = z.val s.succ :=
    stabilizationMatchingTwoCenterRectangle_top G s x y z e he f hf
  have hi := (GridRectangleBetween.mem_toGridRectangle_interior ρ).mp hprop.2.1
  have hcol : s.succ ∈ Grid.cIoo ρ.left ρ.right := hi.1
  have hrow : (G.X s).succ ∈ Grid.cIoo ρ.bottom ρ.top := by
    rw [ρ.bottom_def, ρ.top_def]
    exact hi.2
  rw [hL, hR] at hcol
  rw [hB, hT] at hrow
  have hmemE (c : Fin (n + 1)) : c ∈ (𝔸).OColumns e.toGridRectangle ↔
      c ∈ Grid.cIco s.succ (z.val.transpose (G.X s).castSucc) ∧
        (𝔸).O c ∈ Grid.cIco (G.X s).succ (z.val s.succ) := by
    rw [mem_OColumns_rectangleBetween, es.1, es.2.1, es.2.2.1, es.2.2.2]
  have hmemF (c : Fin (n + 1)) : c ∈ (𝔸).OColumns f.toGridRectangle ↔
      c ∈ Grid.cIco (z.val.transpose (G.X s).succ) s.succ ∧
        (𝔸).O c ∈ Grid.cIco (G.X s).succ (z.val s.succ) := by
    rw [mem_OColumns_rectangleBetween, fs.1, fs.2.1, fs.2.2.1, fs.2.2.2]
  have hmemρ (c : Fin (n + 1)) : c ∈ (𝔸).OColumns ρ.toGridRectangle ↔
      c ∈ Grid.cIco (z.val.transpose (G.X s).succ) (z.val.transpose (G.X s).castSucc) ∧
        (𝔸).O c ∈ Grid.cIco (G.X s).castSucc (z.val s.succ) := by
    rw [mem_OColumns_rectangleBetween, hL, hR, hB, hT]
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro c hcE hcF
    rw [hmemE] at hcE
    rw [hmemF] at hcF
    exact not_mem_cIco_of_mem_cIco_split hcol hcF.1 hcE.1
  · ext c
    rw [Finset.mem_union, Finset.mem_erase, hmemE, hmemF, hmemρ, cIco_split_iff hcol,
      cIco_castSucc_iff hrow, stabilizeX_O_apply_eq_newRow_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨fun hc => castSucc_not_mem_cIco_succ hrow ?_, Or.inr h1, Or.inr h2⟩
        have hO := (stabilizeX_O_apply_eq_newRow_iff G s c).mpr hc
        rw [hO] at h2
        exact h2
      · refine ⟨fun hc => castSucc_not_mem_cIco_succ hrow ?_, Or.inl h1, Or.inr h2⟩
        have hO := (stabilizeX_O_apply_eq_newRow_iff G s c).mpr hc
        rw [hO] at h2
        exact h2
    · rintro ⟨hne, h1, h2 | h2⟩
      · exact absurd h2 hne
      · rcases h1 with h1 | h1
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩

/-- The O columns of a three-rectangle matching path are pairwise disjoint and cover the
reconstructed rectangle except for the new column. -/
theorem OColumns_stabilizationMatchingThreePath (p : StabilizationMatchingThreePath G s x y) :
    Disjoint ((𝔸).OColumns p.2.2.1.val.toGridRectangle)
        ((𝔸).OColumns
          p.2.2.2.1.val.toGridRectangle) ∧
      Disjoint ((𝔸).OColumns
            p.2.2.1.val.toGridRectangle ∪
          (𝔸).OColumns p.2.2.2.1.val.toGridRectangle)
        ((𝔸).OColumns
          p.2.2.2.2.val.toGridRectangle) ∧
      (𝔸).OColumns p.2.2.1.val.toGridRectangle ∪
            (𝔸).OColumns
              p.2.2.2.1.val.toGridRectangle ∪
          (𝔸).OColumns p.2.2.2.2.val.toGridRectangle =
        ((𝔸).OColumns
          (stabilizationMatchingThreePathRectangle G s p).toGridRectangle).erase s.castSucc := by
  classical
  have hprop := stabilizationMatchingThreePathRectangle_properties G s p
  obtain ⟨a, ⟨b, hab⟩, ⟨e, he⟩, ⟨m, hm, hmt⟩, ⟨f, hf⟩⟩ := p
  dsimp only [stabilizationMatchingThreePathRectangle] at hprop ⊢
  have es := stabilizationMatchingEntry_shape G s x a e he
  have ms := stabilizationMatchingTransition_advancing_columns G s a b hab m hmt
  have fs := stabilizationMatchingExit_shape G s b y f hf
  have hab' : a.val s.succ = b.val s.succ := stabilizationMatchingTransition_newColumn G s a b m
  generalize hρ : stabilizationMatchingThreeCenterRectangle G s x y a b hab e he m hmt f hf = ρ
    at hprop ⊢
  have hL : ρ.left = b.val.transpose (G.X s).succ := by
    rw [← hρ]; exact stabilizationMatchingThreeCenterRectangle_left G s x y a b hab e he m hmt f hf
  have hR : ρ.right = a.val.transpose (G.X s).castSucc := by
    rw [← hρ]
    exact stabilizationMatchingThreeCenterRectangle_right G s x y a b hab e he m hmt f hf
  have hB : ρ.bottom = m.bottom := by
    rw [← hρ]
    exact stabilizationMatchingThreeCenterRectangle_bottom G s x y a b hab e he m hmt f hf
  have hT : ρ.top = a.val s.succ := by
    rw [← hρ]
    exact stabilizationMatchingThreeCenterRectangle_top G s x y a b hab e he m hmt f hf
  have hi := (GridRectangleBetween.mem_toGridRectangle_interior ρ).mp hprop.2.1
  have hcol : s.succ ∈ Grid.cIoo ρ.left ρ.right := hi.1
  have hrow : (G.X s).succ ∈ Grid.cIoo ρ.bottom ρ.top := by
    rw [ρ.bottom_def, ρ.top_def]
    exact hi.2
  rw [hL, hR] at hcol
  rw [hB, hT] at hrow
  have hmemE (c : Fin (n + 1)) : c ∈ (𝔸).OColumns e.toGridRectangle ↔
      c ∈ Grid.cIco s.succ (a.val.transpose (G.X s).castSucc) ∧
        (𝔸).O c ∈ Grid.cIco (G.X s).succ (a.val s.succ) := by
    rw [mem_OColumns_rectangleBetween, es.1, es.2.1, es.2.2.1, es.2.2.2]
  have hmemM (c : Fin (n + 1)) : c ∈ (𝔸).OColumns m.toGridRectangle ↔
      c ∈ Grid.cIco (b.val.transpose (G.X s).succ) (a.val.transpose (G.X s).castSucc) ∧
        (𝔸).O c ∈ Grid.cIco m.bottom (G.X s).castSucc := by
    rw [mem_OColumns_rectangleBetween, ms.1, ms.2.1, hmt]
  have hmemF (c : Fin (n + 1)) : c ∈ (𝔸).OColumns f.toGridRectangle ↔
      c ∈ Grid.cIco (b.val.transpose (G.X s).succ) s.succ ∧
        (𝔸).O c ∈ Grid.cIco (G.X s).succ (a.val s.succ) := by
    rw [mem_OColumns_rectangleBetween, fs.1, fs.2.1, fs.2.2.1, fs.2.2.2, hab']
  have hmemρ (c : Fin (n + 1)) : c ∈ (𝔸).OColumns ρ.toGridRectangle ↔
      c ∈ Grid.cIco (b.val.transpose (G.X s).succ) (a.val.transpose (G.X s).castSucc) ∧
        (𝔸).O c ∈ Grid.cIco m.bottom (a.val s.succ) := by
    rw [mem_OColumns_rectangleBetween, hL, hR, hB, hT]
  have hnot := castSucc_not_mem_cIco_three hrow
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro c hcE hcM
    rw [hmemE] at hcE
    rw [hmemM] at hcM
    exact not_mem_cIco_succ_of_mem_cIco_castSucc hrow hcM.2 hcE.2
  · rw [Finset.disjoint_left]
    intro c hcEM hcF
    rw [hmemF] at hcF
    rcases Finset.mem_union.mp hcEM with hcE | hcM
    · rw [hmemE] at hcE
      exact not_mem_cIco_of_mem_cIco_split hcol hcF.1 hcE.1
    · rw [hmemM] at hcM
      exact not_mem_cIco_succ_of_mem_cIco_castSucc hrow hcM.2 hcF.2
  · ext c
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_erase, hmemE, hmemM, hmemF, hmemρ,
      cIco_three_iff hrow, stabilizeX_O_apply_eq_newRow_iff]
    have hsplit := cIco_split_iff (c := c) hcol
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · refine ⟨fun hc => hnot.2 ?_, hsplit.mpr (Or.inr h1), Or.inr (Or.inr h2)⟩
        have hO := (stabilizeX_O_apply_eq_newRow_iff G s c).mpr hc
        rw [hO] at h2
        exact h2
      · refine ⟨fun hc => hnot.1 ?_, h1, Or.inl h2⟩
        have hO := (stabilizeX_O_apply_eq_newRow_iff G s c).mpr hc
        rw [hO] at h2
        exact h2
      · refine ⟨fun hc => hnot.2 ?_, hsplit.mpr (Or.inl h1), Or.inr (Or.inr h2)⟩
        have hO := (stabilizeX_O_apply_eq_newRow_iff G s c).mpr hc
        rw [hO] at h2
        exact h2
    · rintro ⟨hne, h1, h2 | h2 | h2⟩
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact absurd h2 hne
      · rcases hsplit.mp h1 with h1 | h1
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl (Or.inl ⟨h1, h2⟩)

end OnLeConjecture.KnotFloer.GridFull
