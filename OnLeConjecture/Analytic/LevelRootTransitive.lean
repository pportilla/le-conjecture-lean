/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootCellPieces
public import OnLeConjecture.Analytic.LevelRootAssembly

/-!
# Transitivity of the monodromy of the based grid loops

This module proves `GridTransitivityStatement` (`LevelRootInput.lean`): for a root family over
`U` and a grid whose marked cells have centers in their interiors with the punctured closed cells
in `U`, if the total space of the family over the closed grid rectangle minus the centers is
preconnected, the monodromies of the based loops of the marked cells generate a transitive group.
This is the last paragraph of the subsection "Global factorization, exponent count, and
transitivity" of Section 3 of the written proof of Statement E (`statement-E-complete-proof.tex`),
in the following form, which uses no presentation of a fundamental group.

Let `Γ` be the group of the based loops (`basedLoopGroup`) and let `O` be a `Γ`-orbit of labels
over the base vertex. The grid rectangle minus the centers is covered by finitely many convex
pieces: the unmarked closed cells and the four punctured quadrants of the marked cells. Each piece
carries a labelling of the roots (`LevelRootCellPieces.lean`). Over a grid edge the labels are
compared with the reference labels `gridRef i j z`, continued from the labels `vertT i j` of the
based loops at the vertex `(i, j)` along the edge; at a vertex all reference labels are related
by `Γ` (`IsRootFamily.exists_vertical_defect`). Hence the labellings of any two pieces at a common
point differ by an element of `Γ` (`exists_pieces`). The points of the total space whose label in
some piece lies in `O`, and those whose label in some piece does not lie in `O`, form two disjoint
closed sets covering the total space; by preconnectedness one of them is empty.

`levelRootFamilyStatement_of_projectionInput` proves `LevelRootFamilyStatement` from
`LevelProjectionStatement`.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ} {Z : ℂ → Set ℂ} {U : Set ℂ}

/-! ### Labels related by a group -/

/-- The labels `f'` are the labels `f` relabelled by an element of `H`. -/
def LabelRel (H : Subgroup (Equiv.Perm (Fin S))) (f f' : Fin S → ℂ) : Prop :=
  ∃ ρ ∈ H, f' = f ∘ ρ

namespace LabelRel

variable {H : Subgroup (Equiv.Perm (Fin S))} {f f' f'' : Fin S → ℂ}

theorem of_eq (h : f' = f) : LabelRel H f f' := ⟨1, H.one_mem, by rw [h]; rfl⟩

theorem of_comp {ρ : Equiv.Perm (Fin S)} (hρ : ρ ∈ H) (h : f' = f ∘ ρ) : LabelRel H f f' :=
  ⟨ρ, hρ, h⟩

theorem symm (h : LabelRel H f f') : LabelRel H f' f := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  exact ⟨ρ⁻¹, H.inv_mem hρ, by funext k; simp⟩

theorem trans (h : LabelRel H f f') (h' : LabelRel H f' f'') : LabelRel H f f'' := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  obtain ⟨ρ', hρ', rfl⟩ := h'
  exact ⟨ρ * ρ', H.mul_mem hρ hρ', by funext k; simp⟩

end LabelRel

/-- Transport along a constant segment. -/
theorem segT_self {p : ℂ} {f : Fin S → ℂ} (hf : IsFibreLabel Z p f) : segT Z p p f = f := by
  have hK : IsSegLabel Z p p f fun k _ => f k := by
    refine ⟨⟨fun k => continuousOn_const, fun t _ => hf.1, fun t _ => ?_⟩, fun k => rfl⟩
    rw [hf.2]
    simp [segmentPath]
  rw [segT_eq hK]

/-! ### Grid edges and reference labels -/

section Grid

variable {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

/-- The horizontal edge from `(i, j)` to `(i + 1, j)`. -/
def hEdge (xs ys : ℕ → ℝ) (i j : ℕ) : Set ℂ := rectSet (xs i) (xs (i + 1)) (ys j) (ys j)

/-- The vertical edge from `(i, j)` to `(i, j + 1)`. -/
def vEdge (xs ys : ℕ → ℝ) (i j : ℕ) : Set ℂ := rectSet (xs i) (xs i) (ys j) (ys (j + 1))

/-- `z` lies on a grid edge starting at the vertex `(i, j)`. -/
def OnEdge (xs ys : ℕ → ℝ) (n i j : ℕ) (z : ℂ) : Prop :=
  (i < n ∧ j ≤ n ∧ z ∈ hEdge xs ys i j) ∨ (i ≤ n ∧ j < n ∧ z ∈ vEdge xs ys i j)

theorem IsRootGrid.hEdge_subset (G : IsRootGrid U xs ys n marked) {i j : ℕ} (hi : i < n)
    (hj : j ≤ n) : hEdge xs ys i j ⊆ U := by
  intro z hz
  have h1 := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le i) hi.le
  have h2 := le_of_lt_succ_of_le G.xs_lt (Nat.succ_le_of_lt hi) le_rfl
  have hzz : z = ⟨z.re, ys j⟩ := Complex.ext rfl (le_antisymm hz.2.2 hz.2.1)
  rw [hzz]
  exact G.horizontal j hj _ ⟨h1.trans hz.1.1, hz.1.2.trans h2⟩

theorem IsRootGrid.vEdge_subset (G : IsRootGrid U xs ys n marked) {i j : ℕ} (hi : i ≤ n)
    (hj : j < n) : vEdge xs ys i j ⊆ U := by
  intro z hz
  have h1 := le_of_lt_succ_of_le G.ys_lt (Nat.zero_le j) hj.le
  have h2 := le_of_lt_succ_of_le G.ys_lt (Nat.succ_le_of_lt hj) le_rfl
  have hzz : z = ⟨xs i, z.im⟩ := Complex.ext (le_antisymm hz.1.2 hz.1.1) rfl
  rw [hzz]
  exact G.vertical i hi _ ⟨h1.trans hz.2.1, hz.2.2.trans h2⟩

theorem IsRootGrid.xs_inj (G : IsRootGrid U xs ys n marked) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (h : xs a = xs b) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact (lt_of_lt_succ_of_lt G.xs_lt hab hb).ne h
  · exact (lt_of_lt_succ_of_lt G.xs_lt hab ha).ne' h

theorem IsRootGrid.ys_inj (G : IsRootGrid U xs ys n marked) {a b : ℕ} (ha : a ≤ n) (hb : b ≤ n)
    (h : ys a = ys b) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hab
  · exact (lt_of_lt_succ_of_lt G.ys_lt hab hb).ne h
  · exact (lt_of_lt_succ_of_lt G.ys_lt hab ha).ne' h

/-- A value between two consecutive values of a strictly increasing sequence is one of them,
when it is itself a value. -/
theorem eq_or_eq_of_mem_Icc {f : ℕ → ℝ} (hf : ∀ i < n, f i < f (i + 1)) {i a : ℕ} (hi : i < n)
    (ha : a ≤ n) (h : f a ∈ Icc (f i) (f (i + 1))) : a = i ∨ a = i + 1 := by
  by_contra hne
  push Not at hne
  rcases lt_or_gt_of_ne hne.1 with h1 | h1
  · exact absurd h.1 (not_le.mpr (lt_of_lt_succ_of_lt hf h1 hi.le))
  · have : i + 1 < a := by omega
    exact absurd h.2 (not_le.mpr (lt_of_lt_succ_of_lt hf this ha))

/-- Two consecutive intervals of a strictly increasing sequence meet only at their common end. -/
theorem eq_of_mem_Icc_Icc {f : ℕ → ℝ} (hf : ∀ i < n, f i < f (i + 1)) {p p' : ℕ} {x : ℝ}
    (hpp : p < p') (hp' : p' < n) (h : x ∈ Icc (f p) (f (p + 1)))
    (h' : x ∈ Icc (f p') (f (p' + 1))) : x = f (p + 1) :=
  le_antisymm h.2 ((le_of_lt_succ_of_le hf (Nat.succ_le_of_lt hpp) hp'.le).trans h'.1)

/-- A point of `[f 0, f n]` lies in some `[f i, f (i + 1)]` with `i < n`. -/
theorem exists_Icc_index {f : ℕ → ℝ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Icc (f 0) (f n)) : ∃ i < n, x ∈ Icc (f i) (f (i + 1)) := by
  classical
  set i := Nat.findGreatest (fun i => f i ≤ x) (n - 1) with hi
  have hile : i ≤ n - 1 := Nat.findGreatest_le _
  have hfi : f i ≤ x := Nat.findGreatest_spec (P := fun i => f i ≤ x) (Nat.zero_le _) hx.1
  refine ⟨i, by omega, hfi, ?_⟩
  by_cases h : i + 1 ≤ n - 1
  · have hnot : ¬ f (i + 1) ≤ x := Nat.findGreatest_is_greatest (Nat.lt_succ_self i) h
    exact (not_le.mp hnot).le
  · rw [show i + 1 = n by omega]; exact hx.2

variable (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) {f₀ : Fin S → ℂ}
  (hf₀ : IsFibreLabel Z (gridPoint xs ys 0 0) f₀)

/-- The reference labels at `z`, continued from `vertT i j` at the vertex `(i, j)` along the
segment to `z`. -/
def gridRef (Z : ℂ → Set ℂ) (xs ys : ℕ → ℝ) (f₀ : Fin S → ℂ) (i j : ℕ) (z : ℂ) : Fin S → ℂ :=
  segT Z (gridPoint xs ys i j) z (vertT Z xs ys f₀ i j)

include hZ G hf₀

omit hZ G hf₀ in
/-- A labelling of an edge normalized at its first vertex computes the reference labels. -/
theorem gridRef_eq_of_labelling {D : Set ℂ} (hD : Convex ℝ D) {Λ : Fin S → ℂ → ℂ}
    (hΛ : IsRootLabellingOn Z id D Λ) {i j : ℕ} (hv : gridPoint xs ys i j ∈ D)
    (h0 : ∀ k, Λ k (gridPoint xs ys i j) = vertT Z xs ys f₀ i j k) {z : ℂ} (hz : z ∈ D) :
    gridRef Z xs ys f₀ i j z = fun k => Λ k z := by
  unfold gridRef
  rw [show vertT Z xs ys f₀ i j = fun k => Λ k (gridPoint xs ys i j) from
    funext fun k => (h0 k).symm]
  exact segT_of_labelling hΛ (mapsTo_segmentPath_of_convex hD hv hz)

/-- The labelling of an edge normalized at its first vertex. -/
theorem exists_edge_labelling {D : Set ℂ} (hD : Convex ℝ D) (hDU : D ⊆ U) {i j : ℕ}
    (hi : i ≤ n) (hj : j ≤ n) (hv : gridPoint xs ys i j ∈ D) :
    ∃ Λ : Fin S → ℂ → ℂ, IsRootLabellingOn Z id D Λ ∧
      (∀ k, Λ k (gridPoint xs ys i j) = vertT Z xs ys f₀ i j k) ∧
      ∀ z ∈ D, gridRef Z xs ys f₀ i j z = fun k => Λ k z := by
  obtain ⟨Λ, hΛ, h0⟩ := hZ.exists_convex_labelling hD hDU hv
    (hZ.isFibreLabel_vertT G hf₀ i hi j hj)
  exact ⟨Λ, hΛ, h0, fun z hz => gridRef_eq_of_labelling hD hΛ hv h0 hz⟩

/-- **Reference labels at a vertex** are related by the group of the based loops to the labels
of the based loops. -/
theorem labelRel_vertT_gridRef {p q a b : ℕ} {z : ℂ} (hz : OnEdge xs ys n p q z)
    (hza : z = gridPoint xs ys a b) (ha : a ≤ n) (hb : b ≤ n) :
    LabelRel (basedLoopGroup Z xs ys marked f₀) (vertT Z xs ys f₀ a b)
      (gridRef Z xs ys f₀ p q z) := by
  subst hza
  rcases hz with ⟨hp, hq, hzE⟩ | ⟨hp, hq, hzE⟩
  · have hbq : b = q := G.ys_inj hb hq (le_antisymm hzE.2.2 hzE.2.1)
    subst hbq
    rcases eq_or_eq_of_mem_Icc G.xs_lt hp ha hzE.1 with rfl | rfl
    · exact LabelRel.of_eq (segT_self (hZ.isFibreLabel_vertT G hf₀ a ha b hb))
    · exact LabelRel.of_eq rfl
  · have hap : a = p := G.xs_inj ha hp (le_antisymm hzE.1.2 hzE.1.1)
    subst hap
    rcases eq_or_eq_of_mem_Icc G.ys_lt hq hb hzE.2 with rfl | rfl
    · exact LabelRel.of_eq (segT_self (hZ.isFibreLabel_vertT G hf₀ a ha b hb))
    · obtain ⟨g, hg, hgeq⟩ := hZ.exists_vertical_defect G hf₀ a ha q hq
      exact LabelRel.of_comp hg hgeq

/-- **Reference labels at one point** are related by the group of the based loops. -/
theorem labelRel_gridRef {p q p' q' : ℕ} {z : ℂ} (hz : OnEdge xs ys n p q z)
    (hz' : OnEdge xs ys n p' q' z) :
    LabelRel (basedLoopGroup Z xs ys marked f₀) (gridRef Z xs ys f₀ p q z)
      (gridRef Z xs ys f₀ p' q' z) := by
  by_cases hpq : p = p' ∧ q = q'
  · obtain ⟨rfl, rfl⟩ := hpq
    exact LabelRel.of_eq rfl
  -- The point is a common vertex.
  suffices h : ∃ a ≤ n, ∃ b ≤ n, z = gridPoint xs ys a b by
    obtain ⟨a, ha, b, hb, hzab⟩ := h
    exact (labelRel_vertT_gridRef hZ G hf₀ hz hzab ha hb).symm.trans
      (labelRel_vertT_gridRef hZ G hf₀ hz' hzab ha hb)
  have hpt : ∀ {a b : ℕ}, z.re = xs a → z.im = ys b → z = gridPoint xs ys a b :=
    fun h1 h2 => Complex.ext h1 h2
  rcases hz with ⟨hp, hq, hzE⟩ | ⟨hp, hq, hzE⟩ <;>
    rcases hz' with ⟨hp', hq', hzE'⟩ | ⟨hp', hq', hzE'⟩
  · have hqq : q = q' := G.ys_inj hq hq' ((le_antisymm hzE.2.2 hzE.2.1).symm.trans
      (le_antisymm hzE'.2.2 hzE'.2.1))
    have hne : p ≠ p' := fun h => hpq ⟨h, hqq⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨p + 1, by omega, q, hq, hpt (eq_of_mem_Icc_Icc G.xs_lt h hp' hzE.1 hzE'.1)
        (le_antisymm hzE.2.2 hzE.2.1)⟩
    · exact ⟨p' + 1, by omega, q, hq, hpt (eq_of_mem_Icc_Icc G.xs_lt h hp hzE'.1 hzE.1)
        (le_antisymm hzE.2.2 hzE.2.1)⟩
  · exact ⟨p', hp', q, hq, hpt (le_antisymm hzE'.1.2 hzE'.1.1) (le_antisymm hzE.2.2 hzE.2.1)⟩
  · exact ⟨p, hp, q', hq', hpt (le_antisymm hzE.1.2 hzE.1.1) (le_antisymm hzE'.2.2 hzE'.2.1)⟩
  · have hpp : p = p' := G.xs_inj hp hp' ((le_antisymm hzE.1.2 hzE.1.1).symm.trans
      (le_antisymm hzE'.1.2 hzE'.1.1))
    have hne : q ≠ q' := fun h => hpq ⟨hpp, h⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨p, hp, q + 1, by omega, hpt (le_antisymm hzE.1.2 hzE.1.1)
        (eq_of_mem_Icc_Icc G.ys_lt h hq' hzE.2 hzE'.2)⟩
    · exact ⟨p, hp, q' + 1, by omega, hpt (le_antisymm hzE.1.2 hzE.1.1)
        (eq_of_mem_Icc_Icc G.ys_lt h hq hzE'.2 hzE.2)⟩

end Grid

/-! ### The pieces of a cell -/

section Pieces

variable {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

/-- The center of a marked cell, removed from its pieces. -/
def puncture (marked : ℕ → ℕ → Prop) (center : ℕ → ℕ → ℂ) (i j : ℕ) : Set ℂ :=
  {z | marked i j ∧ z = center i j}

/-- The relations of the labelling of a piece of the cell `(i, j)` with the reference labels on
the sides of the cell. -/
def SideRel (Z : ℂ → Set ℂ) (xs ys : ℕ → ℝ) (marked : ℕ → ℕ → Prop) (f₀ : Fin S → ℂ)
    (i j : ℕ) (z : ℂ) (F : Fin S → ℂ) : Prop :=
  (z.im = ys j → LabelRel (basedLoopGroup Z xs ys marked f₀) (gridRef Z xs ys f₀ i j z) F) ∧
  (z.re = xs i → LabelRel (basedLoopGroup Z xs ys marked f₀) (gridRef Z xs ys f₀ i j z) F) ∧
  (z.re = xs (i + 1) →
    LabelRel (basedLoopGroup Z xs ys marked f₀) (gridRef Z xs ys f₀ (i + 1) j z) F) ∧
  (z.im = ys (j + 1) →
    LabelRel (basedLoopGroup Z xs ys marked f₀) (gridRef Z xs ys f₀ i (j + 1) z) F)

variable (hZ : IsRootFamily Z S U) (G : IsRootGrid U xs ys n marked) {center : ℕ → ℕ → ℂ}
  (hc : ∀ a < n, ∀ b < n, marked a b → center a b ∈ gridCellInterior xs ys a b ∧
    gridCell xs ys a b \ {center a b} ⊆ U)
  {f₀ : Fin S → ℂ} (hf₀ : IsFibreLabel Z (gridPoint xs ys 0 0) f₀)

include hZ G hc hf₀

/-- The quadrant `q` of the rectangle `[x₀, x₁] × [y₀, y₁]` around `m`: `q.1` chooses the right
half, `q.2` the upper half. -/
def quadPiece (x₀ x₁ y₀ y₁ : ℝ) (m : ℂ) (q : Bool × Bool) : Set ℂ :=
  rectSet (bif q.1 then m.re else x₀) (bif q.1 then x₁ else m.re)
    (bif q.2 then m.im else y₀) (bif q.2 then y₁ else m.im)

/-- The labellings of the four quadrants. -/
def quadLab (Λ₀ Λ₁ Λ₂ Λ₃ : Fin S → ℂ → ℂ) : Bool × Bool → Fin S → ℂ → ℂ
  | (false, false) => Λ₀
  | (true, false) => Λ₁
  | (true, true) => Λ₂
  | (false, true) => Λ₃

/-- **The pieces of a cell.** Every cell is covered by four closed pieces, minus its puncture,
with labellings related to the reference labels on the sides of the cell and to each other by
the group of the based loops. -/
theorem exists_cell_pieces {i j : ℕ} (hi : i < n) (hj : j < n) :
    ∃ (Qs : Bool × Bool → Set ℂ) (Λ : Bool × Bool → Fin S → ℂ → ℂ),
      (∀ q, IsClosed (Qs q)) ∧ (∀ q, Qs q ⊆ gridCell xs ys i j) ∧
      (∀ z ∈ gridCell xs ys i j, z ∉ puncture marked center i j → ∃ q, z ∈ Qs q) ∧
      (∀ q, IsRootLabellingOn Z id (Qs q \ puncture marked center i j) (Λ q)) ∧
      (∀ q, ∀ z ∈ Qs q \ puncture marked center i j,
        SideRel Z xs ys marked f₀ i j z fun k => Λ q k z) ∧
      ∀ q q', ∀ z ∈ (Qs q \ puncture marked center i j) ∩ (Qs q' \ puncture marked center i j),
        LabelRel (basedLoopGroup Z xs ys marked f₀) (fun k => Λ q k z) fun k => Λ q' k z := by
  classical
  set Γ := basedLoopGroup Z xs ys marked f₀
  have hx := G.xs_lt i hi
  have hy := G.ys_lt j hj
  have hi1 : i + 1 ≤ n := hi
  have hj1 : j + 1 ≤ n := hj
  -- The side labellings.
  have hv0B : gridPoint xs ys i j ∈ hEdge xs ys i j := mem_rectSet' ⟨le_rfl, hx.le⟩ ⟨le_rfl, le_rfl⟩
  have hv0L : gridPoint xs ys i j ∈ vEdge xs ys i j := mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨le_rfl, hy.le⟩
  have hv1R : gridPoint xs ys (i + 1) j ∈ vEdge xs ys (i + 1) j :=
    mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨le_rfl, hy.le⟩
  have hv3T : gridPoint xs ys i (j + 1) ∈ hEdge xs ys i (j + 1) :=
    mem_rectSet' ⟨le_rfl, hx.le⟩ ⟨le_rfl, le_rfl⟩
  obtain ⟨EB, hEB, hEB0, hEBr⟩ := exists_edge_labelling hZ G hf₀ (convex_rectSet _ _ _ _)
    (G.hEdge_subset hi hj.le) (i := i) (j := j) hi.le hj.le hv0B
  obtain ⟨EL, hEL, hEL0, hELr⟩ := exists_edge_labelling hZ G hf₀ (convex_rectSet _ _ _ _)
    (G.vEdge_subset hi.le hj) (i := i) (j := j) hi.le hj.le hv0L
  obtain ⟨ER, hER, hER0, hERr⟩ := exists_edge_labelling hZ G hf₀ (convex_rectSet _ _ _ _)
    (G.vEdge_subset hi1 hj) (i := i + 1) (j := j) hi1 hj.le hv1R
  obtain ⟨ET, hET, hET0, hETr⟩ := exists_edge_labelling hZ G hf₀ (convex_rectSet _ _ _ _)
    (G.hEdge_subset hi hj1) (i := i) (j := j + 1) hi.le hj1 hv3T
  -- The vertical defects of the two vertical sides.
  obtain ⟨g, hg, hgeq⟩ := hZ.exists_vertical_defect G hf₀ i hi.le j hj
  obtain ⟨g', hg', hg'eq⟩ := hZ.exists_vertical_defect G hf₀ (i + 1) hi1 j hj
  let ET' : Fin S → ℂ → ℂ := fun k z => ET (g k) z
  have hET'l : IsRootLabellingOn Z id (hEdge xs ys i (j + 1)) ET' := hET.relabel g
  have hv1B : gridPoint xs ys (i + 1) j ∈ hEdge xs ys i j :=
    mem_rectSet' ⟨hx.le, le_rfl⟩ ⟨le_rfl, le_rfl⟩
  have hv3L : gridPoint xs ys i (j + 1) ∈ vEdge xs ys i j :=
    mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨hy.le, le_rfl⟩
  have hv2R : gridPoint xs ys (i + 1) (j + 1) ∈ vEdge xs ys (i + 1) j :=
    mem_rectSet' ⟨le_rfl, le_rfl⟩ ⟨hy.le, le_rfl⟩
  have hv2T : gridPoint xs ys (i + 1) (j + 1) ∈ hEdge xs ys i (j + 1) :=
    mem_rectSet' ⟨hx.le, le_rfl⟩ ⟨le_rfl, le_rfl⟩
  have hBL : ∀ k, EL k ⟨xs i, ys j⟩ = EB k ⟨xs i, ys j⟩ := fun k => (hEL0 k).trans (hEB0 k).symm
  have hBR : ∀ k, ER k ⟨xs (i + 1), ys j⟩ = EB k ⟨xs (i + 1), ys j⟩ := by
    intro k
    have h1 := congrFun (hEBr _ hv1B) k
    change ER k (gridPoint xs ys (i + 1) j) = EB k (gridPoint xs ys (i + 1) j)
    rw [hER0 k]
    exact h1
  have hLT : ∀ k, ET' k ⟨xs i, ys (j + 1)⟩ = EL k ⟨xs i, ys (j + 1)⟩ := by
    intro k
    have h1 := congrFun (hELr _ hv3L) k
    change ET (g k) (gridPoint xs ys i (j + 1)) = EL k (gridPoint xs ys i (j + 1))
    rw [hET0, ← h1]
    exact (congrFun hgeq k).symm
  set π := g⁻¹ * g'
  have hπ : ∀ k, ER k ⟨xs (i + 1), ys (j + 1)⟩ = ET' (π k) ⟨xs (i + 1), ys (j + 1)⟩ := by
    intro k
    have h1 := congrFun (hERr _ hv2R) k
    have h2 := congrFun (hETr _ hv2T) (g (π k))
    have h3 : g (π k) = g' k := by simp [π]
    rw [h3] at h2
    change ER k (gridPoint xs ys (i + 1) (j + 1)) = ET (g (π k)) (gridPoint xs ys (i + 1) (j + 1))
    rw [h3, ← h2, ← h1]
    exact congrFun hg'eq k
  -- The reference labels on the sides.
  have rB : ∀ z ∈ hEdge xs ys i j, gridRef Z xs ys f₀ i j z = fun k => EB k z := hEBr
  have rL : ∀ z ∈ vEdge xs ys i j, gridRef Z xs ys f₀ i j z = fun k => EL k z := hELr
  have rR : ∀ z ∈ vEdge xs ys (i + 1) j, gridRef Z xs ys f₀ (i + 1) j z = fun k => ER k z := hERr
  have rT : ∀ z ∈ hEdge xs ys i (j + 1),
      (fun k => ET' k z) = gridRef Z xs ys f₀ i (j + 1) z ∘ g :=
    fun z hz => by rw [hETr z hz]; rfl
  by_cases hm : marked i j
  · -- A marked cell: the four punctured quadrants.
    obtain ⟨hint, hsub⟩ := hc i hi j hj hm
    set m := center i j
    have hpunct : puncture marked center i j = {m} := by
      ext z; simp [puncture, hm, m]
    obtain ⟨h0, h1⟩ := hint.1
    obtain ⟨h2, h3⟩ := hint.2
    obtain ⟨Λ₀, Λ₁, Λ₂, Λ₃, hΛ₀, hΛ₁, hΛ₂, hΛ₃, ea, eb, ed, ee, eg, eh, ej, ek, ec, ef, ei, el⟩ :=
      hZ.exists_quadrant_labellings h0 h1 h2 h3 hsub hEB hEL hER hET'l hBL hBR hLT π hπ
    have hπΓ : π ∈ Γ := Γ.mul_mem (Γ.inv_mem hg) hg'
    have hgπ : g * π ∈ Γ := Γ.mul_mem hg hπΓ
    have hTπ : ∀ z ∈ hEdge xs ys i (j + 1), (fun k => ET' (π k) z) =
        gridRef Z xs ys f₀ i (j + 1) z ∘ (g * π) := fun z hz => by
      funext k
      exact congrFun (rT z hz) (π k)
    set x₀ := xs i
    set x₁ := xs (i + 1)
    set y₀ := ys j
    set y₁ := ys (j + 1)
    refine ⟨quadPiece x₀ x₁ y₀ y₁ m, quadLab Λ₀ Λ₁ Λ₂ Λ₃, fun q => isClosed_rectSet _ _ _ _,
      fun q => ?_, fun z hz hzp => ?_, fun q => ?_, fun q z hz => ?_, fun q q' z hz => ?_⟩
    · rcases q with ⟨_ | _, _ | _⟩ <;>
        exact rectSet_subset (by simp; linarith) (by simp; linarith) (by simp; linarith)
          (by simp; linarith)
    · rcases le_total z.re m.re with hr | hr <;> rcases le_total z.im m.im with him | him
      · exact ⟨(false, false), ⟨hz.1.1, hr⟩, ⟨hz.2.1, him⟩⟩
      · exact ⟨(false, true), ⟨hz.1.1, hr⟩, ⟨him, hz.2.2⟩⟩
      · exact ⟨(true, false), ⟨hr, hz.1.2⟩, ⟨hz.2.1, him⟩⟩
      · exact ⟨(true, true), ⟨hr, hz.1.2⟩, ⟨him, hz.2.2⟩⟩
    · rw [hpunct]
      rcases q with ⟨_ | _, _ | _⟩
      · exact hΛ₀
      · exact hΛ₃
      · exact hΛ₁
      · exact hΛ₂
    · rw [hpunct] at hz
      obtain ⟨⟨hzr, hzi⟩, hzm⟩ := hz
      rcases q with ⟨_ | _, _ | _⟩
      · change z.re ∈ Icc x₀ m.re at hzr
        change z.im ∈ Icc y₀ m.im at hzi
        refine ⟨fun hz' => ?_, fun hz' => ?_, fun hz' => ?_, fun hz' => ?_⟩
        · have hB : z ∈ hEdge xs ys i j := ⟨⟨hzr.1, by linarith [hzr.2]⟩, ⟨hz'.ge, hz'.le⟩⟩
          refine LabelRel.of_eq ?_
          rw [rB z hB]
          exact funext fun k => ea k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hB⟩
        · have hL : z ∈ vEdge xs ys i j := ⟨⟨hz'.ge, hz'.le⟩, ⟨hzi.1, by linarith [hzi.2]⟩⟩
          refine LabelRel.of_eq ?_
          rw [rL z hL]
          exact funext fun k => eb k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hL⟩
        · exact absurd hz' (by linarith [hzr.2])
        · exact absurd hz' (by linarith [hzi.2])
      · change z.re ∈ Icc x₀ m.re at hzr
        change z.im ∈ Icc m.im y₁ at hzi
        refine ⟨fun hz' => ?_, fun hz' => ?_, fun hz' => ?_, fun hz' => ?_⟩
        · exact absurd hz' (by linarith [hzi.1])
        · have hL : z ∈ vEdge xs ys i j := ⟨⟨hz'.ge, hz'.le⟩, ⟨by linarith [hzi.1], hzi.2⟩⟩
          refine LabelRel.of_comp hπΓ ?_
          rw [rL z hL]
          exact funext fun k => ek k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hL⟩
        · exact absurd hz' (by linarith [hzr.2])
        · have hT : z ∈ hEdge xs ys i (j + 1) := ⟨⟨hzr.1, by linarith [hzr.2]⟩, ⟨hz'.ge, hz'.le⟩⟩
          refine LabelRel.of_comp hgπ ?_
          rw [← hTπ z hT]
          exact funext fun k => ej k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hT⟩
      · change z.re ∈ Icc m.re x₁ at hzr
        change z.im ∈ Icc y₀ m.im at hzi
        refine ⟨fun hz' => ?_, fun hz' => ?_, fun hz' => ?_, fun hz' => ?_⟩
        · have hB : z ∈ hEdge xs ys i j := ⟨⟨by linarith [hzr.1], hzr.2⟩, ⟨hz'.ge, hz'.le⟩⟩
          refine LabelRel.of_eq ?_
          rw [rB z hB]
          exact funext fun k => ed k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hB⟩
        · exact absurd hz' (by linarith [hzr.1])
        · have hR : z ∈ vEdge xs ys (i + 1) j :=
            ⟨⟨hz'.ge, hz'.le⟩, ⟨hzi.1, by linarith [hzi.2]⟩⟩
          refine LabelRel.of_eq ?_
          rw [rR z hR]
          exact funext fun k => ee k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hR⟩
        · exact absurd hz' (by linarith [hzi.2])
      · change z.re ∈ Icc m.re x₁ at hzr
        change z.im ∈ Icc m.im y₁ at hzi
        refine ⟨fun hz' => ?_, fun hz' => ?_, fun hz' => ?_, fun hz' => ?_⟩
        · exact absurd hz' (by linarith [hzi.1])
        · exact absurd hz' (by linarith [hzr.1])
        · have hR : z ∈ vEdge xs ys (i + 1) j :=
            ⟨⟨hz'.ge, hz'.le⟩, ⟨by linarith [hzi.1], hzi.2⟩⟩
          refine LabelRel.of_eq ?_
          rw [rR z hR]
          exact funext fun k => eg k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hR⟩
        · have hT : z ∈ hEdge xs ys i (j + 1) := ⟨⟨by linarith [hzr.1], hzr.2⟩, ⟨hz'.ge, hz'.le⟩⟩
          refine LabelRel.of_comp hgπ ?_
          rw [← hTπ z hT]
          exact funext fun k => eh k z ⟨⟨⟨hzr, hzi⟩, hzm⟩, hT⟩
    · rw [hpunct] at hz
      obtain ⟨⟨hzq, hzm⟩, ⟨hzq', -⟩⟩ := hz
      have hopp : m.re ≤ z.re → z.re ≤ m.re → m.im ≤ z.im → z.im ≤ m.im → False :=
        fun a b c d => hzm (Complex.ext (le_antisymm b a) (le_antisymm d c))
      have q0 : ∀ {z}, z ∈ quadPiece x₀ x₁ y₀ y₁ m (false, false) \ {m} →
          z ∈ rectSet x₀ m.re y₀ m.im \ {m} := id
      have q1 : ∀ {z}, z ∈ quadPiece x₀ x₁ y₀ y₁ m (true, false) \ {m} →
          z ∈ rectSet m.re x₁ y₀ m.im \ {m} := id
      have q2 : ∀ {z}, z ∈ quadPiece x₀ x₁ y₀ y₁ m (true, true) \ {m} →
          z ∈ rectSet m.re x₁ m.im y₁ \ {m} := id
      have q3 : ∀ {z}, z ∈ quadPiece x₀ x₁ y₀ y₁ m (false, true) \ {m} →
          z ∈ rectSet x₀ m.re m.im y₁ \ {m} := id
      rcases q with ⟨_ | _, _ | _⟩ <;> rcases q' with ⟨_ | _, _ | _⟩
      -- (ff, ·)
      · exact LabelRel.of_eq rfl
      · exact LabelRel.of_comp hπΓ (funext fun k => el k z ⟨q3 ⟨hzq', hzm⟩, q0 ⟨hzq, hzm⟩⟩)
      · exact LabelRel.of_eq (funext fun k => ec k z ⟨q0 ⟨hzq, hzm⟩, q1 ⟨hzq', hzm⟩⟩)
      · exact (hopp hzq'.1.1 hzq.1.2 hzq'.2.1 hzq.2.2).elim
      -- (ft, ·)
      · exact (LabelRel.of_comp hπΓ (funext fun k => el k z ⟨q3 ⟨hzq, hzm⟩,
          q0 ⟨hzq', hzm⟩⟩)).symm
      · exact LabelRel.of_eq rfl
      · exact (hopp hzq'.1.1 hzq.1.2 hzq.2.1 hzq'.2.2).elim
      · exact (LabelRel.of_eq (funext fun k => ei k z ⟨q2 ⟨hzq', hzm⟩,
          q3 ⟨hzq, hzm⟩⟩)).symm
      -- (tf, ·)
      · exact (LabelRel.of_eq (funext fun k => ec k z ⟨q0 ⟨hzq', hzm⟩, q1 ⟨hzq, hzm⟩⟩)).symm
      · exact (hopp hzq.1.1 hzq'.1.2 hzq'.2.1 hzq.2.2).elim
      · exact LabelRel.of_eq rfl
      · exact LabelRel.of_eq (funext fun k => ef k z ⟨q1 ⟨hzq, hzm⟩, q2 ⟨hzq', hzm⟩⟩)
      -- (tt, ·)
      · exact (hopp hzq.1.1 hzq'.1.2 hzq.2.1 hzq'.2.2).elim
      · exact LabelRel.of_eq (funext fun k => ei k z ⟨q2 ⟨hzq, hzm⟩, q3 ⟨hzq', hzm⟩⟩)
      · exact (LabelRel.of_eq (funext fun k => ef k z ⟨q1 ⟨hzq', hzm⟩,
          q2 ⟨hzq, hzm⟩⟩)).symm
      · exact LabelRel.of_eq rfl
  · -- An unmarked cell: one piece.
    have hpunct : puncture marked center i j = ∅ := by
      ext z; simp [puncture, hm]
    obtain ⟨Λc, hΛc, ea, eb, ec, ed⟩ := hZ.exists_rect_labelling hx.le hy.le
      (G.cell i hi j hj hm) hEB hEL hER hET'l hBL hBR hLT
    refine ⟨fun _ => gridCell xs ys i j, fun _ => Λc, fun _ => isClosed_rectSet _ _ _ _,
      fun _ => le_rfl, fun z hz _ => ⟨(false, false), hz⟩,
      fun q => by rw [hpunct, sdiff_empty]; exact hΛc,
      fun q z hz => ?_, fun q q' z _ => LabelRel.of_eq rfl⟩
    rw [hpunct, sdiff_empty] at hz
    obtain ⟨hzr, hzi⟩ := hz
    refine ⟨fun hz' => ?_, fun hz' => ?_, fun hz' => ?_, fun hz' => ?_⟩
    · have hB : z ∈ hEdge xs ys i j := ⟨hzr, ⟨hz'.ge, hz'.le⟩⟩
      exact LabelRel.of_eq (by rw [rB z hB]; exact funext fun k => ea k z ⟨⟨hzr, hzi⟩, hB⟩)
    · have hL : z ∈ vEdge xs ys i j := ⟨⟨hz'.ge, hz'.le⟩, hzi⟩
      exact LabelRel.of_eq (by rw [rL z hL]; exact funext fun k => eb k z ⟨⟨hzr, hzi⟩, hL⟩)
    · have hR : z ∈ vEdge xs ys (i + 1) j := ⟨⟨hz'.ge, hz'.le⟩, hzi⟩
      exact LabelRel.of_eq (by rw [rR z hR]; exact funext fun k => ec k z ⟨⟨hzr, hzi⟩, hR⟩)
    · have hT : z ∈ hEdge xs ys i (j + 1) := ⟨hzr, ⟨hz'.ge, hz'.le⟩⟩
      refine LabelRel.of_comp hg ?_
      rw [← rT z hT]
      exact funext fun k => ed k z ⟨⟨hzr, hzi⟩, hT⟩

end Pieces

/-! ### The proof of `GridTransitivityStatement` -/

section Final

variable {xs ys : ℕ → ℝ} {n : ℕ} {marked : ℕ → ℕ → Prop}

/-- A point of a piece of the cell `(i, j)` on the boundary of the cell lies on an edge, and the
labelling of the piece is related to the reference labels of that edge. -/
theorem exists_onEdge_of_sideRel {f₀ : Fin S → ℂ} {i j : ℕ} (hi : i < n) (hj : j < n) {z : ℂ}
    (hz : z ∈ gridCell xs ys i j) {F : Fin S → ℂ} (hF : SideRel Z xs ys marked f₀ i j z F)
    (hnot : ¬ (z.re ∈ Ioo (xs i) (xs (i + 1)) ∧ z.im ∈ Ioo (ys j) (ys (j + 1)))) :
    ∃ p q, OnEdge xs ys n p q z ∧
      LabelRel (basedLoopGroup Z xs ys marked f₀) (gridRef Z xs ys f₀ p q z) F := by
  obtain ⟨hzr, hzi⟩ := hz
  have hcase : z.im = ys j ∨ z.re = xs i ∨ z.re = xs (i + 1) ∨ z.im = ys (j + 1) := by
    by_contra h
    push Not at h
    exact hnot ⟨⟨lt_of_le_of_ne hzr.1 (Ne.symm h.2.1), lt_of_le_of_ne hzr.2 h.2.2.1⟩,
      ⟨lt_of_le_of_ne hzi.1 (Ne.symm h.1), lt_of_le_of_ne hzi.2 h.2.2.2⟩⟩
  rcases hcase with h | h | h | h
  · exact ⟨i, j, Or.inl ⟨hi, hj.le, hzr, ⟨h.ge, h.le⟩⟩, hF.1 h⟩
  · exact ⟨i, j, Or.inr ⟨hi.le, hj, ⟨h.ge, h.le⟩, hzi⟩, hF.2.1 h⟩
  · exact ⟨i + 1, j, Or.inr ⟨hi, hj, ⟨h.ge, h.le⟩, hzi⟩, hF.2.2.1 h⟩
  · exact ⟨i, j + 1, Or.inl ⟨hi, hj, hzr, ⟨h.ge, h.le⟩⟩, hF.2.2.2 h⟩

/-- **Transitivity from connectedness.** -/
theorem gridTransitivityStatement : GridTransitivityStatement := by
  intro S Z U xs ys n marked center baseLabel hZ G hc hinj hrange hconn x y
  classical
  have hf₀ : IsFibreLabel Z (gridPoint xs ys 0 0) baseLabel := ⟨hinj, hrange⟩
  set Γ := basedLoopGroup Z xs ys marked baseLabel with hΓ
  -- The pieces of all cells.
  have hP := fun ij : Fin n × Fin n => exists_cell_pieces hZ G hc hf₀ ij.1.2 ij.2.2
  choose Qs Λ hQc hQsub hQcov hΛ hside hint using hP
  set ι := (Fin n × Fin n) × (Bool × Bool)
  set punct : ι → Set ℂ := fun α => puncture marked center α.1.1 α.1.2
  -- Any two pieces at a common point.
  have hagree : ∀ α β : ι, ∀ z, z ∈ Qs α.1 α.2 \ punct α → z ∈ Qs β.1 β.2 \ punct β →
      LabelRel Γ (fun k => Λ α.1 α.2 k z) fun k => Λ β.1 β.2 k z := by
    rintro ⟨⟨i, j⟩, q⟩ ⟨⟨i', j'⟩, q'⟩ z hzα hzβ
    by_cases hij : (i, j) = (i', j')
    · simp only [Prod.mk.injEq] at hij
      obtain ⟨rfl, rfl⟩ := hij
      exact hint (i, j) q q' z ⟨hzα, hzβ⟩
    · have hzc := hQsub (i, j) q hzα.1
      have hzc' := hQsub (i', j') q' hzβ.1
      have hnot : ∀ {a b a' b' : Fin n}, (a, b) ≠ (a', b') →
          z ∈ gridCell xs ys a b → z ∈ gridCell xs ys a' b' →
          ¬ (z.re ∈ Ioo (xs a) (xs (a + 1)) ∧ z.im ∈ Ioo (ys b) (ys (b + 1))) := by
        intro a b a' b' hne h1 h2 ⟨hr, him⟩
        apply hne
        have e1 := Ioo_index_unique G.xs_lt a'.2 a.2 h2.1 hr
        have e2 := Ioo_index_unique G.ys_lt b'.2 b.2 h2.2 him
        rw [Fin.ext e1, Fin.ext e2]
      obtain ⟨p, r, hpr, hrel⟩ := exists_onEdge_of_sideRel i.2 j.2 hzc (hside (i, j) q z hzα)
        (hnot hij hzc hzc')
      obtain ⟨p', r', hpr', hrel'⟩ := exists_onEdge_of_sideRel i'.2 j'.2 hzc'
        (hside (i', j') q' z hzβ) (hnot (Ne.symm hij) hzc' hzc)
      exact (hrel.symm.trans (labelRel_gridRef hZ G hf₀ hpr hpr')).trans hrel'
  -- The total space as a preconnected space.
  set E := {q : ℂ × ℂ | (q.1.re ∈ Icc (xs 0) (xs n) ∧ q.1.im ∈ Icc (ys 0) (ys n)) ∧
      (∀ a < n, ∀ b < n, marked a b → q.1 ≠ center a b) ∧ q.2 ∈ Z q.1} with hE
  have hXc : PreconnectedSpace E := isPreconnected_iff_preconnectedSpace.mp hconn
  have hEp : ∀ e : E, ∀ α : ι, e.1.1 ∉ punct α := fun e α h => e.2.2.1 _ α.1.1.2 _ α.1.2.2 h.1 h.2
  -- The orbit of `x`.
  set O : Set (Fin S) := {k | ∃ τ ∈ Γ, τ x = k} with hO
  have hOmem : ∀ ρ ∈ Γ, ∀ k ∈ O, ρ k ∈ O := by
    rintro ρ hρ k ⟨τ, hτ, rfl⟩
    exact ⟨ρ * τ, Γ.mul_mem hρ hτ, rfl⟩
  -- The two closed sets.
  set C : ι → Fin S → Set E := fun α k => {e | e.1.1 ∈ Qs α.1 α.2 ∧ Λ α.1 α.2 k e.1.1 = e.1.2}
  have hCc : ∀ α k, IsClosed (C α k) := by
    intro α k
    have hs : IsClosed {e : E | e.1.1 ∈ Qs α.1 α.2} :=
      (hQc α.1 α.2).preimage (continuous_fst.comp continuous_subtype_val)
    have hcont : ContinuousOn (fun e : E => (Λ α.1 α.2 k e.1.1, e.1.2))
        {e : E | e.1.1 ∈ Qs α.1 α.2} := by
      refine ContinuousOn.prodMk ?_ (continuous_snd.comp continuous_subtype_val).continuousOn
      exact ((hΛ α.1 α.2).continuousOn k).comp
        (continuous_fst.comp continuous_subtype_val).continuousOn fun e he => ⟨he, hEp e α⟩
    have := hcont.preimage_isClosed_of_isClosed hs isClosed_diagonal
    have heq : C α k = {e : E | e.1.1 ∈ Qs α.1 α.2} ∩
        (fun e : E => (Λ α.1 α.2 k e.1.1, e.1.2)) ⁻¹' diagonal ℂ := by
      ext e
      simp [C, Set.mem_diagonal_iff]
    rw [heq]
    exact this
  set A : Set E := ⋃ α, ⋃ k : {k // k ∈ O}, C α k
  set B : Set E := ⋃ α, ⋃ k : {k // k ∉ O}, C α k
  have hAc : IsClosed A := isClosed_iUnion_of_finite fun α => isClosed_iUnion_of_finite fun k =>
    hCc α k
  have hBc : IsClosed B := isClosed_iUnion_of_finite fun α => isClosed_iUnion_of_finite fun k =>
    hCc α k
  -- Every point of the total space lies in a piece.
  have hcover : ∀ e : E, ∃ α : ι, e.1.1 ∈ Qs α.1 α.2 := by
    intro e
    obtain ⟨⟨hre, him⟩, -, -⟩ := e.2
    obtain ⟨i, hi, hir⟩ := exists_Icc_index G.pos hre
    obtain ⟨j, hj, hji⟩ := exists_Icc_index G.pos him
    obtain ⟨q, hq⟩ := hQcov (⟨i, hi⟩, ⟨j, hj⟩) e.1.1 ⟨hir, hji⟩ (hEp e ((⟨i, hi⟩, ⟨j, hj⟩), (false,
      false)))
    exact ⟨((⟨i, hi⟩, ⟨j, hj⟩), q), hq⟩
  have hlabel : ∀ (e : E) (α : ι), e.1.1 ∈ Qs α.1 α.2 → ∃ k, Λ α.1 α.2 k e.1.1 = e.1.2 := by
    intro e α hα
    have := (hΛ α.1 α.2).range_eq e.1.1 ⟨hα, hEp e α⟩
    change _ = Z e.1.1 at this
    have h2 : e.1.2 ∈ Z e.1.1 := e.2.2.2
    rw [← this] at h2
    exact h2
  have hunion : A ∪ B = univ := by
    refine eq_univ_of_forall fun e => ?_
    obtain ⟨α, hα⟩ := hcover e
    obtain ⟨k, hk⟩ := hlabel e α hα
    by_cases hkO : k ∈ O
    · exact Or.inl (mem_iUnion.mpr ⟨α, mem_iUnion.mpr ⟨⟨k, hkO⟩, hα, hk⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨α, mem_iUnion.mpr ⟨⟨k, hkO⟩, hα, hk⟩⟩)
  have hdisj : ∀ e, e ∈ A → e ∈ B → False := by
    intro e hA hB
    obtain ⟨α, hα⟩ := mem_iUnion.mp hA
    obtain ⟨⟨k₁, hk₁⟩, hα1, hk₁e⟩ := mem_iUnion.mp hα
    obtain ⟨β, hβ⟩ := mem_iUnion.mp hB
    obtain ⟨⟨k₂, hk₂⟩, hβ1, hk₂e⟩ := mem_iUnion.mp hβ
    obtain ⟨ρ, hρ, hρeq⟩ := hagree α β e.1.1 ⟨hα1, hEp e α⟩ ⟨hβ1, hEp e β⟩
    have h1 : Λ α.1 α.2 (ρ k₂) e.1.1 = Λ α.1 α.2 k₁ e.1.1 := by
      have := congrFun hρeq k₂
      simp only [Function.comp_apply] at this
      rw [← this, hk₂e, hk₁e]
    have h2 : ρ k₂ = k₁ := (hΛ α.1 α.2).injective e.1.1 ⟨hα1, hEp e α⟩ h1
    apply hk₂
    have := hOmem ρ⁻¹ (Γ.inv_mem hρ) k₁ hk₁
    rw [← h2] at this
    simpa using this
  have hAo : IsOpen A := by
    have : Aᶜ = B := by
      ext e
      constructor
      · intro h
        rcases (show e ∈ A ∪ B by rw [hunion]; trivial) with h' | h'
        · exact absurd h' h
        · exact h'
      · exact fun h h' => hdisj e h' h
    rw [← isClosed_compl_iff, this]
    exact hBc
  -- The base points.
  set c₀ := gridPoint xs ys 0 0
  have hc₀E : ∀ k, (c₀, baseLabel k) ∈ E := by
    intro k
    refine ⟨⟨⟨le_rfl, le_of_lt_succ_of_le G.xs_lt (Nat.zero_le n) le_rfl⟩,
      ⟨le_rfl, le_of_lt_succ_of_le G.ys_lt (Nat.zero_le n) le_rfl⟩⟩, fun a ha b hb hm h => ?_,
      ?_⟩
    · have := (hc a ha b hb hm).1.1.1
      rw [← h] at this
      have h0 : xs 0 ≤ xs a := le_of_lt_succ_of_le G.xs_lt (Nat.zero_le a) ha.le
      exact absurd this (not_lt.mpr h0)
    · rw [← hrange]; exact ⟨k, rfl⟩
  set e : Fin S → E := fun k => ⟨(c₀, baseLabel k), hc₀E k⟩
  obtain ⟨α₀, hα₀⟩ := hcover (e x)
  -- The labels of the piece at the base vertex.
  have hbase : ∃ ρ ∈ Γ, (fun k => Λ α₀.1 α₀.2 k c₀) = baseLabel ∘ ρ := by
    -- The base vertex lies on the boundary of every cell containing it.
    have hcell := hQsub α₀.1 α₀.2 hα₀
    have hi0 : (α₀.1.1 : ℕ) = 0 := by
      by_contra h0
      have : xs α₀.1.1 ≤ xs 0 := hcell.1.1
      have h1 : xs 0 < xs α₀.1.1 := lt_of_lt_succ_of_lt G.xs_lt (Nat.pos_of_ne_zero h0)
        α₀.1.1.2.le
      linarith
    have hj0 : (α₀.1.2 : ℕ) = 0 := by
      by_contra h0
      have : ys α₀.1.2 ≤ ys 0 := hcell.2.1
      have h1 : ys 0 < ys α₀.1.2 := lt_of_lt_succ_of_lt G.ys_lt (Nat.pos_of_ne_zero h0)
        α₀.1.2.2.le
      linarith
    have hrel := (hside α₀.1 α₀.2 c₀ ⟨hα₀, hEp (e x) α₀⟩).1 (by
      change ys 0 = ys α₀.1.2
      rw [hj0])
    obtain ⟨ρ, hρ, hρeq⟩ := hrel
    refine ⟨ρ, hρ, ?_⟩
    rw [hρeq]
    have hgr : gridRef Z xs ys baseLabel α₀.1.1 α₀.1.2 c₀ = baseLabel := by
      unfold gridRef
      rw [hi0, hj0]
      exact segT_self hf₀
    rw [hgr]
  obtain ⟨ρ, hρ, hρeq⟩ := hbase
  have hlab : ∀ k, Λ α₀.1 α₀.2 (ρ⁻¹ k) c₀ = baseLabel k := by
    intro k
    have := congrFun hρeq (ρ⁻¹ k)
    simpa using this
  have hxA : e x ∈ A := mem_iUnion.mpr ⟨α₀, mem_iUnion.mpr
    ⟨⟨ρ⁻¹ x, hOmem ρ⁻¹ (Γ.inv_mem hρ) x ⟨1, Γ.one_mem, rfl⟩⟩, hα₀, hlab x⟩⟩
  -- Conclusion.
  by_contra hy
  have hyO : y ∉ O := fun h => hy h
  have hyB : e y ∈ B := by
    refine mem_iUnion.mpr ⟨α₀, mem_iUnion.mpr ⟨⟨ρ⁻¹ y, fun h => hyO ?_⟩, hα₀, hlab y⟩⟩
    have := hOmem ρ hρ _ h
    simpa using this
  rcases isClopen_iff.mp ⟨hAc, hAo⟩ with hA0 | hA1
  · rw [hA0] at hxA; exact hxA
  · exact hdisj (e y) (by rw [hA1]; trivial) hyB

end Final

/-- **`LevelRootFamilyStatement` from the projection data of the levels.** -/
theorem levelRootFamilyStatement_of_projectionInput (h : LevelProjectionStatement) :
    LevelRootFamilyStatement :=
  levelRootFamilyStatement_of_levelProjection gridTransitivityStatement h

/-- **`LevelRootFamilyStatement` from the four propositions of a setup.** -/
theorem levelRootFamilyStatement_of_setup (h : LevelProjectionSetupStatement) :
    LevelRootFamilyStatement :=
  levelRootFamilyStatement_of_projectionInput (levelProjectionStatement_of_setup h)

end OnLeConjecture.Analytic
