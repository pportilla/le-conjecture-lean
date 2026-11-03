/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridVertexNeighborhoods

/-! # Exhaustive native edge and corner coverage of the retained rounded word

Every parameter of the same rounded word lies on a native horizontal arc, on a
native vertical segment at its prescribed depth, or inside a neighborhood of one
of that strand's own marked corners. The assertions below describe literal
coordinates. They do not identify a general grid knot or a Floer invariant.
-/

@[expose] public noncomputable section
open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- The cylinder points above an actual horizontal arc, on its native `O` row.
The imaginary coordinate is unrestricted because connector depths vary. -/
def PositiveWordNativeHorizontalPoint {m : ℕ} (w : PositiveAdjacentWord m)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (p : Circle × ℂ) : Prop :=
  ∃ a : PositiveRectilinearHorizontalArc w,
    ((p.1 : ℂ), positiveRectilinearHorizontalArcRow w a) ∈
      positiveRectilinearHorizontalArcSet w a ∧
    p.2.re = row (G.O (finProdFinEquiv ((positiveRectilinearOutgoingArc w).symm a)))

/-- The cylinder points on a literal native vertical segment, with the upper
strand at depth `1` and the lower strand at depth `-1`. -/
def PositiveWordNativeVerticalPoint {m : ℕ} (w : PositiveAdjacentWord m)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (p : Circle × ℂ) : Prop :=
  ∃ j : Fin w.length, ∃ c : Fin 3,
    p.1 = Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
      (2 * (w.length : ℝ) + 1)) ∧
    p.2.re ∈ uIcc (row (G.X (finProdFinEquiv (j, c))))
      (row (G.O (finProdFinEquiv (j, c)))) ∧
    p.2.im = if c = 1 then 1 else -1

/-- Literal native straight-edge membership or membership in one prescribed
marking neighborhood. This pointwise property includes all source parameters. -/
def PositiveWordNativeEdgeOrCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ)) (p : Circle × ℂ) : Prop :=
  PositiveWordNativeHorizontalPoint w G row p ∨
    PositiveWordNativeVerticalPoint w G row p ∨ ∃ j c o, p ∈ V j c o

/-- The original source label and progress parameter lie in the support of a
specified corner of that same moving strand. -/
def PositiveRoundedWordOwnCornerParameter {m : ℕ} (w : PositiveAdjacentWord m)
    (δ : ℝ) (k : Fin m) (t : ℝ) (j : Fin w.length) (c : Fin 3) (o : Bool) : Prop :=
  t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) ∧
    (positiveWordPrefix w j.val).symm k = positiveGridMarkingStrand w[j.val] c ∧
    |positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 -
      positiveGridMarkingTime c o| < δ

/-- Straight-edge membership or a neighborhood of a corner of the same strand,
with its original label, letter interval, and corner support retained. -/
def PositiveRoundedWordNativeEdgeOrOwnCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (δ : ℝ) (k : Fin m) (t : ℝ) (p : Circle × ℂ) : Prop :=
  PositiveWordNativeHorizontalPoint w G row p ∨
    PositiveWordNativeVerticalPoint w G row p ∨ ∃ j c o,
      PositiveRoundedWordOwnCornerParameter w δ k t j c o ∧ p ∈ V j c o

/-- Forgetting source metadata leaves the literal geometric edge-or-corner assertion. -/
theorem PositiveRoundedWordNativeEdgeOrOwnCorner.edgeOrCorner {m : ℕ}
    {w : PositiveAdjacentWord m} {G : TauCeti.GridDiagram (w.length * 3)}
    {row : Fin (w.length * 3) → ℝ}
    {V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ)} {δ : ℝ} {k : Fin m}
    {t : ℝ} {p : Circle × ℂ} (h : PositiveRoundedWordNativeEdgeOrOwnCorner w G row V δ k t p) :
    PositiveWordNativeEdgeOrCorner w G row V p := by
  rcases h with hh | hv | ⟨j, c, o, _, hV⟩
  · exact Or.inl hh
  · exact Or.inr (Or.inl hv)
  · exact Or.inr (Or.inr ⟨j, c, o, hV⟩)

/-- Every time in the word's closed period is in a connector or a letter. -/
theorem positiveWordPeriodTime_gap_or_letter (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * (n : ℝ) + 1)) :
    (∃ j : Fin (n + 1), t ∈ Icc (2 * (j.val : ℝ)) (2 * (j.val : ℝ) + 1)) ∨
      ∃ j : Fin n, t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2) := by
  induction n with
  | zero => exact Or.inl ⟨0, by simpa using ht⟩
  | succ n ih =>
    by_cases hn : t ≤ 2 * (n : ℝ) + 1
    · rcases ih ⟨ht.1, hn⟩ with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨j.castSucc, hj⟩
      · exact Or.inr ⟨j.castSucc, hj⟩
    · by_cases hl : t ≤ 2 * (n : ℝ) + 2
      · refine Or.inr ⟨Fin.last n, ?_⟩
        simp only [Fin.val_last]
        exact ⟨by linarith, hl⟩
      · refine Or.inl ⟨Fin.last (n + 1), ?_⟩
        simp only [Fin.val_last, Nat.cast_add, Nat.cast_one] at *
        constructor <;> linarith [ht.2]

/-- The moving strand's polygon parameter remains in the original unit interval. -/
theorem positiveGridRoundingProgress_half_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    positiveGridRoundingProgress t / 2 ∈ Icc (0 : ℝ) 1 := by
  unfold positiveGridRoundingProgress
  constructor <;> linarith [Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t,
    ht.1, ht.2]

/-- Every parameter of either moving polygonal strand is horizontal or vertical. -/
theorem positiveGrid_moving_horizontal_or_vertical {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (hk : k = adjacentLower i ∨ k = adjacentUpper i) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    PositiveGridMovingHorizontalTime i k t ∨ ∃ c, PositiveGridVerticalTime i k c t := by
  rcases hk with rfl | rfl
  · by_cases h₀ : t ≤ 1 / 6
    · exact Or.inl (Or.inl ⟨rfl, Or.inl ⟨ht.1, h₀⟩⟩)
    · by_cases h₁ : t ≤ 5 / 12
      · exact Or.inr ⟨0, Or.inl ⟨rfl, rfl, by constructor <;> linarith⟩⟩
      · by_cases h₂ : t ≤ 7 / 12
        · exact Or.inl (Or.inl ⟨rfl, Or.inr (Or.inl (by constructor <;> linarith))⟩)
        · by_cases h₃ : t ≤ 5 / 6
          · exact Or.inr ⟨2, Or.inr (Or.inr ⟨rfl, rfl, by constructor <;> linarith⟩)⟩
          · exact Or.inl (Or.inl ⟨rfl, Or.inr (Or.inr (by constructor <;> linarith [ht.2]))⟩)
  · by_cases h₀ : t ≤ 1 / 4
    · exact Or.inl (Or.inr ⟨rfl, Or.inl ⟨ht.1, h₀⟩⟩)
    · by_cases h₁ : t ≤ 3 / 4
      · exact Or.inr ⟨1, Or.inr (Or.inl ⟨rfl, rfl, by constructor <;> linarith⟩)⟩
      · exact Or.inl (Or.inr ⟨rfl, Or.inr (by constructor <;> linarith [ht.2])⟩)

/-- Any actual horizontal-arc point is carried to that arc's exact native row. -/
theorem positiveGridRowShear_nativeHorizontal_of_mem {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (p : Circle × ℂ) (a : PositiveRectilinearHorizontalArc w)
    (ha : ((p.1 : ℂ), p.2.re) ∈ positiveRectilinearHorizontalArcSet w a) :
    PositiveWordNativeHorizontalPoint w G row (positiveGridRowShearCylinder q 1 p) := by
  have hs := positiveRectilinearHorizontalArc_shear_row w g hq a p ha
  have hr : p.2.re = positiveRectilinearHorizontalArcRow w a := by
    obtain ⟨x, hx, he⟩ := ha
    exact (congrArg Prod.snd he).symm
  exact ⟨a, by simpa only [hs.1, ← hr] using ha, (hs.2.1).trans (hO _).symm⟩

/-- The depth of every literal vertical move is prescribed by its column. -/
theorem positiveGridRectilinear_vertical_depth {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (c : Fin 3) {t : ℝ} (ht : PositiveGridVerticalTime i k c t) :
    (positiveGridRectilinear i k t).2.im = if c = 1 then 1 else -1 := by
  rcases ht with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;>
    norm_num [positiveGridRectilinear, positiveGridRectilinearDepth, Fin.reduceEq]
  decide

/-- At an unchanged polygonal letter point the retained shear gives the exact
native vertical segment, including the crossing depth. -/
theorem positiveRoundedWord_nativeVertical_of_polygon {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (k : Fin m) (j : Fin w.length) (c : Fin 3) (t s : ℝ)
    (he : positiveRoundedWord w l u k 1 t =
      let p := positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm k) s
      (2 * (j.val : ℝ) + 1 + p.1, p.2))
    (hv : PositiveGridVerticalTime w[j.val] ((positiveWordPrefix w j.val).symm k) c s) :
    PositiveWordNativeVerticalPoint w G row (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t))) := by
  have hp := positiveGridRectilinear_vertical_segment w[j.val] _ c hv
  have himage := positiveGridShearedRow_image_native_vertical w g hqlip hq G row hO hX (j, c)
  have hp' : (positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm k) s).2.re ∈
      uIcc (positiveRectilinearWordXCorner w j c).2 (positiveRectilinearWordOCorner w j c).2 :=
    hp.2
  have hmem := Set.mem_image_of_mem
    (positiveGridShearedRow q (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
      (2 * (w.length : ℝ) + 1)))) hp' 
  rw [himage] at hmem
  refine ⟨j, c, ?_, ?_, ?_⟩
  · change Circle.exp _ = _
    rw [he]
    congr 1
    dsimp only
    rw [hp.1]
    rfl
  · change (positiveGridRowShear q 1 _).2.re ∈ _
    rw [positiveGridRowShear_re]
    simpa only [he, positiveRectilinearCylinderPoint, hp.1, Real.smoothTransition.one, one_mul,
      positiveRectilinearWordColumn, positiveGridShearedRow] using hmem
  · change (positiveGridRowShear q 1 _).2.im = _
    rw [positiveGridRowShear_im]
    simpa only [he, positiveRectilinearCylinderPoint] using
      positiveGridRectilinear_vertical_depth w[j.val] _ c hv

/-- An unchanged moving letter point lies on one of the native straight edges. -/
theorem positiveRoundedWord_nativeEdge_of_polygon {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (k : Fin m) (j : Fin w.length) (t s : ℝ)
    (he : positiveRoundedWord w l u k 1 t =
      let p := positiveGridRectilinear w[j.val] ((positiveWordPrefix w j.val).symm k) s
      (2 * (j.val : ℝ) + 1 + p.1, p.2))
    (hk : (positiveWordPrefix w j.val).symm k = adjacentLower w[j.val] ∨
      (positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val])
    (hs : s ∈ Icc (0 : ℝ) 1) :
    PositiveWordNativeHorizontalPoint w G row (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t))) ∨
    PositiveWordNativeVerticalPoint w G row (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t))) := by
  rcases positiveGrid_moving_horizontal_or_vertical w[j.val] _ hk hs with hh | ⟨c, hv⟩
  · obtain ⟨a, ha⟩ := positiveRectilinear_letter_horizontal_mem w j _ hh
    apply Or.inl
    apply positiveGridRowShear_nativeHorizontal_of_mem w g hq G row hO _ a
    simpa only [he, positiveRectilinearCylinderPoint] using ha
  · exact Or.inr (positiveRoundedWord_nativeVertical_of_polygon w g hqlip hq G row hO hX
      k j c t s he hv)

/-- Every point of the retained word is on a literal native straight edge or
inside a prescribed neighborhood of one of its own markings. The four lower
and two upper vertex supports are kept separate throughout the proof. -/
theorem positiveRoundedWord_native_edge_or_own_corner {m : ℕ} (w : PositiveAdjacentWord m)
    (hrows : ∀ r : Fin m, Nonempty (PositiveRectilinearRowOccurrences w r))
    {δ : ℝ} (hδ : δ ≤ 1 / 48) {l u : ℝ → ℝ}
    (hl : EqOn l positiveGridRectilinearLowerRise (positiveGridLowerVertexNeighborhood δ)ᶜ)
    (hu : EqOn u positiveGridRectilinearUpperDrop (positiveGridUpperVertexNeighborhood δ)ᶜ)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (V : Fin w.length → Fin 3 → Bool → Set (Circle × ℂ))
    (hnear : PositiveRoundedWordMarkingNeighborhoods w q V δ l u)
    (k : Fin m) {t : ℝ} (ht : t ∈ Icc 0 (2 * (w.length : ℝ) + 1)) :
    PositiveRoundedWordNativeEdgeOrOwnCorner w G row V δ k t (positiveGridRowShearCylinder q 1
      (positiveRectilinearCylinderPoint w
        (positiveRoundedWord w (fun _ => l) (fun _ => u) k 1 t))) := by
  have hlc := hl.mono (compl_subset_compl.mpr (positiveGridLowerVertexNeighborhood_subset δ))
  have huc := hu.mono (compl_subset_compl.mpr (positiveGridUpperVertexNeighborhood_subset δ))
  have hU : positiveGridRoundingCornerNeighborhood δ ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    have hh := positiveGridRoundingCornerNeighborhood_subset hδ hx
    constructor <;> linarith [hh.1, hh.2]
  rcases positiveWordPeriodTime_gap_or_letter w.length ht with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨a, ha⟩ := positiveRoundedWord_gap_mem_horizontalArc w (fun _ => hlc)
      (fun _ => huc) hU hrows k 1 j hj
    exact Or.inl (positiveGridRowShear_nativeHorizontal_of_mem w g hq G row hO _ a ha)
  · let s := positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2
    have hs : s ∈ Icc (0 : ℝ) 1 := positiveGridRoundingProgress_half_mem
      (by constructor <;> linarith [hj.1, hj.2])
    by_cases hk₀ : (positiveWordPrefix w j.val).symm k = adjacentLower w[j.val]
    · by_cases hn : s ∈ positiveGridLowerVertexNeighborhood δ
      · obtain ⟨c, hc, o, hco⟩ := positiveGridLowerVertexNeighborhood_iff_marking.mp hn
        have hk : (positiveWordPrefix w j.val).symm k = positiveGridMarkingStrand w[j.val] c :=
          by simpa [positiveGridMarkingStrand, hc] using hk₀
        exact Or.inr (Or.inr ⟨j, c, o, ⟨hj, hk, hco⟩, hnear k j c o t hj hk hco⟩)
      · have he := positiveRoundedWord_letter_eq_polygon_own_vertices w hδ
          (fun _ => hl) (fun _ => hu) k j hj (Or.inl ⟨hk₀, hn⟩)
        rcases positiveRoundedWord_nativeEdge_of_polygon w g hqlip hq G row hO hX k j t s
          he (Or.inl hk₀) hs with hh | hv
        · exact Or.inl hh
        · exact Or.inr (Or.inl hv)
    · by_cases hk₁ : (positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val]
      · by_cases hn : s ∈ positiveGridUpperVertexNeighborhood δ
        · obtain ⟨o, hco⟩ := positiveGridUpperVertexNeighborhood_iff_marking.mp hn
          have hk : (positiveWordPrefix w j.val).symm k = positiveGridMarkingStrand w[j.val] 1 :=
            by simpa [positiveGridMarkingStrand] using hk₁
          exact Or.inr (Or.inr ⟨j, 1, o, ⟨hj, hk, hco⟩, hnear k j 1 o t hj hk hco⟩)
        · have he := positiveRoundedWord_letter_eq_polygon_own_vertices w hδ
            (fun _ => hl) (fun _ => hu) k j hj (Or.inr ⟨hk₁, hn⟩)
          rcases positiveRoundedWord_nativeEdge_of_polygon w g hqlip hq G row hO hX k j t s
            he (Or.inr hk₁) hs with hh | hv
          · exact Or.inl hh
          · exact Or.inr (Or.inl hv)
      · obtain ⟨a, ha⟩ := positiveRoundedWord_fixed_letter_mem_horizontalArc w
          (fun _ => hlc) (fun _ => huc) hU hrows k 1 j hj hk₀ hk₁
        exact Or.inl (positiveGridRowShear_nativeHorizontal_of_mem w g hq G row hO _ a ha)

end OnLeConjecture.KnotTheory
