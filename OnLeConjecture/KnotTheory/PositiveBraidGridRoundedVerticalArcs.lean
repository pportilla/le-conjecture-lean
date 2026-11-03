/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridRoundedHorizontalArcs
public import Mathlib.Topology.Order.IntermediateValue

/-! # Exact vertical segments under the retained row deformation

At every fixed column the constructed row shear is strictly increasing. Its
endpoint values are the marking rows, so it carries the entire original vertical
segment onto the exact interval between the native grid's two markings.
-/

@[expose] public noncomputable section
open Set
open scoped Topology ContDiff Interval

namespace OnLeConjecture.KnotTheory

/-- The terminal shear on the real height at a fixed base point. -/
def positiveGridShearedRow (q : ℂ × ℝ → ℝ) (c : ℂ) (y : ℝ) : ℝ := y + q (c, y)

/-- The small Lipschitz bound preserves vertical order, including downward moves. -/
theorem positiveGridShearedRow_strictMono {q : ℂ × ℝ → ℝ}
    (hq : LipschitzWith (1 / 2) q) (c : ℂ) : StrictMono (positiveGridShearedRow q c) := by
  intro x y hxy
  have hb := hq.dist_le_mul (c, y) (c, x)
  have hyx : 0 ≤ y - x := sub_nonneg.mpr hxy.le
  have hb' : |q (c, y) - q (c, x)| ≤ (1 / 2 : ℝ) * (y - x) := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hyx, max_eq_right hyx] using hb
  have hlo := (abs_le.mp hb').1
  dsimp [positiveGridShearedRow]
  linarith

theorem positiveGridShearedRow_continuous {q : ℂ × ℝ → ℝ}
    (hq : Continuous q) (c : ℂ) : Continuous (positiveGridShearedRow q c) :=
  continuous_id.add (hq.comp (continuous_const.prodMk continuous_id))

/-- Both endpoints of every closed horizontal arc belong to the actual compact arc set. -/
theorem positiveRectilinearHorizontalArc_endpoints_mem {m : ℕ}
    (w : PositiveAdjacentWord m) (a : PositiveRectilinearHorizontalArc w) :
    ((Circle.exp (2 * Real.pi * positiveRectilinearHorizontalArcStart w a /
      (2 * (w.length : ℝ) + 1)) : ℂ), positiveRectilinearHorizontalArcRow w a) ∈
        positiveRectilinearHorizontalArcSet w a ∧
    ((Circle.exp (2 * Real.pi * positiveRectilinearHorizontalArcEnd w a /
      (2 * (w.length : ℝ) + 1)) : ℂ), positiveRectilinearHorizontalArcRow w a) ∈
        positiveRectilinearHorizontalArcSet w a := by
  have hs := positiveRectilinearHorizontalArc_endpoints_mem_period w a
  constructor
  · refine ⟨_, ⟨⟨hs.1.1.le, hs.1.2.le⟩, ?_⟩, rfl⟩
    change PositiveRectilinearClosedCyclicBetween _ _ _
    unfold PositiveRectilinearClosedCyclicBetween
    split_ifs with h
    · exact ⟨le_rfl, h.le⟩
    · exact Or.inl le_rfl
  · refine ⟨_, ⟨⟨hs.2.1.le, hs.2.2.le⟩, ?_⟩, rfl⟩
    change PositiveRectilinearClosedCyclicBetween _ _ _
    unfold PositiveRectilinearClosedCyclicBetween
    split_ifs with h
    · exact ⟨h.le, le_rfl⟩
    · exact Or.inr le_rfl

/-- The outgoing end of a vertical move is carried to its exact assigned `O` row. -/
theorem positiveGridShearedRow_OCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (p : Fin w.length × Fin 3) :
    positiveGridShearedRow q
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w p.1 p.2 /
        (2 * (w.length : ℝ) + 1))) (positiveRectilinearWordOCorner w p.1 p.2).2 = g p := by
  have hh := hq (positiveRectilinearOutgoingArc w p) _
    (positiveRectilinearHorizontalArc_endpoints_mem w (positiveRectilinearOutgoingArc w p)).1
  have hs : positiveRectilinearHorizontalArcStart w (positiveRectilinearOutgoingArc w p) =
      positiveRectilinearWordColumn w p.1 p.2 := by
    simp [positiveRectilinearHorizontalArcStart]
  rw [hs, Equiv.symm_apply_apply, positiveRectilinearOutgoingArc_row] at hh
  simp only [positiveGridShearedRow]
  rw [hh]
  ring

/-- The incoming end is carried to the row of its unique preceding horizontal arc. -/
theorem positiveGridShearedRow_XCorner {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (p : Fin w.length × Fin 3) :
    positiveGridShearedRow q
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w p.1 p.2 /
        (2 * (w.length : ℝ) + 1))) (positiveRectilinearWordXCorner w p.1 p.2).2 =
      g ((positiveRectilinearWordMatching w).symm p) := by
  let a := positiveRectilinearOutgoingArc w ((positiveRectilinearWordMatching w).symm p)
  have hh := hq a _ (positiveRectilinearHorizontalArc_endpoints_mem w a).2
  have hs : positiveRectilinearHorizontalArcEnd w a =
      positiveRectilinearWordColumn w p.1 p.2 := by
    change positiveRectilinearWordColumn w
      (positiveRectilinearWordMatching w ((positiveRectilinearWordMatching w).symm p)).1
      (positiveRectilinearWordMatching w ((positiveRectilinearWordMatching w).symm p)).2 = _
    rw [Equiv.apply_symm_apply]
  have hr : positiveRectilinearHorizontalArcRow w a =
      (positiveRectilinearWordXCorner w p.1 p.2).2 := by
    rw [positiveRectilinearOutgoingArc_row]
    exact positiveRectilinearWordArcRow_incoming w p
  rw [hs, hr] at hh
  have he : (positiveRectilinearOutgoingArc w).symm a =
      (positiveRectilinearWordMatching w).symm p := Equiv.symm_apply_apply _ _
  rw [he] at hh
  simp only [positiveGridShearedRow]
  rw [hh]
  ring

/-- The entire old vertical segment maps onto the exact new interval, rather
than merely having the expected endpoint permutation. -/
theorem positiveGridShearedRow_image_vertical {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (p : Fin w.length × Fin 3) :
    positiveGridShearedRow q
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w p.1 p.2 /
        (2 * (w.length : ℝ) + 1))) ''
      uIcc (positiveRectilinearWordXCorner w p.1 p.2).2
        (positiveRectilinearWordOCorner w p.1 p.2).2 =
      uIcc (g ((positiveRectilinearWordMatching w).symm p)) (g p) := by
  rw [(positiveGridShearedRow_continuous hqlip.continuous _).continuousOn.image_uIcc_of_monotoneOn
    ((positiveGridShearedRow_strictMono hqlip _).monotone.monotoneOn _),
    positiveGridShearedRow_XCorner w g hq, positiveGridShearedRow_OCorner w g hq]

/-- The new vertical interval is exactly between the two native grid markings. -/
theorem positiveGridShearedRow_image_native_vertical {m : ℕ} (w : PositiveAdjacentWord m)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p)) (p : Fin w.length × Fin 3) :
    positiveGridShearedRow q
      (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w p.1 p.2 /
        (2 * (w.length : ℝ) + 1))) ''
      uIcc (positiveRectilinearWordXCorner w p.1 p.2).2
        (positiveRectilinearWordOCorner w p.1 p.2).2 =
      uIcc (row (G.X (finProdFinEquiv p))) (row (G.O (finProdFinEquiv p))) := by
  rw [hO, hX]
  exact positiveGridShearedRow_image_vertical w g hqlip hq p

/-- The three vertical moves, with their original polygon parameters and columns. -/
def PositiveGridVerticalTime {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (c : Fin 3)
    (t : ℝ) : Prop :=
  (c = 0 ∧ k = adjacentLower i ∧ t ∈ Icc (1 / 6) (5 / 12)) ∨
  (c = 1 ∧ k = adjacentUpper i ∧ t ∈ Icc (1 / 4) (3 / 4)) ∨
  (c = 2 ∧ k = adjacentLower i ∧ t ∈ Icc (7 / 12) (5 / 6))

/-- Each literal polygonal vertical move has the exact marked column and endpoint interval. -/
theorem positiveGridRectilinear_vertical_segment {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (c : Fin 3) {t : ℝ} (ht : PositiveGridVerticalTime i k c t) :
    (positiveGridRectilinear i k t).1 = positiveGridRectilinearColumns c ∧
      (positiveGridRectilinear i k t).2.re ∈
        uIcc (positiveGridRectilinearRows i (positiveGridRectilinearDiagram.X c))
          (positiveGridRectilinearRows i (positiveGridRectilinearDiagram.O c)) := by
  rcases ht with ⟨rfl, rfl, ht⟩ | ⟨rfl, rfl, ht⟩ | ⟨rfl, rfl, ht⟩
  · have hp := (positiveGridRectilinear_lower_segments i).2.1 t ht
    refine ⟨congrArg Prod.fst hp, ?_⟩
    rw [show (positiveGridRectilinear i (adjacentLower i) t).2.re =
      (i.val : ℝ) + 2 * t - 1 / 3 from congrArg Prod.snd hp]
    norm_num [positiveGridRectilinearRows, positiveGridRectilinearDiagram,
      Equiv.swap_apply_def, uIcc, min_def, max_def, Fin.ext_iff, Matrix.cons_val_two]
    constructor <;> linarith [ht.1, ht.2]
  · have hp := (positiveGridRectilinear_upper_segments i).2.1 t ht
    refine ⟨congrArg Prod.fst hp, ?_⟩
    rw [show (positiveGridRectilinear i (adjacentUpper i) t).2.re =
      (i.val : ℝ) + 3 / 2 - 2 * t from congrArg Prod.snd hp]
    norm_num [positiveGridRectilinearRows, positiveGridRectilinearDiagram,
      Equiv.swap_apply_def, uIcc, min_def, max_def, Fin.ext_iff, Matrix.cons_val_two]
    constructor <;> linarith [ht.1, ht.2]
  · have hp := (positiveGridRectilinear_lower_segments i).2.2.2.1 t ht
    refine ⟨congrArg Prod.fst hp, ?_⟩
    rw [show (positiveGridRectilinear i (adjacentLower i) t).2.re =
      (i.val : ℝ) + 2 * t - 2 / 3 from congrArg Prod.snd hp]
    norm_num [positiveGridRectilinearRows, positiveGridRectilinearDiagram,
      Equiv.swap_apply_def, uIcc, min_def, max_def, Fin.ext_iff, Matrix.cons_val_two]
    constructor <;> linarith [ht.1, ht.2]

/-- The SAME rounded-word point lies on the designated original vertical segment
whenever its explicit polygon parameter is outside the retained rounding neighborhood. -/
theorem positiveRoundedWord_vertical_segment {m : ℕ} (w : PositiveAdjacentWord m)
    {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (k : Fin m) (j : Fin w.length) (c : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hout : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉ U)
    (hv : PositiveGridVerticalTime w[j.val] ((positiveWordPrefix w j.val).symm k) c
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)) :
    (positiveRoundedWord w l u k 1 t).1 = positiveRectilinearWordColumn w j c ∧
      (positiveRoundedWord w l u k 1 t).2.re ∈
        uIcc (positiveRectilinearWordXCorner w j c).2 (positiveRectilinearWordOCorner w j c).2 := by
  have hk : (positiveWordPrefix w j.val).symm k = adjacentLower w[j.val] ∨
      (positiveWordPrefix w j.val).symm k = adjacentUpper w[j.val] := by
    rcases hv with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
    exacts [Or.inl h, Or.inr h, Or.inl h]
  have hp := positiveGridRectilinear_vertical_segment w[j.val] _ c hv
  rw [positiveRoundedWord_letter w hl hu hU k 1 j ht,
    positiveGridRoundedDeformation_one_eq_polygon w[j.val] (hl j) (hu j) _ hout hk]
  exact ⟨congrArg (fun x => 2 * (j.val : ℝ) + 1 + x) hp.1, hp.2⟩

/-- Every retained rounded vertical portion is carried to the literal column and
row interval of the SAME native marking diagram, with imaginary depth unchanged. -/
theorem positiveRoundedWord_shear_native_vertical_segment {m : ℕ}
    (w : PositiveAdjacentWord m) {l u : Fin w.length → ℝ → ℝ} {U : Set ℝ}
    (hl : ∀ j, EqOn (l j) positiveGridRectilinearLowerRise Uᶜ)
    (hu : ∀ j, EqOn (u j) positiveGridRectilinearUpperDrop Uᶜ) (hU : U ⊆ Ioo (0 : ℝ) 1)
    (g : Fin w.length × Fin 3 → ℝ) {q : ℂ × ℝ → ℝ}
    (hqlip : LipschitzWith (1 / 2) q)
    (hq : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p))
    (k : Fin m) (j : Fin w.length) (c : Fin 3) {t : ℝ}
    (ht : t ∈ Icc (2 * (j.val : ℝ) + 1) (2 * (j.val : ℝ) + 2))
    (hout : positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2 ∉ U)
    (hv : PositiveGridVerticalTime w[j.val] ((positiveWordPrefix w j.val).symm k) c
      (positiveGridRoundingProgress (t - (2 * j.val + 1)) / 2)) :
    let p := positiveRectilinearCylinderPoint w (positiveRoundedWord w l u k 1 t)
    (positiveGridRowShearCylinder q 1 p).1 =
        Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
          (2 * (w.length : ℝ) + 1)) ∧
      (positiveGridRowShearCylinder q 1 p).2.re ∈
        uIcc (row (G.X (finProdFinEquiv (j, c)))) (row (G.O (finProdFinEquiv (j, c)))) ∧
      (positiveGridRowShearCylinder q 1 p).2.im = p.2.im := by
  have hp := positiveRoundedWord_vertical_segment w hl hu hU k j c ht hout hv
  have himage := positiveGridShearedRow_image_native_vertical w g hqlip hq G row hO hX (j, c)
  have hmem := Set.mem_image_of_mem
    (positiveGridShearedRow q (Circle.exp (2 * Real.pi * positiveRectilinearWordColumn w j c /
      (2 * (w.length : ℝ) + 1)))) hp.2
  rw [himage] at hmem
  constructor
  · change Circle.exp _ = _
    rw [hp.1]
  constructor
  · change (positiveGridRowShear q 1 _).2.re ∈ _
    rw [positiveGridRowShear_re]
    simpa only [Real.smoothTransition.one, one_mul, positiveRectilinearCylinderPoint,
      hp.1, positiveGridShearedRow] using hmem
  · exact positiveGridRowShear_im q 1 _

end OnLeConjecture.KnotTheory
