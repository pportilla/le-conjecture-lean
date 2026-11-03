/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridProfileAmbientIsotopy

/-! # Interpolation of two native row offsets

Convex interpolation preserves the half-Lipschitz bound and every common value
on an original horizontal arc. Consequently the same native marking rows are
retained throughout the interpolation.
-/

@[expose] public noncomputable section
open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- A stationary convex interpolation between two row-offset functions. -/
def positiveGridRowOffsetInterpolation (q₀ q₁ : ℂ × ℝ → ℝ) (s : ℝ) (p : ℂ × ℝ) : ℝ :=
  (1 - Real.smoothTransition s) * q₀ p + Real.smoothTransition s * q₁ p

@[simp] theorem positiveGridRowOffsetInterpolation_zero (q₀ q₁ : ℂ × ℝ → ℝ) :
    positiveGridRowOffsetInterpolation q₀ q₁ 0 = q₀ := by
  funext p
  simp [positiveGridRowOffsetInterpolation]

@[simp] theorem positiveGridRowOffsetInterpolation_one (q₀ q₁ : ℂ × ℝ → ℝ) :
    positiveGridRowOffsetInterpolation q₀ q₁ 1 = q₁ := by
  funext p
  simp [positiveGridRowOffsetInterpolation]

theorem positiveGridRowOffsetInterpolation_of_nonpos (q₀ q₁ : ℂ × ℝ → ℝ)
    {s : ℝ} (hs : s ≤ 0) : positiveGridRowOffsetInterpolation q₀ q₁ s = q₀ := by
  funext p
  simp [positiveGridRowOffsetInterpolation, Real.smoothTransition.zero_of_nonpos hs]

theorem positiveGridRowOffsetInterpolation_of_one_le (q₀ q₁ : ℂ × ℝ → ℝ)
    {s : ℝ} (hs : 1 ≤ s) : positiveGridRowOffsetInterpolation q₀ q₁ s = q₁ := by
  funext p
  simp [positiveGridRowOffsetInterpolation, Real.smoothTransition.one_of_one_le hs]

theorem positiveGridRowOffsetInterpolation_contDiff {q₀ q₁ : ℂ × ℝ → ℝ}
    (h₀ : ContDiff ℝ ∞ q₀) (h₁ : ContDiff ℝ ∞ q₁) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℝ) => positiveGridRowOffsetInterpolation q₀ q₁ p.1 p.2) :=
  ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).mul
    (h₀.comp contDiff_snd)).add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (h₁.comp contDiff_snd))

/-- The same half-Lipschitz bound holds at every interpolation time. -/
theorem positiveGridRowOffsetInterpolation_lipschitz {q₀ q₁ : ℂ × ℝ → ℝ}
    (h₀ : LipschitzWith (1 / 2) q₀) (h₁ : LipschitzWith (1 / 2) q₁) (s : ℝ) :
    LipschitzWith (1 / 2) (positiveGridRowOffsetInterpolation q₀ q₁ s) := by
  apply LipschitzWith.of_dist_le_mul
  intro p r
  have ha : 0 ≤ 1 - Real.smoothTransition s := sub_nonneg.mpr (Real.smoothTransition.le_one s)
  have hb : 0 ≤ Real.smoothTransition s := Real.smoothTransition.nonneg s
  calc
    dist (positiveGridRowOffsetInterpolation q₀ q₁ s p)
        (positiveGridRowOffsetInterpolation q₀ q₁ s r) =
      |(1 - Real.smoothTransition s) * (q₀ p - q₀ r) +
        Real.smoothTransition s * (q₁ p - q₁ r)| := by
          rw [Real.dist_eq, positiveGridRowOffsetInterpolation, positiveGridRowOffsetInterpolation]
          congr 1
          ring
    _ ≤ |(1 - Real.smoothTransition s) * (q₀ p - q₀ r)| +
        |Real.smoothTransition s * (q₁ p - q₁ r)| := abs_add_le _ _
    _ = (1 - Real.smoothTransition s) * dist (q₀ p) (q₀ r) +
        Real.smoothTransition s * dist (q₁ p) (q₁ r) := by
          simp only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb, Real.dist_eq]
    _ ≤ (1 - Real.smoothTransition s) * ((1 / 2 : ℝ) * dist p r) +
        Real.smoothTransition s * ((1 / 2 : ℝ) * dist p r) :=
      add_le_add (mul_le_mul_of_nonneg_left (h₀.dist_le_mul p r) ha)
        (mul_le_mul_of_nonneg_left (h₁.dist_le_mul p r) hb)
    _ = (1 / 2 : ℝ) * dist p r := by ring

/-- A common offset value is preserved at every interpolation time. -/
theorem positiveGridRowOffsetInterpolation_eq_of_eq {q₀ q₁ : ℂ × ℝ → ℝ} {p : ℂ × ℝ}
    (h : q₀ p = q₁ p) (s : ℝ) : positiveGridRowOffsetInterpolation q₀ q₁ s p = q₀ p := by
  rw [positiveGridRowOffsetInterpolation, ← h]
  ring

/-- The actual cylinder shear point is fixed whenever the two offsets agree there. -/
theorem positiveGridRowOffsetInterpolation_shear_fixed {q₀ q₁ : ℂ × ℝ → ℝ}
    (p : Circle × ℂ) (h : q₀ ((p.1 : ℂ), p.2.re) = q₁ ((p.1 : ℂ), p.2.re)) (s : ℝ) :
    positiveGridRowShearCylinder (positiveGridRowOffsetInterpolation q₀ q₁ s) 1 p =
      positiveGridRowShearCylinder q₀ 1 p := by
  apply Prod.ext
  · rfl
  · simp only [positiveGridRowShearCylinder, positiveGridRowShear_one,
      positiveGridRowOffsetInterpolation_eq_of_eq h]

/-- Every interpolated offset has the same prescribed value on the complete
original horizontal arcs, including both native marking corners. -/
theorem positiveGridRowOffsetInterpolation_on_horizontalArcs {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    {q₀ q₁ : ℂ × ℝ → ℝ}
    (h₀ : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q₀ p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (h₁ : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q₁ p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a) (s : ℝ) :
    ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      positiveGridRowOffsetInterpolation q₀ q₁ s p =
        g ((positiveRectilinearOutgoingArc w).symm a) -
          positiveRectilinearHorizontalArcRow w a := by
  intro a p hp
  rw [positiveGridRowOffsetInterpolation_eq_of_eq ((h₀ a p hp).trans (h₁ a p hp).symm), h₀ a p hp]

/-- The exact same native `X` and `O` coordinates and strand depths are retained
at every row-offset interpolation time. -/
theorem positiveGridRowOffsetInterpolation_markedCorner {m : ℕ}
    (w : PositiveAdjacentWord m) (g : Fin w.length × Fin 3 → ℝ)
    {q₀ q₁ : ℂ × ℝ → ℝ}
    (h₀ : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q₀ p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (h₁ : ∀ a p, p ∈ positiveRectilinearHorizontalArcSet w a →
      q₁ p = g ((positiveRectilinearOutgoingArc w).symm a) -
        positiveRectilinearHorizontalArcRow w a)
    (G : TauCeti.GridDiagram (w.length * 3)) (row : Fin (w.length * 3) → ℝ)
    (hO : ∀ p, row (G.O (finProdFinEquiv p)) = g p)
    (hX : ∀ p, row (G.X (finProdFinEquiv p)) =
      g ((positiveRectilinearWordMatching w).symm p)) (s : ℝ) (j : Fin w.length)
    (c : Fin 3) (o : Bool) :
    positiveGridRowShearCylinder (positiveGridRowOffsetInterpolation q₀ q₁ s) 1
      (positiveRectilinearCylinderPoint w (positiveRectilinearWordMarkedCorner w j c o)) =
        positiveWordNativeMarkedCorner w G row j c o :=
  positiveGridRowShear_markedCorner w g
    (positiveGridRowOffsetInterpolation_on_horizontalArcs w g h₀ h₁ s) G row hO hX j c o

end OnLeConjecture.KnotTheory
