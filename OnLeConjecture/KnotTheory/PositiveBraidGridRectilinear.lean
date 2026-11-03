/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridGenerator
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Diagram.Basic
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-! # The three-move rectilinear positive crossing

The projection coordinates are horizontal position and real height. Imaginary
height records depth. The lower strand travels up to the middle row, across,
and up again. The upper strand travels down across that middle horizontal
segment. Its depth is larger, so the vertical segment passes over the
horizontal segment, as in Ng--Thurston, Proposition 7(3), Figure 10.

The polygonal endpoint is a continuous embedded tangle. It is not asserted to
be smooth at its corners. Global row separation, grid markings, cyclic closure,
and corner smoothing are not supplied by the local construction.
-/

@[expose] public noncomputable section

open Set
open scoped Topology ContDiff

namespace OnLeConjecture.KnotTheory

/-- A clipped affine ramp. -/
def positiveGridRectilinearRamp (h x : ℝ) : ℝ := max 0 (min h x)

/-- Vertical progress on the lower strand, with two moves of height one half. -/
def positiveGridRectilinearLowerRise (t : ℝ) : ℝ :=
  positiveGridRectilinearRamp (1 / 2) (2 * t - 1 / 3) +
    positiveGridRectilinearRamp (1 / 2) (2 * t - 7 / 6)

/-- Vertical progress on the upper strand, with one move of height one. -/
def positiveGridRectilinearUpperDrop (t : ℝ) : ℝ :=
  positiveGridRectilinearRamp 1 (2 * t - 1 / 2)

/-- Constant depths of the moving strands. -/
def positiveGridRectilinearDepth {m : ℕ} (i : Fin (m - 1)) (k : Fin m) : ℝ :=
  if k = adjacentLower i then -1 else if k = adjacentUpper i then 1 else 0

/-- Horizontal position of the polygonal strand. -/
def positiveGridRectilinearHorizontal {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (t : ℝ) : ℝ :=
  if k = adjacentLower i then 2 * t - positiveGridRectilinearLowerRise t
  else if k = adjacentUpper i then 2 * t - positiveGridRectilinearUpperDrop t else t

/-- Real height of the polygonal strand. -/
def positiveGridRectilinearRow {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (t : ℝ) : ℝ :=
  if k = adjacentLower i then (i.val : ℝ) + positiveGridRectilinearLowerRise t
  else if k = adjacentUpper i then (i.val : ℝ) + 1 - positiveGridRectilinearUpperDrop t
  else (k.val : ℝ)

/-- Literal polygonal strands in horizontal-position times complex-height space. -/
def positiveGridRectilinear {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (t : ℝ) : ℝ × ℂ :=
  (positiveGridRectilinearHorizontal i k t,
    (positiveGridRectilinearRow i k t : ℂ) +
      (positiveGridRectilinearDepth i k : ℂ) * Complex.I)

/-- Deformation from the smooth adjacent crossing at constant depths to the
literal rectilinear crossing. -/
def positiveGridRectilinearDeformation {m : ℕ} (i : Fin (m - 1))
    (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  ((1 - s) * t + s * positiveGridRectilinearHorizontal i k t,
    (((1 - s) * positiveAdjacentReal i k t + s * positiveGridRectilinearRow i k t : ℝ) : ℂ) +
      (positiveGridRectilinearDepth i k : ℂ) * Complex.I)

private theorem lower_ne_upper {m : ℕ} (i : Fin (m - 1)) :
    adjacentLower i ≠ adjacentUpper i := by
  intro he
  have hh := congrArg Fin.val he
  change i.val = i.val + 1 at hh
  omega

@[simp] theorem positiveGridRectilinearDepth_lower {m : ℕ} (i : Fin (m - 1)) :
    positiveGridRectilinearDepth i (adjacentLower i) = -1 := by
  simp [positiveGridRectilinearDepth]

@[simp] theorem positiveGridRectilinearDepth_upper {m : ℕ} (i : Fin (m - 1)) :
    positiveGridRectilinearDepth i (adjacentUpper i) = 1 := by
  simp [positiveGridRectilinearDepth, (lower_ne_upper i).symm]

theorem positiveGridRectilinearDepth_eq_neg_one_iff {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) :
    positiveGridRectilinearDepth i k = -1 ↔ k = adjacentLower i := by
  simp only [positiveGridRectilinearDepth]
  split_ifs <;> simp_all
  all_goals norm_num

theorem positiveGridRectilinearDepth_eq_one_iff {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) :
    positiveGridRectilinearDepth i k = 1 ↔ k = adjacentUpper i := by
  simp only [positiveGridRectilinearDepth]
  split_ifs with h h <;> simp_all
  all_goals norm_num

theorem positiveGridRectilinearRamp_of_nonpos {h x : ℝ} (hx : x ≤ 0) :
    positiveGridRectilinearRamp h x = 0 :=
  max_eq_left ((min_le_right h x).trans hx)

theorem positiveGridRectilinearRamp_of_le {h x : ℝ} (hx : 0 ≤ x) (xh : x ≤ h) :
    positiveGridRectilinearRamp h x = x := by
  simp only [positiveGridRectilinearRamp, min_eq_right xh, max_eq_right hx]

theorem positiveGridRectilinearRamp_of_ge {h x : ℝ} (hh : 0 ≤ h) (hx : h ≤ x) :
    positiveGridRectilinearRamp h x = h := by
  simp only [positiveGridRectilinearRamp, min_eq_left hx, max_eq_right hh]

theorem positiveGridRectilinearRamp_continuous (h : ℝ) :
    Continuous (positiveGridRectilinearRamp h) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem positiveGridRectilinearLowerRise_continuous :
    Continuous positiveGridRectilinearLowerRise :=
  ((positiveGridRectilinearRamp_continuous _).comp
    ((continuous_const.mul continuous_id).sub continuous_const)).add
      ((positiveGridRectilinearRamp_continuous _).comp
        ((continuous_const.mul continuous_id).sub continuous_const))

theorem positiveGridRectilinearUpperDrop_continuous :
    Continuous positiveGridRectilinearUpperDrop :=
  (positiveGridRectilinearRamp_continuous _).comp
    ((continuous_const.mul continuous_id).sub continuous_const)

theorem positiveGridRectilinearHorizontal_continuous {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) : Continuous (positiveGridRectilinearHorizontal i k) := by
  unfold positiveGridRectilinearHorizontal
  split_ifs
  · exact (continuous_const.mul continuous_id).sub positiveGridRectilinearLowerRise_continuous
  · exact (continuous_const.mul continuous_id).sub positiveGridRectilinearUpperDrop_continuous
  · exact continuous_id

theorem positiveGridRectilinearRow_continuous {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) : Continuous (positiveGridRectilinearRow i k) := by
  unfold positiveGridRectilinearRow
  split_ifs
  · exact continuous_const.add positiveGridRectilinearLowerRise_continuous
  · exact continuous_const.sub positiveGridRectilinearUpperDrop_continuous
  · exact continuous_const

/-- Joint continuity of the deformation, with no hidden piecewise gluing premise. -/
theorem positiveGridRectilinearDeformation_continuous {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) :
    Continuous (fun p : ℝ × ℝ => positiveGridRectilinearDeformation i k p.1 p.2) := by
  apply Continuous.prodMk
  · exact ((continuous_const.sub continuous_fst).mul continuous_snd).add
      (continuous_fst.mul ((positiveGridRectilinearHorizontal_continuous i k).comp continuous_snd))
  · exact (Complex.continuous_ofReal.comp
      (((continuous_const.sub continuous_fst).mul
        ((positiveAdjacentReal_contDiff i k).continuous.comp continuous_snd)).add
          (continuous_fst.mul ((positiveGridRectilinearRow_continuous i k).comp
            continuous_snd)))).add continuous_const

@[simp] theorem positiveGridRectilinearDeformation_re {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (s t : ℝ) :
    (positiveGridRectilinearDeformation i k s t).2.re =
      (1 - s) * positiveAdjacentReal i k t + s * positiveGridRectilinearRow i k t := by
  simp [positiveGridRectilinearDeformation]

@[simp] theorem positiveGridRectilinearDeformation_im {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (s t : ℝ) :
    (positiveGridRectilinearDeformation i k s t).2.im = positiveGridRectilinearDepth i k := by
  simp [positiveGridRectilinearDeformation]

@[simp] theorem positiveGridRectilinearDeformation_zero {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (t : ℝ) :
    positiveGridRectilinearDeformation i k 0 t =
      (t, positiveAdjacentHeight i (positiveGridRectilinearDepth i) k t) := by
  simp [positiveGridRectilinearDeformation, positiveAdjacentHeight]

@[simp] theorem positiveGridRectilinearDeformation_one {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (t : ℝ) :
    positiveGridRectilinearDeformation i k 1 t = positiveGridRectilinear i k t := by
  simp [positiveGridRectilinearDeformation, positiveGridRectilinear]

/-- Horizontal plus vertical progress is independent of the ramp breakpoints. -/
theorem positiveGridRectilinearDeformation_lower_progress {m : ℕ}
    (i : Fin (m - 1)) (s t : ℝ) :
    (positiveGridRectilinearDeformation i (adjacentLower i) s t).1 +
      (positiveGridRectilinearDeformation i (adjacentLower i) s t).2.re - i.val =
        (1 + s) * t + (1 - s) * Real.smoothTransition t := by
  simp only [positiveGridRectilinearDeformation, positiveGridRectilinearHorizontal,
    positiveGridRectilinearRow, ite_true, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero, positiveAdjacentReal_lower]
  ring

theorem positiveGridRectilinearDeformation_upper_progress {m : ℕ}
    (i : Fin (m - 1)) (s t : ℝ) :
    (positiveGridRectilinearDeformation i (adjacentUpper i) s t).1 -
      (positiveGridRectilinearDeformation i (adjacentUpper i) s t).2.re + (i.val + 1) =
        (1 + s) * t + (1 - s) * Real.smoothTransition t := by
  simp only [positiveGridRectilinearDeformation, positiveGridRectilinearHorizontal,
    positiveGridRectilinearRow, if_neg (lower_ne_upper i).symm, ite_true,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    positiveAdjacentReal_upper]
  ring

theorem positiveGridRectilinearDeformation_fixed {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (hk₀ : k ≠ adjacentLower i) (hk₁ : k ≠ adjacentUpper i)
    (s t : ℝ) : positiveGridRectilinearDeformation i k s t = (t, (k.val : ℂ)) := by
  simp only [positiveGridRectilinearDeformation, positiveGridRectilinearHorizontal,
    positiveGridRectilinearRow, positiveGridRectilinearDepth, if_neg hk₀, if_neg hk₁,
    positiveAdjacentReal_fixed i k hk₀ hk₁, Complex.ofReal_zero, zero_mul, add_zero]
  congr 1 <;> push_cast <;> ring

private theorem progress_strictMono {s : ℝ} (hs : s ∈ Icc 0 1) :
    StrictMono (fun t : ℝ => (1 + s) * t + (1 - s) * Real.smoothTransition t) := by
  intro t u htu
  have hp : 0 < 1 + s := by linarith [hs.1]
  have ht := mul_lt_mul_of_pos_left htu hp
  have hq := mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone htu.le)
    (sub_nonneg.mpr hs.2)
  exact add_lt_add_of_lt_of_le ht hq

/-- Distinct labels cannot meet, even when their parameters differ. -/
theorem positiveGridRectilinearDeformation_label_eq {m : ℕ}
    (i : Fin (m - 1)) (k l : Fin m) (s t u : ℝ)
    (he : positiveGridRectilinearDeformation i k s t =
      positiveGridRectilinearDeformation i l s u) : k = l := by
  have hd := congrArg (fun p : ℝ × ℂ => p.2.im) he
  simp only [positiveGridRectilinearDeformation_im] at hd
  by_cases hk₀ : k = adjacentLower i
  · subst k
    exact ((positiveGridRectilinearDepth_eq_neg_one_iff i l).mp
      (hd.symm.trans (positiveGridRectilinearDepth_lower i))).symm
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    exact ((positiveGridRectilinearDepth_eq_one_iff i l).mp
      (hd.symm.trans (positiveGridRectilinearDepth_upper i))).symm
  have hl₀ : l ≠ adjacentLower i := by
    intro hl
    exact hk₀ ((positiveGridRectilinearDepth_eq_neg_one_iff i k).mp (by simpa [hl] using hd))
  have hl₁ : l ≠ adjacentUpper i := by
    intro hl
    exact hk₁ ((positiveGridRectilinearDepth_eq_one_iff i k).mp (by simpa [hl] using hd))
  rw [positiveGridRectilinearDeformation_fixed i k hk₀ hk₁,
    positiveGridRectilinearDeformation_fixed i l hl₀ hl₁] at he
  exact Fin.ext (Nat.cast_injective (congrArg Prod.snd he))

/-- Each deformation slice is injective on the whole disjoint union of strands. -/
theorem positiveGridRectilinearDeformation_injective {m : ℕ}
    (i : Fin (m - 1)) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Function.Injective (fun p : Fin m × ℝ => positiveGridRectilinearDeformation i p.1 s p.2) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hkl := positiveGridRectilinearDeformation_label_eq i k l s t u he
  subst l
  suffices t = u by simp [this]
  by_cases hk₀ : k = adjacentLower i
  · subst k
    apply (progress_strictMono hs).injective
    simpa only [positiveGridRectilinearDeformation_lower_progress] using
      congrArg (fun p : ℝ × ℂ => p.1 + p.2.re - i.val) he
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    apply (progress_strictMono hs).injective
    simpa only [positiveGridRectilinearDeformation_upper_progress] using
      congrArg (fun p : ℝ × ℂ => p.1 - p.2.re + (i.val + 1)) he
  simpa only [positiveGridRectilinearDeformation_fixed i k hk₀ hk₁] using congrArg Prod.fst he


/-- The first deformation lifts the canonical generator to constant depths. -/
def positiveGridDepthLift {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (s t : ℝ) : ℝ × ℂ :=
  (t, positiveGridGeneratorDeformation i (positiveGridRectilinearDepth i) k (1 - s) t)

@[simp] theorem positiveGridDepthLift_zero {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (t : ℝ) :
    positiveGridDepthLift i k 0 t = (t, positiveGridGenerator i k t) := by
  simp [positiveGridDepthLift]

/-- The two deformations meet in exactly the same strand parametrization. -/
theorem positiveGridDepthLift_one {m : ℕ} (i : Fin (m - 1)) (k : Fin m) (t : ℝ) :
    positiveGridDepthLift i k 1 t = positiveGridRectilinearDeformation i k 0 t := by
  simp [positiveGridDepthLift]

theorem positiveGridDepthLift_contDiff {m : ℕ} (i : Fin (m - 1)) (k : Fin m) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => positiveGridDepthLift i k p.1 p.2) :=
  contDiff_snd.prodMk ((positiveGridGeneratorDeformation_contDiff i _ k).comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd))

theorem positiveGridDepthLift_injective {m : ℕ}
    (i : Fin (m - 1)) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Function.Injective (fun p : Fin m × ℝ => positiveGridDepthLift i p.1 s p.2) := by
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have htu : t = u := congrArg Prod.fst he
  subst u
  have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
  have hy : positiveGridRectilinearDepth i (adjacentLower i) <
      positiveGridRectilinearDepth i (adjacentUpper i) := by simp
  have hkl := positiveGridGeneratorDeformation_injective i _ hy hs' t (congrArg Prod.snd he)
  change k = l at hkl
  simp [hkl]

/-- Each slice is a closed embedding of the compact disjoint union of strand intervals. -/
theorem positiveGridRectilinearDeformation_isClosedEmbedding {m : ℕ}
    (i : Fin (m - 1)) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Topology.IsClosedEmbedding (fun p : Σ _k : Fin m, unitInterval =>
      positiveGridRectilinearDeformation i p.1 s p.2) := by
  have hc : Continuous (fun p : Σ _k : Fin m, unitInterval =>
      positiveGridRectilinearDeformation i p.1 s p.2) :=
    continuous_sigma fun k => (positiveGridRectilinearDeformation_continuous i k).comp
      (continuous_const.prodMk continuous_subtype_val)
  apply hc.isClosedEmbedding
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hp := positiveGridRectilinearDeformation_injective i hs
    (a₁ := (k, (t : ℝ))) (a₂ := (l, (u : ℝ))) he
  have hk : k = l := congrArg Prod.fst hp
  have ht := Subtype.ext (congrArg Prod.snd hp)
  subst l
  subst u
  rfl

theorem positiveGridDepthLift_isClosedEmbedding {m : ℕ}
    (i : Fin (m - 1)) {s : ℝ} (hs : s ∈ Icc 0 1) :
    Topology.IsClosedEmbedding (fun p : Σ _k : Fin m, unitInterval =>
      positiveGridDepthLift i p.1 s p.2) := by
  have hc : Continuous (fun p : Σ _k : Fin m, unitInterval =>
      positiveGridDepthLift i p.1 s p.2) :=
    continuous_sigma fun k => (positiveGridDepthLift_contDiff i k).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)
  apply hc.isClosedEmbedding
  rintro ⟨k, t⟩ ⟨l, u⟩ he
  have hp := positiveGridDepthLift_injective i hs
    (a₁ := (k, (t : ℝ))) (a₂ := (l, (u : ℝ))) he
  have hk : k = l := congrArg Prod.fst hp
  have ht := Subtype.ext (congrArg Prod.snd hp)
  subst l
  subst u
  rfl

/-- The literal polygonal tangle is a closed embedding of the disjoint strand intervals. -/
theorem positiveGridRectilinear_isClosedEmbedding {m : ℕ} (i : Fin (m - 1)) :
    Topology.IsClosedEmbedding (fun p : Σ _k : Fin m, unitInterval =>
      positiveGridRectilinear i p.1 p.2) := by
  simpa only [positiveGridRectilinearDeformation_one] using
    positiveGridRectilinearDeformation_isClosedEmbedding i
      (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)

/-- Break times at the six lower-strand vertices, in constant L1-speed parametrization. -/
def positiveGridRectilinearLowerTimes : Fin 6 → ℝ := ![0, 1 / 6, 5 / 12, 7 / 12, 5 / 6, 1]

/-- Actual lower-strand vertices, with constant depth minus one. -/
def positiveGridRectilinearLowerCorners {m : ℕ} (i : Fin (m - 1)) : Fin 6 → ℝ × ℂ :=
  ![(0, (i.val : ℂ) - Complex.I),
    (1 / 3, (i.val : ℂ) - Complex.I),
    (1 / 3, (i.val : ℂ) + 1 / 2 - Complex.I),
    (2 / 3, (i.val : ℂ) + 1 / 2 - Complex.I),
    (2 / 3, (i.val : ℂ) + 1 - Complex.I),
    (1, (i.val : ℂ) + 1 - Complex.I)]

/-- Break times at the four upper-strand vertices. -/
def positiveGridRectilinearUpperTimes : Fin 4 → ℝ := ![0, 1 / 4, 3 / 4, 1]

/-- Actual upper-strand vertices, with constant depth plus one. -/
def positiveGridRectilinearUpperCorners {m : ℕ} (i : Fin (m - 1)) : Fin 4 → ℝ × ℂ :=
  ![(0, (i.val : ℂ) + 1 + Complex.I),
    (1 / 2, (i.val : ℂ) + 1 + Complex.I),
    (1 / 2, (i.val : ℂ) + Complex.I),
    (1, (i.val : ℂ) + Complex.I)]

theorem positiveGridRectilinear_lower_corners {m : ℕ}
    (i : Fin (m - 1)) (j : Fin 6) :
    positiveGridRectilinear i (adjacentLower i) (positiveGridRectilinearLowerTimes j) =
      positiveGridRectilinearLowerCorners i j := by
  fin_cases j <;>
    norm_num [positiveGridRectilinearLowerTimes, positiveGridRectilinearLowerCorners,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      positiveGridRectilinearLowerRise, positiveGridRectilinearRamp] <;> ring

theorem positiveGridRectilinear_upper_corners {m : ℕ}
    (i : Fin (m - 1)) (j : Fin 4) :
    positiveGridRectilinear i (adjacentUpper i) (positiveGridRectilinearUpperTimes j) =
      positiveGridRectilinearUpperCorners i j := by
  fin_cases j <;>
    norm_num [positiveGridRectilinearUpperTimes, positiveGridRectilinearUpperCorners,
      positiveGridRectilinear, positiveGridRectilinearHorizontal, positiveGridRectilinearRow,
      (lower_ne_upper i).symm, positiveGridRectilinearUpperDrop, positiveGridRectilinearRamp]


/-- Projection to the rectangular drawing plane. -/
def positiveGridRectilinearProjection (p : ℝ × ℂ) : ℝ × ℝ := (p.1, p.2.re)

@[simp] theorem positiveGridRectilinearProjection_lower {m : ℕ}
    (i : Fin (m - 1)) (t : ℝ) :
    positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
      (2 * t - positiveGridRectilinearLowerRise t,
        (i.val : ℝ) + positiveGridRectilinearLowerRise t) := by
  simp [positiveGridRectilinearProjection, positiveGridRectilinear,
    positiveGridRectilinearHorizontal, positiveGridRectilinearRow]

@[simp] theorem positiveGridRectilinearProjection_upper {m : ℕ}
    (i : Fin (m - 1)) (t : ℝ) :
    positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentUpper i) t) =
      (2 * t - positiveGridRectilinearUpperDrop t,
        (i.val : ℝ) + 1 - positiveGridRectilinearUpperDrop t) := by
  simp [positiveGridRectilinearProjection, positiveGridRectilinear,
    positiveGridRectilinearHorizontal, positiveGridRectilinearRow, (lower_ne_upper i).symm]

theorem positiveGridRectilinearLowerRise_first {t : ℝ} (ht : t ≤ 1 / 6) :
    positiveGridRectilinearLowerRise t = 0 := by
  rw [positiveGridRectilinearLowerRise,
    positiveGridRectilinearRamp_of_nonpos (show 2 * t - 1 / 3 ≤ 0 by linarith),
    positiveGridRectilinearRamp_of_nonpos (show 2 * t - 7 / 6 ≤ 0 by linarith)]
  norm_num

theorem positiveGridRectilinearLowerRise_second {t : ℝ} (ht : t ∈ Icc (1 / 6) (5 / 12)) :
    positiveGridRectilinearLowerRise t = 2 * t - 1 / 3 := by
  rw [positiveGridRectilinearLowerRise,
    positiveGridRectilinearRamp_of_le (show 0 ≤ 2 * t - 1 / 3 by linarith [ht.1])
      (show 2 * t - 1 / 3 ≤ 1 / 2 by linarith [ht.2]),
    positiveGridRectilinearRamp_of_nonpos (show 2 * t - 7 / 6 ≤ 0 by linarith [ht.2])]
  ring

theorem positiveGridRectilinearLowerRise_third {t : ℝ} (ht : t ∈ Icc (5 / 12) (7 / 12)) :
    positiveGridRectilinearLowerRise t = 1 / 2 := by
  rw [positiveGridRectilinearLowerRise,
    positiveGridRectilinearRamp_of_ge (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show 1 / 2 ≤ 2 * t - 1 / 3 by linarith [ht.1]),
    positiveGridRectilinearRamp_of_nonpos (show 2 * t - 7 / 6 ≤ 0 by linarith [ht.2])]
  ring

theorem positiveGridRectilinearLowerRise_fourth {t : ℝ} (ht : t ∈ Icc (7 / 12) (5 / 6)) :
    positiveGridRectilinearLowerRise t = 2 * t - 2 / 3 := by
  rw [positiveGridRectilinearLowerRise,
    positiveGridRectilinearRamp_of_ge (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show 1 / 2 ≤ 2 * t - 1 / 3 by linarith [ht.1]),
    positiveGridRectilinearRamp_of_le (show 0 ≤ 2 * t - 7 / 6 by linarith [ht.1])
      (show 2 * t - 7 / 6 ≤ 1 / 2 by linarith [ht.2])]
  ring

theorem positiveGridRectilinearLowerRise_fifth {t : ℝ} (ht : 5 / 6 ≤ t) :
    positiveGridRectilinearLowerRise t = 1 := by
  rw [positiveGridRectilinearLowerRise,
    positiveGridRectilinearRamp_of_ge (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show 1 / 2 ≤ 2 * t - 1 / 3 by linarith),
    positiveGridRectilinearRamp_of_ge (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show 1 / 2 ≤ 2 * t - 7 / 6 by linarith)]
  norm_num

theorem positiveGridRectilinearUpperDrop_first {t : ℝ} (ht : t ≤ 1 / 4) :
    positiveGridRectilinearUpperDrop t = 0 :=
  positiveGridRectilinearRamp_of_nonpos (by linarith)

theorem positiveGridRectilinearUpperDrop_second {t : ℝ} (ht : t ∈ Icc (1 / 4) (3 / 4)) :
    positiveGridRectilinearUpperDrop t = 2 * t - 1 / 2 :=
  positiveGridRectilinearRamp_of_le (by linarith [ht.1]) (by linarith [ht.2])

theorem positiveGridRectilinearUpperDrop_third {t : ℝ} (ht : 3 / 4 ≤ t) :
    positiveGridRectilinearUpperDrop t = 1 :=
  positiveGridRectilinearRamp_of_ge (by norm_num) (by linarith)

/-- The five lower segments, with their exact affine coordinates. -/
theorem positiveGridRectilinear_lower_segments {m : ℕ} (i : Fin (m - 1)) :
    (∀ t ∈ Icc (0 : ℝ) (1 / 6),
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
        (2 * t, (i.val : ℝ))) ∧
    (∀ t ∈ Icc (1 / 6 : ℝ) (5 / 12),
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
        (1 / 3, (i.val : ℝ) + 2 * t - 1 / 3)) ∧
    (∀ t ∈ Icc (5 / 12 : ℝ) (7 / 12),
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
        (2 * t - 1 / 2, (i.val : ℝ) + 1 / 2)) ∧
    (∀ t ∈ Icc (7 / 12 : ℝ) (5 / 6),
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
        (2 / 3, (i.val : ℝ) + 2 * t - 2 / 3)) ∧
    (∀ t ∈ Icc (5 / 6 : ℝ) 1,
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
        (2 * t - 1, (i.val : ℝ) + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [positiveGridRectilinearLowerRise_first ht.2]
  · intro t ht
    rw [positiveGridRectilinearProjection_lower, positiveGridRectilinearLowerRise_second ht]
    ext <;> ring
  · intro t ht
    rw [positiveGridRectilinearProjection_lower, positiveGridRectilinearLowerRise_third ht]
  · intro t ht
    rw [positiveGridRectilinearProjection_lower, positiveGridRectilinearLowerRise_fourth ht]
    ext <;> ring
  · intro t ht
    rw [positiveGridRectilinearProjection_lower, positiveGridRectilinearLowerRise_fifth ht.1]

/-- The upper strand has one vertical segment, between its two horizontal segments. -/
theorem positiveGridRectilinear_upper_segments {m : ℕ} (i : Fin (m - 1)) :
    (∀ t ∈ Icc (0 : ℝ) (1 / 4),
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentUpper i) t) =
        (2 * t, (i.val : ℝ) + 1)) ∧
    (∀ t ∈ Icc (1 / 4 : ℝ) (3 / 4),
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentUpper i) t) =
        (1 / 2, (i.val : ℝ) + 3 / 2 - 2 * t)) ∧
    (∀ t ∈ Icc (3 / 4 : ℝ) 1,
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentUpper i) t) =
        (2 * t - 1, (i.val : ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simp [positiveGridRectilinearUpperDrop_first ht.2]
  · intro t ht
    rw [positiveGridRectilinearProjection_upper, positiveGridRectilinearUpperDrop_second ht]
    ext <;> ring
  · intro t ht
    rw [positiveGridRectilinearProjection_upper, positiveGridRectilinearUpperDrop_third ht.1]
    ext <;> ring

private theorem lower_rise_cases {t : ℝ} (ht : t ∈ Icc 0 1) :
    (0 ≤ t ∧ t ≤ 1 / 6 ∧ positiveGridRectilinearLowerRise t = 0) ∨
    (1 / 6 ≤ t ∧ t ≤ 5 / 12 ∧ positiveGridRectilinearLowerRise t = 2 * t - 1 / 3) ∨
    (5 / 12 ≤ t ∧ t ≤ 7 / 12 ∧ positiveGridRectilinearLowerRise t = 1 / 2) ∨
    (7 / 12 ≤ t ∧ t ≤ 5 / 6 ∧ positiveGridRectilinearLowerRise t = 2 * t - 2 / 3) ∨
    (5 / 6 ≤ t ∧ t ≤ 1 ∧ positiveGridRectilinearLowerRise t = 1) := by
  by_cases h₁ : t ≤ 1 / 6
  · exact Or.inl ⟨ht.1, h₁, positiveGridRectilinearLowerRise_first h₁⟩
  right
  by_cases h₂ : t ≤ 5 / 12
  · exact Or.inl ⟨le_of_not_ge h₁, h₂,
      positiveGridRectilinearLowerRise_second ⟨le_of_not_ge h₁, h₂⟩⟩
  right
  by_cases h₃ : t ≤ 7 / 12
  · exact Or.inl ⟨le_of_not_ge h₂, h₃,
      positiveGridRectilinearLowerRise_third ⟨le_of_not_ge h₂, h₃⟩⟩
  right
  by_cases h₄ : t ≤ 5 / 6
  · exact Or.inl ⟨le_of_not_ge h₃, h₄,
      positiveGridRectilinearLowerRise_fourth ⟨le_of_not_ge h₃, h₄⟩⟩
  exact Or.inr ⟨le_of_not_ge h₄, ht.2, positiveGridRectilinearLowerRise_fifth (le_of_not_ge h₄)⟩

private theorem upper_drop_cases {t : ℝ} (ht : t ∈ Icc 0 1) :
    (0 ≤ t ∧ t ≤ 1 / 4 ∧ positiveGridRectilinearUpperDrop t = 0) ∨
    (1 / 4 ≤ t ∧ t ≤ 3 / 4 ∧ positiveGridRectilinearUpperDrop t = 2 * t - 1 / 2) ∨
    (3 / 4 ≤ t ∧ t ≤ 1 ∧ positiveGridRectilinearUpperDrop t = 1) := by
  by_cases h₁ : t ≤ 1 / 4
  · exact Or.inl ⟨ht.1, h₁, positiveGridRectilinearUpperDrop_first h₁⟩
  right
  by_cases h₂ : t ≤ 3 / 4
  · exact Or.inl ⟨le_of_not_ge h₁, h₂,
      positiveGridRectilinearUpperDrop_second ⟨le_of_not_ge h₁, h₂⟩⟩
  exact Or.inr ⟨le_of_not_ge h₂, ht.2, positiveGridRectilinearUpperDrop_third (le_of_not_ge h₂)⟩

/-- The two moving projected strands meet exactly once, at both parameter midpoints. -/
theorem positiveGridRectilinear_crossing_iff {m : ℕ} (i : Fin (m - 1))
    {t u : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1) :
    positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) t) =
      positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentUpper i) u) ↔
        t = 1 / 2 ∧ u = 1 / 2 := by
  rw [positiveGridRectilinearProjection_lower, positiveGridRectilinearProjection_upper,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hy⟩
    rcases lower_rise_cases ht with ⟨hl₀, hl₁, hv⟩ | ⟨hl₀, hl₁, hv⟩ |
      ⟨hl₀, hl₁, hv⟩ | ⟨hl₀, hl₁, hv⟩ | ⟨hl₀, hl₁, hv⟩
    all_goals
      rcases upper_drop_cases hu with ⟨hu₀, hu₁, hw⟩ | ⟨hu₀, hu₁, hw⟩ | ⟨hu₀, hu₁, hw⟩
      all_goals
        rw [hv, hw] at hx hy
        constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [positiveGridRectilinearLowerRise, positiveGridRectilinearUpperDrop,
      positiveGridRectilinearRamp]
    ring

/-- The sole crossing has the upper vertical strand above the lower horizontal strand. -/
theorem positiveGridRectilinear_crossing_depth {m : ℕ} (i : Fin (m - 1)) :
    (positiveGridRectilinear i (adjacentLower i) (1 / 2)).2.im = -1 ∧
    (positiveGridRectilinear i (adjacentUpper i) (1 / 2)).2.im = 1 ∧
    positiveGridRectilinearProjection (positiveGridRectilinear i (adjacentLower i) (1 / 2)) =
      (1 / 2, (i.val : ℝ) + 1 / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [positiveGridRectilinear]
  · simp [positiveGridRectilinear]
  · rw [positiveGridRectilinearProjection_lower,
      positiveGridRectilinearLowerRise_third (by constructor <;> norm_num)]
    norm_num


private theorem ramp_bounds (h : ℝ) (hh : 0 ≤ h) (x : ℝ) :
    positiveGridRectilinearRamp h x ∈ Icc 0 h :=
  ⟨le_max_left _ _, max_le hh (min_le_left _ _)⟩

private theorem lower_rise_bounds (t : ℝ) : positiveGridRectilinearLowerRise t ∈ Icc 0 1 := by
  have h₁ := ramp_bounds (1 / 2) (by norm_num) (2 * t - 1 / 3)
  have h₂ := ramp_bounds (1 / 2) (by norm_num) (2 * t - 7 / 6)
  dsimp only [positiveGridRectilinearLowerRise]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

private theorem label_of_row_between {m : ℕ} (i : Fin (m - 1)) (k : Fin m)
    (h : (k.val : ℝ) ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1)) :
    k = adjacentLower i ∨ k = adjacentUpper i := by
  have h₀ : i.val ≤ k.val := by exact_mod_cast h.1
  have h₁ : k.val ≤ i.val + 1 := by exact_mod_cast h.2
  by_cases he : k.val = i.val
  · exact Or.inl (Fin.ext he)
  · exact Or.inr (Fin.ext (by change k.val = i.val + 1; omega))

theorem positiveGridRectilinear_fixed {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (hk₀ : k ≠ adjacentLower i) (hk₁ : k ≠ adjacentUpper i)
    (t : ℝ) : positiveGridRectilinear i k t = (t, (k.val : ℂ)) := by
  simpa only [positiveGridRectilinearDeformation_one] using
    positiveGridRectilinearDeformation_fixed i k hk₀ hk₁ 1 t

/-- A strand at a fixed integer row cannot acquire an additional projected crossing. -/
theorem positiveGridRectilinear_label_eq_of_projection_fixed {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (hk₀ : k ≠ adjacentLower i) (hk₁ : k ≠ adjacentUpper i)
    (l : Fin m) (t u : ℝ)
    (he : positiveGridRectilinearProjection (positiveGridRectilinear i l t) =
      (u, (k.val : ℝ))) : l = k := by
  have hr := congrArg Prod.snd he
  by_cases hl₀ : l = adjacentLower i
  · subst l
    rw [positiveGridRectilinearProjection_lower] at hr
    have hb := lower_rise_bounds t
    have hm : (k.val : ℝ) ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1) := by
      constructor <;> dsimp at hr <;> linarith [hb.1, hb.2]
    exact ((label_of_row_between i k hm).elim hk₀ hk₁).elim
  by_cases hl₁ : l = adjacentUpper i
  · subst l
    rw [positiveGridRectilinearProjection_upper] at hr
    have hb := ramp_bounds 1 (by norm_num) (2 * t - 1 / 2)
    change positiveGridRectilinearUpperDrop t ∈ Icc 0 1 at hb
    have hm : (k.val : ℝ) ∈ Icc (i.val : ℝ) ((i.val : ℝ) + 1) := by
      constructor <;> dsimp at hr <;> linarith [hb.1, hb.2]
    exact ((label_of_row_between i k hm).elim hk₀ hk₁).elim
  rw [positiveGridRectilinear_fixed i l hl₀ hl₁] at hr
  simp only [positiveGridRectilinearProjection, Complex.natCast_re] at hr
  exact Fin.ext (Nat.cast_injective hr)

/-- The complete projected tangle has exactly the one prescribed positive crossing. -/
theorem positiveGridRectilinear_projected_crossing_iff {m : ℕ}
    (i : Fin (m - 1)) {k l : Fin m} (hkl : k ≠ l)
    {t u : ℝ} (ht : t ∈ Icc 0 1) (hu : u ∈ Icc 0 1) :
    positiveGridRectilinearProjection (positiveGridRectilinear i k t) =
      positiveGridRectilinearProjection (positiveGridRectilinear i l u) ↔
      ((k = adjacentLower i ∧ l = adjacentUpper i) ∨
        (k = adjacentUpper i ∧ l = adjacentLower i)) ∧ t = 1 / 2 ∧ u = 1 / 2 := by
  constructor
  · intro he
    have hk : k = adjacentLower i ∨ k = adjacentUpper i := by
      by_contra hn
      push Not at hn
      have hf := he.symm
      rw [positiveGridRectilinear_fixed i k hn.1 hn.2] at hf
      have hh := positiveGridRectilinear_label_eq_of_projection_fixed i k hn.1 hn.2 l u t hf
      exact hkl hh.symm
    have hl : l = adjacentLower i ∨ l = adjacentUpper i := by
      by_contra hn
      push Not at hn
      rw [positiveGridRectilinear_fixed i l hn.1 hn.2] at he
      exact hkl (positiveGridRectilinear_label_eq_of_projection_fixed i l hn.1 hn.2 k t u he)
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
    · exact (hkl rfl).elim
    · exact ⟨Or.inl ⟨rfl, rfl⟩, (positiveGridRectilinear_crossing_iff i ht hu).mp he⟩
    · have hh := (positiveGridRectilinear_crossing_iff i hu ht).mp he.symm
      exact ⟨Or.inr ⟨rfl, rfl⟩, hh.2, hh.1⟩
    · exact (hkl rfl).elim
  · rintro ⟨h | h, rfl, rfl⟩ <;> rcases h with ⟨rfl, rfl⟩
    · exact (positiveGridRectilinear_crossing_iff i ht hu).mpr ⟨rfl, rfl⟩
    · exact ((positiveGridRectilinear_crossing_iff i hu ht).mpr ⟨rfl, rfl⟩).symm

/-- The underpassing tangent is horizontal and oriented rightwards. -/
theorem positiveGridRectilinear_lower_crossing_tangent {m : ℕ} (i : Fin (m - 1)) :
    HasDerivAt (fun t => positiveGridRectilinearProjection
      (positiveGridRectilinear i (adjacentLower i) t)) (2, 0) (1 / 2) := by
  have he : (fun t => positiveGridRectilinearProjection
      (positiveGridRectilinear i (adjacentLower i) t)) =ᶠ[𝓝 (1 / 2 : ℝ)]
      fun t => (2 * t - 1 / 2, (i.val : ℝ) + 1 / 2) := by
    filter_upwards [Ioo_mem_nhds (show (5 / 12 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 7 / 12 by norm_num)] with t ht
    exact (positiveGridRectilinear_lower_segments i).2.2.1 t ⟨ht.1.le, ht.2.le⟩
  have hd : HasDerivAt (fun t : ℝ => (2 * t - 1 / 2, (i.val : ℝ) + 1 / 2))
      (2, 0) (1 / 2) := by
    convert (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).sub_const (1 / 2)).prodMk
      (hasDerivAt_const (1 / 2 : ℝ) ((i.val : ℝ) + 1 / 2)) using 1 <;> norm_num
  exact hd.congr_of_eventuallyEq he

/-- The overpassing tangent is vertical and oriented downwards. -/
theorem positiveGridRectilinear_upper_crossing_tangent {m : ℕ} (i : Fin (m - 1)) :
    HasDerivAt (fun t => positiveGridRectilinearProjection
      (positiveGridRectilinear i (adjacentUpper i) t)) (0, -2) (1 / 2) := by
  have he : (fun t => positiveGridRectilinearProjection
      (positiveGridRectilinear i (adjacentUpper i) t)) =ᶠ[𝓝 (1 / 2 : ℝ)]
      fun t => (1 / 2, (i.val : ℝ) + 3 / 2 - 2 * t) := by
    filter_upwards [Ioo_mem_nhds (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 3 / 4 by norm_num)] with t ht
    exact (positiveGridRectilinear_upper_segments i).2.1 t ⟨ht.1.le, ht.2.le⟩
  have hd : HasDerivAt (fun t : ℝ => ((1 / 2 : ℝ), (i.val : ℝ) + 3 / 2 - 2 * t))
      (0, -2) (1 / 2) := by
    convert (hasDerivAt_const (1 / 2 : ℝ) (1 / 2 : ℝ)).prodMk
      (((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).const_sub ((i.val : ℝ) + 3 / 2))
      using 1 <;> norm_num
  exact hd.congr_of_eventuallyEq he


/-- The oriented determinant in overpass-then-underpass order is positive. -/
theorem positiveGridRectilinear_crossing_determinant {m : ℕ} (i : Fin (m - 1)) :
    let vUnder := deriv (fun t => positiveGridRectilinearProjection
      (positiveGridRectilinear i (adjacentLower i) t)) (1 / 2)
    let vOver := deriv (fun t => positiveGridRectilinearProjection
      (positiveGridRectilinear i (adjacentUpper i) t)) (1 / 2)
    vOver.1 * vUnder.2 - vOver.2 * vUnder.1 = 4 := by
  simp only [(positiveGridRectilinear_lower_crossing_tangent i).deriv,
    (positiveGridRectilinear_upper_crossing_tangent i).deriv]
  norm_num

/-- The planar deformation fixes the two constant-depth endpoint configurations. -/
theorem positiveGridRectilinearDeformation_endpoints {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (s : ℝ) :
    positiveGridRectilinearDeformation i k s 0 =
      (0, (k.val : ℂ) + (positiveGridRectilinearDepth i k : ℂ) * Complex.I) ∧
    positiveGridRectilinearDeformation i k s 1 =
      (1, ((adjacentSwap i k).val : ℂ) +
        (positiveGridRectilinearDepth i k : ℂ) * Complex.I) := by
  by_cases hk₀ : k = adjacentLower i
  · subst k
    norm_num [positiveGridRectilinearDeformation, positiveGridRectilinearHorizontal,
      positiveGridRectilinearRow, positiveGridRectilinearLowerRise,
      positiveGridRectilinearRamp, adjacentSwap.eq_def, adjacentLower, adjacentUpper]
    constructor <;> ring
  by_cases hk₁ : k = adjacentUpper i
  · subst k
    norm_num [positiveGridRectilinearDeformation, positiveGridRectilinearHorizontal,
      positiveGridRectilinearRow, (lower_ne_upper i).symm, positiveGridRectilinearUpperDrop,
      positiveGridRectilinearRamp, adjacentSwap.eq_def, adjacentLower, adjacentUpper]
    constructor <;> ring
  rw [positiveGridRectilinearDeformation_fixed i k hk₀ hk₁,
    positiveGridRectilinearDeformation_fixed i k hk₀ hk₁]
  simp [positiveGridRectilinearDepth, hk₀, hk₁, adjacentSwap.eq_def,
    Equiv.swap_apply_of_ne_of_ne hk₀ hk₁]

/-- The depth-lifting deformation records its moving endpoint configurations explicitly. -/
theorem positiveGridDepthLift_endpoints {m : ℕ}
    (i : Fin (m - 1)) (k : Fin m) (s : ℝ) :
    positiveGridDepthLift i k s 0 =
      (0, (k.val : ℂ) + ((s * positiveGridRectilinearDepth i k : ℝ) : ℂ) * Complex.I) ∧
    positiveGridDepthLift i k s 1 =
      (1, ((adjacentSwap i k).val : ℂ) +
        ((s * positiveGridRectilinearDepth i k : ℝ) : ℂ) * Complex.I) := by
  simp only [positiveGridDepthLift,
    positiveGridGeneratorDeformation_of_nonpos i _ k _ (show (0 : ℝ) ≤ 0 by rfl),
    positiveGridGeneratorDeformation_of_one_le i _ k _ (show (1 : ℝ) ≤ 1 by rfl),
    sub_sub_cancel, and_self]


/-- The three distinct vertical-move columns, in their geometric order. -/
def positiveGridRectilinearColumns : Fin 3 → ℝ := ![1 / 3, 1 / 2, 2 / 3]

/-- The three distinct horizontal levels occupied by the crossing gadget. -/
def positiveGridRectilinearRows {m : ℕ} (i : Fin (m - 1)) : Fin 3 → ℝ :=
  ![(i.val : ℝ), (i.val : ℝ) + 1 / 2, (i.val : ℝ) + 1]

/-- The six internal vertices form an actual grid marking pair. This definition
does not by itself identify the closed grid link with a closed geometric braid. -/
def positiveGridRectilinearDiagram : TauCeti.GridDiagram 3 where
  O := ⟨Equiv.swap 0 1⟩
  X := ⟨Equiv.swap 1 2⟩
  disjoint := by decide

theorem positiveGridRectilinearColumns_strictMono : StrictMono positiveGridRectilinearColumns := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num [positiveGridRectilinearColumns] at *

theorem positiveGridRectilinearRows_strictMono {m : ℕ} (i : Fin (m - 1)) :
    StrictMono (positiveGridRectilinearRows i) := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num [positiveGridRectilinearRows] at *

/-- The `X` marking is precisely the beginning of each of the three vertical moves. -/
theorem positiveGridRectilinearDiagram_X_corners {m : ℕ} (i : Fin (m - 1)) (c : Fin 3) :
    (positiveGridRectilinearColumns c,
      positiveGridRectilinearRows i (positiveGridRectilinearDiagram.X c)) =
      ![positiveGridRectilinearProjection (positiveGridRectilinearLowerCorners i 1),
        positiveGridRectilinearProjection (positiveGridRectilinearUpperCorners i 1),
        positiveGridRectilinearProjection (positiveGridRectilinearLowerCorners i 3)] c := by
  change (positiveGridRectilinearColumns c, positiveGridRectilinearRows i (Equiv.swap 1 2 c)) = _
  fin_cases c <;> norm_num [positiveGridRectilinearColumns, positiveGridRectilinearRows,
    positiveGridRectilinearLowerCorners, positiveGridRectilinearUpperCorners,
    positiveGridRectilinearProjection, Equiv.swap_apply_def, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

/-- The `O` marking is precisely the end of each of the three vertical moves. -/
theorem positiveGridRectilinearDiagram_O_corners {m : ℕ} (i : Fin (m - 1)) (c : Fin 3) :
    (positiveGridRectilinearColumns c,
      positiveGridRectilinearRows i (positiveGridRectilinearDiagram.O c)) =
      ![positiveGridRectilinearProjection (positiveGridRectilinearLowerCorners i 2),
        positiveGridRectilinearProjection (positiveGridRectilinearUpperCorners i 2),
        positiveGridRectilinearProjection (positiveGridRectilinearLowerCorners i 4)] c := by
  change (positiveGridRectilinearColumns c, positiveGridRectilinearRows i (Equiv.swap 0 1 c)) = _
  fin_cases c <;> norm_num [positiveGridRectilinearColumns, positiveGridRectilinearRows,
    positiveGridRectilinearLowerCorners, positiveGridRectilinearUpperCorners,
    positiveGridRectilinearProjection, Equiv.swap_apply_def, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

end OnLeConjecture.KnotTheory
