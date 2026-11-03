/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.PositiveBraidGridEquationScheduleIsotopy
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Smooth vertical shears for separating the horizontal rows

The base-circle coordinate and the imaginary height are unchanged. A real row
offset with Lipschitz constant at most one half gives injective differentials
and injective maps throughout the smooth interpolation. Row offsets are to be
constructed from the finite horizontal arcs, rather than assigned to corners
independently.
-/

@[expose] public noncomputable section
open Set Manifold
open scoped Topology ContDiff Manifold
open OnLeConjecture.Analytic OnLeConjecture.DifferentialTopology
attribute [local instance] finrank_real_complex_fact'

namespace OnLeConjecture.KnotTheory

/-- The Euclidean extension of the row deformation. -/
def positiveGridRowShear (q : ℂ × ℝ → ℝ) (s : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, p.2 + ((Real.smoothTransition s * q (p.1, p.2.re) : ℝ) : ℂ))

/-- The displacement changes only the real height. -/
def positiveGridRowDisplacement (q : ℂ × ℝ → ℝ) (s : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (0, ((Real.smoothTransition s * q (p.1, p.2.re) : ℝ) : ℂ))

theorem positiveGridRowShear_eq_add (q : ℂ × ℝ → ℝ) (s : ℝ) :
    positiveGridRowShear q s = fun p => p + positiveGridRowDisplacement q s p := by
  funext p
  simp [positiveGridRowShear, positiveGridRowDisplacement, Prod.add_def]

@[simp] theorem positiveGridRowShear_zero (q : ℂ × ℝ → ℝ) (p : ℂ × ℂ) :
    positiveGridRowShear q 0 p = p := by simp [positiveGridRowShear]

@[simp] theorem positiveGridRowShear_one (q : ℂ × ℝ → ℝ) (p : ℂ × ℂ) :
    positiveGridRowShear q 1 p = (p.1, p.2 + (q (p.1, p.2.re) : ℂ)) := by
  simp [positiveGridRowShear]

@[simp] theorem positiveGridRowShear_fst (q : ℂ × ℝ → ℝ) (s : ℝ) (p : ℂ × ℂ) :
    (positiveGridRowShear q s p).1 = p.1 := rfl

@[simp] theorem positiveGridRowShear_im (q : ℂ × ℝ → ℝ) (s : ℝ) (p : ℂ × ℂ) :
    (positiveGridRowShear q s p).2.im = p.2.im := by simp [positiveGridRowShear]

@[simp] theorem positiveGridRowShear_re (q : ℂ × ℝ → ℝ) (s : ℝ) (p : ℂ × ℂ) :
    (positiveGridRowShear q s p).2.re = p.2.re + Real.smoothTransition s * q (p.1, p.2.re) := by
  simp [positiveGridRowShear]

theorem positiveGridRowDisplacement_contDiff {q : ℂ × ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℂ) => positiveGridRowDisplacement q p.1 p.2) := by
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℂ) => (p.2.1, p.2.2.re)) :=
    (contDiff_fst.comp contDiff_snd).prodMk
      (Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_snd))
  exact contDiff_const.prodMk (Complex.ofRealCLM.contDiff.comp
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (hq.comp harg)))

theorem positiveGridRowShear_contDiff {q : ℂ × ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun p : ℝ × (ℂ × ℂ) => positiveGridRowShear q p.1 p.2) := by
  simp_rw [positiveGridRowShear_eq_add]
  exact contDiff_snd.add (positiveGridRowDisplacement_contDiff hq)

/-- The displacement has the same small Lipschitz bound at every interpolation time. -/
theorem positiveGridRowDisplacement_lipschitz {q : ℂ × ℝ → ℝ}
    (hq : LipschitzWith (1 / 2) q) (s : ℝ) :
    LipschitzWith (1 / 2) (positiveGridRowDisplacement q s) := by
  apply LipschitzWith.of_dist_le_mul
  intro p r
  have hσ := Real.smoothTransition.nonneg s
  have hσ' := Real.smoothTransition.le_one s
  have hqd := hq.dist_le_mul (p.1, p.2.re) (r.1, r.2.re)
  have hre : dist p.2.re r.2.re ≤ dist p.2 r.2 := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, Complex.sub_re] using
      Complex.abs_re_le_norm (p.2 - r.2)
  have hpr : dist (p.1, p.2.re) (r.1, r.2.re) ≤ dist p r := by
    simp only [Prod.dist_eq]
    exact max_le_max le_rfl hre
  have hnorm : dist (positiveGridRowDisplacement q s p) (positiveGridRowDisplacement q s r) =
      Real.smoothTransition s * dist (q (p.1, p.2.re)) (q (r.1, r.2.re)) := by
    simp [positiveGridRowDisplacement, dist_eq_norm, ← Complex.ofReal_sub,
      ← mul_sub, Real.norm_eq_abs, abs_of_nonneg hσ, mul_nonneg hσ (abs_nonneg _)]
  rw [hnorm]
  have hnon := dist_nonneg (x := q (p.1, p.2.re)) (y := q (r.1, r.2.re))
  have hle : Real.smoothTransition s * dist (q (p.1, p.2.re)) (q (r.1, r.2.re)) ≤
      dist (q (p.1, p.2.re)) (q (r.1, r.2.re)) := by nlinarith
  exact hle.trans (hqd.trans (mul_le_mul_of_nonneg_left hpr (by positivity)))

/-- Every interpolated row map is injective, with a uniform lower distance bound. -/
theorem positiveGridRowShear_injective {q : ℂ × ℝ → ℝ}
    (hq : LipschitzWith (1 / 2) q) (s : ℝ) : Function.Injective (positiveGridRowShear q s) := by
  rw [positiveGridRowShear_eq_add]
  exact (AntilipschitzWith.id.add_lipschitzWith
    (positiveGridRowDisplacement_lipschitz hq s) (by norm_num)).injective

/-- The derivative is injective because the displacement derivative has norm at most one half. -/
theorem positiveGridRowShear_fderiv_injective {q : ℂ × ℝ → ℝ}
    (hqs : ContDiff ℝ ∞ q) (hq : LipschitzWith (1 / 2) q) (s : ℝ) (p : ℂ × ℂ) :
    Function.Injective (fderiv ℝ (positiveGridRowShear q s) p) := by
  have hD : DifferentiableAt ℝ (positiveGridRowDisplacement q s) p :=
    ((positiveGridRowDisplacement_contDiff hqs).comp
      (contDiff_const (c := s) |>.prodMk contDiff_id)).differentiable (by simp) p
  have hder : fderiv ℝ (positiveGridRowShear q s) p =
      ContinuousLinearMap.id ℝ (ℂ × ℂ) + fderiv ℝ (positiveGridRowDisplacement q s) p := by
    rw [positiveGridRowShear_eq_add]
    exact ((hasFDerivAt_id p).add hD.hasFDerivAt).fderiv
  rw [hder]
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have he : v = -(fderiv ℝ (positiveGridRowDisplacement q s) p v) := by
    exact eq_neg_of_add_eq_zero_left hv
  have hb := norm_fderiv_le_of_lipschitz ℝ (x₀ := p) (positiveGridRowDisplacement_lipschitz hq s)
  have hbound := (fderiv ℝ (positiveGridRowDisplacement q s) p).le_opNorm v
  have hn : ‖v‖ ≤ (1 / 2 : ℝ) * ‖v‖ := by
    calc
      ‖v‖ = ‖fderiv ℝ (positiveGridRowDisplacement q s) p v‖ :=
        (congrArg norm he).trans (norm_neg _)
      _ ≤ ‖fderiv ℝ (positiveGridRowDisplacement q s) p‖ * ‖v‖ := hbound
      _ ≤ (1 / 2 : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  exact norm_eq_zero.mp (by linarith [norm_nonneg v])

/-- The native cylinder version has exactly the same base point and imaginary height. -/
def positiveGridRowShearCylinder (q : ℂ × ℝ → ℝ) (s : ℝ) (p : Circle × ℂ) : Circle × ℂ :=
  (p.1, (positiveGridRowShear q s ((p.1 : ℂ), p.2)).2)

/-- A prescribed row offset realizes the target row, with both other coordinates unchanged. -/
theorem positiveGridRowShearCylinder_row {q : ℂ × ℝ → ℝ} (p : Circle × ℂ) {g : ℝ}
    (hq : q ((p.1 : ℂ), p.2.re) = g - p.2.re) :
    (positiveGridRowShearCylinder q 1 p).1 = p.1 ∧
      (positiveGridRowShearCylinder q 1 p).2.re = g ∧
      (positiveGridRowShearCylinder q 1 p).2.im = p.2.im := by
  simp [positiveGridRowShearCylinder, positiveGridRowShear, hq]

theorem positiveGridRowShearCylinder_injective {q : ℂ × ℝ → ℝ}
    (hq : LipschitzWith (1 / 2) q) (s : ℝ) :
    Function.Injective (positiveGridRowShearCylinder q s) := by
  intro p r h
  have he : positiveGridRowShear q s ((p.1 : ℂ), p.2) =
      positiveGridRowShear q s ((r.1 : ℂ), r.2) := by
    apply Prod.ext
    · simpa only [positiveGridRowShearCylinder, positiveGridRowShear_fst] using
        congrArg (fun x : Circle × ℂ => (x.1 : ℂ)) h
    · exact congrArg (fun x : Circle × ℂ => x.2) h
  have hh := positiveGridRowShear_injective hq s he
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun x : ℂ × ℂ => x.2) hh)

end OnLeConjecture.KnotTheory
