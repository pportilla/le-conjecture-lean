/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyRootGrid
public import OnLeConjecture.Analytic.WindingNumberArgument

/-!
# Rectangle boundaries and circles

The local factors and the outer braid of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`) are computed over circles, while the cut system of
`BraidMonodromyRootGrid.lean` uses the boundaries of the rectangles of a grid. This module
compares the two by explicit straight-line homotopies.

* `rectLoop x₀ x₁ y₀ y₁`: the boundary of the rectangle `[x₀, x₁] × [y₀, y₁]`, counterclockwise
  from its lower left corner. The boundary of a grid cell and of the grid rectangle are of this
  form (`cellBoundary_eq_rectLoop`, `outerLoop_eq_rectLoop`).
* `rectCircleHomotopy c r R t`: the straight-line homotopy between the circle
  `c + r e^{iθ}`, `θ = -3π/4 + 2π t`, and the rectangle boundary at the time `4 t`. The angle
  `θ` is a corner angle at the times `t = 0, 1/4, 1/2, 3/4, 1`.
* `IsRootFamily.signedBraidConj_rectLoop_circle_of_mapsTo`: if this homotopy stays in the base of
  a root family, the root path words of the rectangle boundary on `[0, 4]` and of the circle on
  `[-3π/4, 5π/4]` are conjugate.
* `IsRootFamily.signedBraidConj_rectLoop_circle_inner`: the hypothesis holds for a rectangle
  containing `c` in its interior, contained in a ball `B(c, R)` with `B(c, R) \ {c} ⊆ U`, and every
  radius `0 < r < R`; the homotopy avoids `c` because on each side the rectangle point and the
  circle point lie strictly on the same side of `c`.
* `IsRootFamily.signedBraidConj_rectLoop_circle_outer`: the hypothesis holds for a rectangle in
  the square `[-ρ √2/2, ρ √2/2]²` and the circle of radius `ρ` around `0`, when the closed disc of
  radius `ρ` minus the open rectangle lies in `U`.
-/

@[expose] public noncomputable section

open Set Function Real

namespace OnLeConjecture.Analytic

open KnotTheory SignedAdjacentWord

variable {S : ℕ} {Z : ℂ → Set ℂ} {U : Set ℂ}

/-! ### Rectangle boundaries -/

/-- The boundary of the rectangle `[x₀, x₁] × [y₀, y₁]`, counterclockwise from `(x₀, y₀)`. -/
def rectLoop (x₀ x₁ y₀ y₁ : ℝ) : ℕ → ℂ :=
  quadLoop ⟨x₀, y₀⟩ ⟨x₁, y₀⟩ ⟨x₁, y₁⟩ ⟨x₀, y₁⟩

theorem cellBoundary_eq_rectLoop (xs ys : ℕ → ℝ) (a b : ℕ) :
    cellBoundary xs ys a b = rectLoop (xs a) (xs (a + 1)) (ys b) (ys (b + 1)) := rfl

theorem outerLoop_eq_rectLoop (xs ys : ℕ → ℝ) (n : ℕ) :
    outerLoop xs ys n = rectLoop (xs 0) (xs n) (ys 0) (ys n) := rfl

section Sides

variable {x₀ x₁ y₀ y₁ : ℝ}

theorem polygonPath_rectLoop_side0 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    polygonPath (rectLoop x₀ x₁ y₀ y₁) t = ⟨x₀ + t * (x₁ - x₀), y₀⟩ := by
  rw [polygonPath_eq _ 0 (by simpa using ht)]
  apply Complex.ext <;> simp [rectLoop, quadLoop, segmentPath]

theorem polygonPath_rectLoop_side1 {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    polygonPath (rectLoop x₀ x₁ y₀ y₁) t = ⟨x₁, y₀ + (t - 1) * (y₁ - y₀)⟩ := by
  rw [polygonPath_eq _ 1 (by norm_num; exact ht)]
  apply Complex.ext <;> simp [rectLoop, quadLoop, segmentPath]

theorem polygonPath_rectLoop_side2 {t : ℝ} (ht : t ∈ Icc (2 : ℝ) 3) :
    polygonPath (rectLoop x₀ x₁ y₀ y₁) t = ⟨x₁ + (t - 2) * (x₀ - x₁), y₁⟩ := by
  rw [polygonPath_eq _ 2 (by norm_num; exact ht)]
  apply Complex.ext <;> simp [rectLoop, quadLoop, segmentPath]

theorem polygonPath_rectLoop_side3 {t : ℝ} (ht : t ∈ Icc (3 : ℝ) 4) :
    polygonPath (rectLoop x₀ x₁ y₀ y₁) t = ⟨x₀, y₁ + (t - 3) * (y₀ - y₁)⟩ := by
  rw [polygonPath_eq _ 3 (by norm_num; exact ht)]
  apply Complex.ext <;> simp [rectLoop, quadLoop, segmentPath]

theorem polygonPath_rectLoop_zero : polygonPath (rectLoop x₀ x₁ y₀ y₁) 0 = ⟨x₀, y₀⟩ := by
  rw [polygonPath_rectLoop_side0 ⟨le_rfl, zero_le_one⟩]; simp

theorem polygonPath_rectLoop_four : polygonPath (rectLoop x₀ x₁ y₀ y₁) 4 = ⟨x₀, y₀⟩ := by
  rw [polygonPath_rectLoop_side3 ⟨by norm_num, le_rfl⟩]; apply Complex.ext <;> simp; ring

/-- The boundary of the rectangle lies in the closed rectangle. -/
theorem polygonPath_rectLoop_mem (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 4) :
    (polygonPath (rectLoop x₀ x₁ y₀ y₁) t).re ∈ Icc x₀ x₁ ∧
      (polygonPath (rectLoop x₀ x₁ y₀ y₁) t).im ∈ Icc y₀ y₁ := by
  rcases le_or_gt t 1 with h1 | h1
  · rw [polygonPath_rectLoop_side0 ⟨ht.1, h1⟩]
    exact ⟨⟨by nlinarith [ht.1], by nlinarith [ht.1]⟩, ⟨le_rfl, hy⟩⟩
  rcases le_or_gt t 2 with h2 | h2
  · rw [polygonPath_rectLoop_side1 ⟨h1.le, h2⟩]
    exact ⟨⟨hx, le_rfl⟩, ⟨by nlinarith, by nlinarith⟩⟩
  rcases le_or_gt t 3 with h3 | h3
  · rw [polygonPath_rectLoop_side2 ⟨h2.le, h3⟩]
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨hy, le_rfl⟩⟩
  · rw [polygonPath_rectLoop_side3 ⟨h3.le, ht.2⟩]
    exact ⟨⟨le_rfl, hx⟩, ⟨by nlinarith [ht.2], by nlinarith [ht.2]⟩⟩

end Sides

/-! ### Corner angles -/

/-- The angle of the circle at the time `t`: `-3π/4 + 2π t`. -/
def rectAngle (t : ℝ) : ℝ := -(3 * π / 4) + 2 * π * t

theorem sqrt_two_div_two_le_cos {φ : ℝ} (hφ : φ ∈ Icc (-(π / 4)) (π / 4)) :
    √2 / 2 ≤ Real.cos φ := by
  rw [← Real.cos_abs, ← Real.cos_pi_div_four]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) (by linarith [Real.pi_pos]) ?_
  exact abs_le.mpr ⟨hφ.1, hφ.2⟩

theorem sqrt_two_div_two_pos : 0 < √2 / 2 := by positivity

theorem rectAngle_side0 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 4)) :
    Real.sin (rectAngle t) ≤ -(√2 / 2) := by
  have : Real.sin (rectAngle t) = -Real.cos (rectAngle t + π / 2) := by
    rw [← Real.sin_sub_pi_div_two]; ring_nf
  rw [this, neg_le_neg_iff]
  exact sqrt_two_div_two_le_cos ⟨by unfold rectAngle; nlinarith [Real.pi_pos, ht.1],
    by unfold rectAngle; nlinarith [Real.pi_pos, ht.2]⟩

theorem rectAngle_side1 {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (1 / 2)) :
    √2 / 2 ≤ Real.cos (rectAngle t) :=
  sqrt_two_div_two_le_cos ⟨by unfold rectAngle; nlinarith [Real.pi_pos, ht.1],
    by unfold rectAngle; nlinarith [Real.pi_pos, ht.2]⟩

theorem rectAngle_side2 {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) (3 / 4)) :
    √2 / 2 ≤ Real.sin (rectAngle t) := by
  have : Real.sin (rectAngle t) = Real.cos (rectAngle t - π / 2) := by
    rw [← Real.sin_add_pi_div_two]; ring_nf
  rw [this]
  exact sqrt_two_div_two_le_cos ⟨by unfold rectAngle; nlinarith [Real.pi_pos, ht.1],
    by unfold rectAngle; nlinarith [Real.pi_pos, ht.2]⟩

theorem rectAngle_side3 {t : ℝ} (ht : t ∈ Icc (3 / 4 : ℝ) 1) :
    Real.cos (rectAngle t) ≤ -(√2 / 2) := by
  have : Real.cos (rectAngle t) = -Real.cos (rectAngle t - π) := by
    rw [← Real.cos_add_pi]; ring_nf
  rw [this, neg_le_neg_iff]
  exact sqrt_two_div_two_le_cos ⟨by unfold rectAngle; nlinarith [Real.pi_pos, ht.1],
    by unfold rectAngle; nlinarith [Real.pi_pos, ht.2]⟩

theorem circlePath_re (r θ : ℝ) : (circlePath r θ).re = r * Real.cos θ := by
  simp [circlePath, Complex.exp_ofReal_mul_I_re]

theorem circlePath_im (r θ : ℝ) : (circlePath r θ).im = r * Real.sin θ := by
  simp [circlePath, Complex.exp_ofReal_mul_I_im]

theorem circlePath_rectAngle_one (r : ℝ) :
    circlePath r (rectAngle 1) = circlePath r (rectAngle 0) := by
  have : rectAngle 1 = rectAngle 0 + 2 * π := by unfold rectAngle; ring
  rw [this]
  simp only [circlePath]
  congr 1
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]
  have : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show (((2 * π : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  rw [this, mul_one]

/-! ### The straight-line homotopy -/

/-- The straight-line homotopy from the circle `c + r e^{i θ(t)}` (at `s = 0`) to the rectangle
boundary at the time `4 t` (at `s = 1`). -/
def rectCircleHomotopy (x₀ x₁ y₀ y₁ : ℝ) (c : ℂ) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  (1 - (p.1 : ℂ)) * (c + circlePath r (rectAngle p.2)) +
    (p.1 : ℂ) * polygonPath (rectLoop x₀ x₁ y₀ y₁) (4 * p.2)

theorem continuousOn_rectCircleHomotopy (x₀ x₁ y₀ y₁ : ℝ) (c : ℂ) (r : ℝ) :
    ContinuousOn (rectCircleHomotopy x₀ x₁ y₀ y₁ c r) (Icc 0 1 ×ˢ Icc 0 1) := by
  have hpoly : ContinuousOn (fun p : ℝ × ℝ => polygonPath (rectLoop x₀ x₁ y₀ y₁) (4 * p.2))
      (Icc 0 1 ×ˢ Icc 0 1) := by
    refine (continuousOn_polygonPath (rectLoop x₀ x₁ y₀ y₁) 4).comp (by fun_prop) ?_
    intro p hp
    exact ⟨by nlinarith [hp.2.1], by push_cast; nlinarith [hp.2.2]⟩
  have hcirc : Continuous fun p : ℝ × ℝ => c + circlePath r (rectAngle p.2) := by
    have := continuous_circlePath r
    unfold rectAngle
    fun_prop
  unfold rectCircleHomotopy
  exact ((by fun_prop : Continuous fun p : ℝ × ℝ => (1 - (p.1 : ℂ))).continuousOn.mul
    hcirc.continuousOn).add ((by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ)).continuousOn.mul
    hpoly)

theorem rectCircleHomotopy_re (x₀ x₁ y₀ y₁ : ℝ) (c : ℂ) (r : ℝ) (p : ℝ × ℝ) :
    (rectCircleHomotopy x₀ x₁ y₀ y₁ c r p).re =
      (1 - p.1) * (c.re + r * Real.cos (rectAngle p.2)) +
        p.1 * (polygonPath (rectLoop x₀ x₁ y₀ y₁) (4 * p.2)).re := by
  simp [rectCircleHomotopy, circlePath_re]

theorem rectCircleHomotopy_im (x₀ x₁ y₀ y₁ : ℝ) (c : ℂ) (r : ℝ) (p : ℝ × ℝ) :
    (rectCircleHomotopy x₀ x₁ y₀ y₁ c r p).im =
      (1 - p.1) * (c.im + r * Real.sin (rectAngle p.2)) +
        p.1 * (polygonPath (rectLoop x₀ x₁ y₀ y₁) (4 * p.2)).im := by
  simp [rectCircleHomotopy, circlePath_im]

/-- **Rectangle boundaries and circles.** If the straight-line homotopy between the circle
`c + r e^{iθ}` and the boundary of the rectangle stays in `U`, the root path words of the
rectangle boundary on `[0, 4]` and of the circle on `[-3π/4, 5π/4]` are conjugate. -/
theorem IsRootFamily.signedBraidConj_rectLoop_circle_of_mapsTo (hZ : IsRootFamily Z S U)
    {x₀ x₁ y₀ y₁ : ℝ} {c : ℂ} {r : ℝ}
    (hmaps : MapsTo (rectCircleHomotopy x₀ x₁ y₀ y₁ c r) (Icc 0 1 ×ˢ Icc 0 1) U)
    {W W' : SignedAdjacentWord S}
    (hW : IsRootPathWord Z (polygonPath (rectLoop x₀ x₁ y₀ y₁)) 0 4 W)
    (hW' : IsRootPathWord Z (fun θ => c + circlePath r θ) (rectAngle 0) (rectAngle 1) W') :
    SignedBraidConj W W' := by
  set P := rectCircleHomotopy x₀ x₁ y₀ y₁ c r with hP
  have hPc := continuousOn_rectCircleHomotopy x₀ x₁ y₀ y₁ c r
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- The bottom side is the circle.
  have hb : IsRootPathWord Z (fun t => P (0, t)) 0 1 W' := by
    have h := IsRootPathWord.comp_affine (φ := rectAngle) (α := 2 * π)
      (β := -(3 * π / 4)) (by positivity) (fun t => by unfold rectAngle; ring) hW'
    refine h.of_eqOn fun t _ => ?_
    simp [hP, rectCircleHomotopy]
  -- The top side is the rectangle boundary.
  have ht : IsRootPathWord Z (fun t => P (1, t)) 0 1 W := by
    have h := IsRootPathWord.comp_affine (u := 0) (v := 1) (φ := fun t => 4 * t) (α := 4)
      (β := 0) (by norm_num) (fun t => by ring) (by simpa using hW)
    refine h.of_eqOn fun t _ => ?_
    simp [hP, rectCircleHomotopy]
  -- The two vertical sides coincide.
  have hside : ∀ s, P (s, 0) = P (s, 1) := fun s => by
    simp only [hP, rectCircleHomotopy, mul_zero, mul_one, polygonPath_rectLoop_zero,
      polygonPath_rectLoop_four, circlePath_rectAngle_one]
  have hlU : MapsTo (fun s => P (s, 0)) (Icc 0 1) U := fun s hs => hmaps ⟨hs, hI0⟩
  obtain ⟨L, hl⟩ := hZ.exists_isRootPathWord zero_lt_one
    (hPc.comp (by fun_prop) fun s hs => ⟨hs, hI0⟩) hlU
  have hr : IsRootPathWord Z (fun s => P (s, 1)) 0 1 L := hl.of_eqOn fun s _ => hside s
  have hrel := hZ.square_relation hPc hmaps hb ht hl hr
  exact (SignedBraidConj.of_equiv_conjugate hrel).symm

theorem rectAngle_lt : rectAngle 0 < rectAngle 1 := by
  unfold rectAngle; nlinarith [Real.pi_pos]

/-! ### The two cases -/

theorem comb_neg {s A B : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hA : A < 0) (hB : B < 0) :
    (1 - s) * A + s * B < 0 := by
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; linarith
  · nlinarith [mul_pos h (neg_pos.mpr hB), mul_nonneg (sub_nonneg.mpr hs1) (neg_nonneg.mpr hA.le)]

theorem comb_le {s a b y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : a ≤ y) (hb : b ≤ y) :
    (1 - s) * a + s * b ≤ y := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ha),
    mul_nonneg hs0 (sub_nonneg.mpr hb)]

theorem comb_ge {s a b y : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : y ≤ a) (hb : y ≤ b) :
    y ≤ (1 - s) * a + s * b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ha),
    mul_nonneg hs0 (sub_nonneg.mpr hb)]

/-- A convex combination of two points of a ball lies in the ball. -/
theorem convex_comb_mem_ball {a b c : ℂ} {R : ℝ} (ha : a ∈ Metric.ball c R)
    (hb : b ∈ Metric.ball c R) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 - (s : ℂ)) * a + (s : ℂ) * b ∈ Metric.ball c R := by
  have h := (convex_ball c R).add_smul_mem ha (show a + (b - a) ∈ Metric.ball c R by simpa using hb)
    hs
  convert h using 1
  simp only [Complex.real_smul]
  ring

/-- **The inner case.** For a rectangle containing `c` in its interior, contained in a ball
`B(c, R)` with `B(c, R) \ {c} ⊆ U`, and a radius `0 < r < R`, the root path words of the rectangle
boundary and of the circle `c + r e^{iθ}` are conjugate. -/
theorem IsRootFamily.signedBraidConj_rectLoop_circle_inner (hZ : IsRootFamily Z S U)
    {x₀ x₁ y₀ y₁ : ℝ} {c : ℂ} (hx₀ : x₀ < c.re) (hx₁ : c.re < x₁) (hy₀ : y₀ < c.im)
    (hy₁ : c.im < y₁) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrect : ∀ z : ℂ, z.re ∈ Icc x₀ x₁ → z.im ∈ Icc y₀ y₁ → z ∈ Metric.ball c R)
    (hU : Metric.ball c R \ {c} ⊆ U) {W W' : SignedAdjacentWord S}
    (hW : IsRootPathWord Z (polygonPath (rectLoop x₀ x₁ y₀ y₁)) 0 4 W)
    (hW' : IsRootPathWord Z (fun θ => c + circlePath r θ) (rectAngle 0) (rectAngle 1) W') :
    SignedBraidConj W W' := by
  refine hZ.signedBraidConj_rectLoop_circle_of_mapsTo (fun p hp => hU ⟨?_, ?_⟩) hW hW'
  · refine convex_comb_mem_ball ?_ ?_ hp.1
    · simpa [dist_eq_norm, norm_circlePath hr.le] using hrR
    · obtain ⟨h1, h2⟩ := polygonPath_rectLoop_mem (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (by linarith) (by linarith) (t := 4 * p.2) ⟨by nlinarith [hp.2.1], by nlinarith [hp.2.2]⟩
      exact hrect _ h1 h2
  · intro heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    rw [rectCircleHomotopy_re] at hre
    rw [rectCircleHomotopy_im] at him
    obtain ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩ := hp
    set s := p.1
    set t := p.2
    have hpos := sqrt_two_div_two_pos
    rcases le_or_gt t (1 / 4) with h1 | h1
    · have hpoly := polygonPath_rectLoop_side0 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hsin := rectAngle_side0 ⟨ht0, h1⟩
      rw [hpoly] at him
      simp only at him
      have e : (1 - s) * (r * Real.sin (rectAngle t)) + s * (y₀ - c.im) = 0 := by
        linear_combination him
      exact (comb_neg hs0 hs1 (mul_neg_of_pos_of_neg hr (by linarith)) (by linarith)).ne e
    rcases le_or_gt t (1 / 2) with h2 | h2
    · have hpoly := polygonPath_rectLoop_side1 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hcos := rectAngle_side1 ⟨h1.le, h2⟩
      rw [hpoly] at hre
      simp only at hre
      have e : (1 - s) * (-(r * Real.cos (rectAngle t))) + s * (c.re - x₁) = 0 := by
        linear_combination -hre
      exact (comb_neg hs0 hs1 (neg_neg_of_pos (mul_pos hr (by linarith))) (by linarith)).ne e
    rcases le_or_gt t (3 / 4) with h3 | h3
    · have hpoly := polygonPath_rectLoop_side2 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hsin := rectAngle_side2 ⟨h2.le, h3⟩
      rw [hpoly] at him
      simp only at him
      have e : (1 - s) * (-(r * Real.sin (rectAngle t))) + s * (c.im - y₁) = 0 := by
        linear_combination -him
      exact (comb_neg hs0 hs1 (neg_neg_of_pos (mul_pos hr (by linarith))) (by linarith)).ne e
    · have hpoly := polygonPath_rectLoop_side3 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hcos := rectAngle_side3 ⟨h3.le, ht1⟩
      rw [hpoly] at hre
      simp only at hre
      have e : (1 - s) * (r * Real.cos (rectAngle t)) + s * (x₀ - c.re) = 0 := by
        linear_combination hre
      exact (comb_neg hs0 hs1 (mul_neg_of_pos_of_neg hr (by linarith)) (by linarith)).ne e

/-- **The outer case.** For a rectangle in the square `[-ρ √2/2, ρ √2/2]²`, if the closed disc
of radius `ρ` around `0` minus the open rectangle lies in `U`, the root path words of the
rectangle boundary and of the circle of radius `ρ` are conjugate. -/
theorem IsRootFamily.signedBraidConj_rectLoop_circle_outer (hZ : IsRootFamily Z S U)
    {x₀ x₁ y₀ y₁ ρ : ℝ} (hρ : 0 < ρ) (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hx₀ : -(ρ * (√2 / 2)) ≤ x₀) (hx₁ : x₁ ≤ ρ * (√2 / 2)) (hy₀ : -(ρ * (√2 / 2)) ≤ y₀)
    (hy₁ : y₁ ≤ ρ * (√2 / 2))
    (hU : ∀ z ∈ Metric.closedBall (0 : ℂ) ρ, ¬ (z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁) → z ∈ U)
    {W W' : SignedAdjacentWord S}
    (hW : IsRootPathWord Z (polygonPath (rectLoop x₀ x₁ y₀ y₁)) 0 4 W)
    (hW' : IsRootPathWord Z (fun θ => 0 + circlePath ρ θ) (rectAngle 0) (rectAngle 1) W') :
    SignedBraidConj W W' := by
  refine hZ.signedBraidConj_rectLoop_circle_of_mapsTo (fun p hp => hU _ ?_ ?_) hW hW'
  · -- The homotopy stays in the closed disc.
    have h2 : (√2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have hc : ‖0 + circlePath ρ (rectAngle p.2)‖ ≤ ρ := by
      rw [zero_add, norm_circlePath hρ.le]
    obtain ⟨hre, him⟩ := polygonPath_rectLoop_mem (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
      hx hy (t := 4 * p.2) ⟨by nlinarith [hp.2.1], by nlinarith [hp.2.2]⟩
    set q := polygonPath (rectLoop x₀ x₁ y₀ y₁) (4 * p.2)
    have hq : ‖q‖ ≤ ρ := by
      have hsq : ‖q‖ ^ 2 ≤ ρ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        have hb : (ρ * (√2 / 2)) * (ρ * (√2 / 2)) = ρ ^ 2 / 2 := by
          have : (ρ * (√2 / 2)) * (ρ * (√2 / 2)) = ρ ^ 2 * (√2 / 2) ^ 2 := by ring
          rw [this, h2]; ring
        have h1 : q.re * q.re ≤ ρ ^ 2 / 2 := by
          rw [← hb, ← abs_mul_abs_self q.re]
          exact mul_self_le_mul_self (abs_nonneg _)
            (abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩)
        have h3 : q.im * q.im ≤ ρ ^ 2 / 2 := by
          rw [← hb, ← abs_mul_abs_self q.im]
          exact mul_self_le_mul_self (abs_nonneg _)
            (abs_le.mpr ⟨by linarith [him.1], by linarith [him.2]⟩)
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ.le two_ne_zero).mp hsq
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖rectCircleHomotopy x₀ x₁ y₀ y₁ 0 ρ p‖
        ≤ ‖(1 - (p.1 : ℂ)) * (0 + circlePath ρ (rectAngle p.2))‖ + ‖(p.1 : ℂ) * q‖ :=
          norm_add_le _ _
      _ = (1 - p.1) * ‖0 + circlePath ρ (rectAngle p.2)‖ + p.1 * ‖q‖ := by
          rw [norm_mul, norm_mul, show (1 - (p.1 : ℂ)) = ((1 - p.1 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by linarith [hp.1.2]),
            Real.norm_of_nonneg hp.1.1]
      _ ≤ (1 - p.1) * ρ + p.1 * ρ := by
          gcongr
          · linarith [hp.1.2]
          · exact hp.1.1
      _ = ρ := by ring
  · -- The homotopy avoids the open rectangle.
    rintro ⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩
    rw [rectCircleHomotopy_re] at hre0 hre1
    rw [rectCircleHomotopy_im] at him0 him1
    obtain ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩ := hp
    set s := p.1
    set t := p.2
    simp only [Complex.zero_re, Complex.zero_im, zero_add] at hre0 hre1 him0 him1
    rcases le_or_gt t (1 / 4) with h1 | h1
    · have hpoly := polygonPath_rectLoop_side0 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hsin := rectAngle_side0 ⟨ht0, h1⟩
      rw [hpoly] at him0
      simp only at him0
      have ha : ρ * Real.sin (rectAngle t) ≤ y₀ := by
        nlinarith [mul_le_mul_of_nonneg_left hsin hρ.le]
      linarith [comb_le hs0 hs1 ha (le_refl y₀)]
    rcases le_or_gt t (1 / 2) with h2 | h2
    · have hpoly := polygonPath_rectLoop_side1 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hcos := rectAngle_side1 ⟨h1.le, h2⟩
      rw [hpoly] at hre1
      simp only at hre1
      have ha : x₁ ≤ ρ * Real.cos (rectAngle t) := by
        nlinarith [mul_le_mul_of_nonneg_left hcos hρ.le]
      linarith [comb_ge hs0 hs1 ha (le_refl x₁)]
    rcases le_or_gt t (3 / 4) with h3 | h3
    · have hpoly := polygonPath_rectLoop_side2 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hsin := rectAngle_side2 ⟨h2.le, h3⟩
      rw [hpoly] at him1
      simp only at him1
      have ha : y₁ ≤ ρ * Real.sin (rectAngle t) := by
        nlinarith [mul_le_mul_of_nonneg_left hsin hρ.le]
      linarith [comb_ge hs0 hs1 ha (le_refl y₁)]
    · have hpoly := polygonPath_rectLoop_side3 (x₀ := x₀) (x₁ := x₁) (y₀ := y₀) (y₁ := y₁)
        (t := 4 * t) ⟨by linarith, by linarith⟩
      have hcos := rectAngle_side3 ⟨h3.le, ht1⟩
      rw [hpoly] at hre0
      simp only at hre0
      have ha : ρ * Real.cos (rectAngle t) ≤ x₀ := by
        nlinarith [mul_le_mul_of_nonneg_left hcos hρ.le]
      linarith [comb_le hs0 hs1 ha (le_refl x₀)]

end OnLeConjecture.Analytic
