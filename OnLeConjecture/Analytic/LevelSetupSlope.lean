/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupChoice

/-!
# The radii of a slope projection

For a slope `t` and a radius `R`, write `h_t = slopeBase t` (so `h_t y = y₂ - t y₁`) and
`ζ₀ = slopeFibre 1`. `CentralProps A R t` collects the properties of the central curve supplied by
`exists_central_unramified`: `H` is analytic on `B̄_R` and injective on `B_R`, the origin is the
only common zero of `v` and `h_t ∘ H` on `B̄_R`, and the central curve is unramified over
`h_t ∘ H ≠ 0` in `B_R`.

`SlopeChoice A R t` collects the radii chosen for this projection before the level: the disc
radius `ρ`, the margin `μ > ρ` on the sphere, the central disc `δ > ρ`, the level disc `η` over
which the annulus `ρ/4 ≤ |h| ≤ ρ` is unramified, the separation `κ` of the roots over the
boundary of the square `[-ρ/3, ρ/3]²` for the levels `|v| ≤ η/2`, the radius of small roots, and
a radius of points over `|h| < ρ`. `exists_slopeChoice` constructs these data from
`CentralProps` (`LevelSetupChoice.lean`).

`SlopeChoice.eventually_good`: every sufficiently small nonzero level `s` is admissible for these
data: it is small compared with `η` and with the radius of small roots, and the singular points
of the level `s` of radius `R` lie over `|h| < ρ`. The last condition is the step "by choosing an
allowed nonzero level sufficiently small, all of the singular points listed in that level lie in
`B_R` and satisfy `|h₀| < ρ/4`" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`). It uses that the number of singular points does not depend
on the radius.
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The properties of the central curve for the slope `t` on the ball of radius `R`. -/
def CentralProps (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (t : ℂ) : Prop :=
  (∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x) ∧
    InjOn A.H (ball (0 : Source 2) R) ∧
    (∀ x ∈ closedBall (0 : Source 2) R, A.H x 0 = 0 → slopeBase t (A.H x) = 0 → x = 0) ∧
    ∀ x ∈ ball (0 : Source 2) R, A.H x 0 = 0 → slopeBase t (A.H x) ≠ 0 →
      Injective (fderiv ℂ (levelBaseMap A (slopeBase t)) x)

/-- The radii chosen for the slope `t` on the ball of radius `R`, before the level. -/
structure SlopeChoice (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (t : ℂ) where
  /-- The disc radius `ρ`. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- The margin `μ` on the sphere. -/
  margin : ℝ
  radius_lt_margin : radius < margin
  sphere : ∀ x : Source 2, ‖x‖ = R → margin ≤ max ‖A.H x 0‖ ‖slopeBase t (A.H x)‖
  /-- The central disc `δ`. -/
  centralDisc : ℝ
  radius_lt_centralDisc : radius < centralDisc
  central_boundary : ∀ x : Source 2, ‖x‖ = R → A.H x 0 = 0 →
    centralDisc ≤ ‖slopeBase t (A.H x)‖
  /-- The level disc `η`. -/
  levelDisc : ℝ
  levelDisc_pos : 0 < levelDisc
  levelDisc_le : levelDisc ≤ margin
  annulus : ∀ x ∈ ball (0 : Source 2) R, ‖A.H x 0‖ < levelDisc →
    radius / 4 ≤ ‖slopeBase t (A.H x)‖ → ‖slopeBase t (A.H x)‖ ≤ radius →
    Injective (fderiv ℂ (levelBaseMap A (slopeBase t)) x)
  /-- The separation `κ` of the roots over the boundary of the square. -/
  sep : ℝ
  sep_pos : 0 < sep
  separation : ∀ (s c : ℂ), ‖s‖ ≤ levelDisc / 2 → squareNorm c = radius / 3 →
    ∀ x ∈ ball (0 : Source 2) R, ∀ y ∈ ball (0 : Source 2) R,
      levelBaseMap A (slopeBase t) x = (s, c) → levelBaseMap A (slopeBase t) y = (s, c) →
      x ≠ y → sep ≤ ‖slopeFibre 1 (A.H x) - slopeFibre 1 (A.H y)‖
  /-- The radius of small roots. -/
  small : ℝ
  small_pos : 0 < small
  small_roots : ∀ x ∈ closedBall (0 : Source 2) R, ‖A.H x 0‖ < small →
    ‖slopeBase t (A.H x)‖ < small → ‖slopeFibre 1 (A.H x)‖ < sep / 2
  /-- A radius of points over `|h| < ρ`. -/
  pointRadius : ℝ
  pointRadius_pos : 0 < pointRadius
  point_small : ∀ x ∈ ball (0 : Source 2) pointRadius, ‖slopeBase t (A.H x)‖ < radius

/-- The square of half side `ρ/3` is inside the disc of radius `ρ`, with its boundary in the
annulus `ρ/4 ≤ |c| ≤ ρ`. -/
theorem norm_le_of_squareNorm_eq {a : ℝ} {c : ℂ} (hc : squareNorm c = a) : ‖c‖ ≤ √2 * a :=
  norm_le_of_mem_baseSquare (by
    have h := hc.le
    simp only [squareNorm, max_le_iff, abs_le] at h
    exact ⟨⟨h.1.1, h.1.2⟩, h.2.1, h.2.2⟩)

theorem sqrt_two_div_three_lt_one : √2 / 3 < 1 := by
  have h : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- **The radii of a slope projection.** -/
theorem exists_slopeChoice (A : ResolutionSectionAssembly g hd hi) {R : ℝ} (hR : 0 < R) {t : ℂ}
    (hC : CentralProps A R t) : Nonempty (SlopeChoice A R t) := by
  obtain ⟨han, hinj, hiso, hunr⟩ := hC
  set h := slopeBase t with hhdef
  have hHc : ContinuousOn A.H (closedBall 0 R) := fun x hx =>
    (han x hx).continuousAt.continuousWithinAt
  -- the central disc
  obtain ⟨δ, hδ, hδK⟩ := exists_pos_le_norm_baseCoord A hR hHc hiso
  have hbd : ∀ x : Source 2, ‖x‖ = R → A.H x 0 = 0 → δ ≤ ‖h (A.H x)‖ := fun x hx hx0 =>
    hδK x (mem_closedBall_zero_iff.mpr hx.le) hx0 hx.ge
  -- the margin on the sphere
  obtain ⟨μ, hμ, hμS⟩ := exists_sphere_margin A hR han hiso
  set ρ := min μ δ / 2 with hρdef
  have hρpos : 0 < ρ := half_pos (lt_min hμ hδ)
  have hρμ : ρ < μ := lt_of_lt_of_le (half_lt_self (lt_min hμ hδ)) (min_le_left _ _)
  have hρδ : ρ < δ := lt_of_lt_of_le (half_lt_self (lt_min hμ hδ)) (min_le_right _ _)
  -- the unramified annulus
  obtain ⟨ε, hε, hεreg⟩ := exists_annulus_regular A han hbd hunr (by positivity : 0 < ρ / 4) hρδ
  set η := min ε μ with hηdef
  have hηpos : 0 < η := lt_min hε hμ
  -- the separation of the roots over the boundary of the square
  set T : Set (ℂ × ℂ) := closedBall (0 : ℂ) (η / 2) ×ˢ {c | squareNorm c = ρ / 3} with hTdef
  have hTc : IsCompact T := by
    refine (isCompact_closedBall _ _).prod ?_
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq continuous_squareNorm continuous_const) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * (ρ / 3))).subset fun c hc => ?_
    rw [mem_closedBall_zero_iff]
    have := norm_le_two_mul_squareNorm c
    rw [show squareNorm c = ρ / 3 from hc] at this
    exact this
  have hcbound : ∀ c : ℂ, squareNorm c = ρ / 3 → ρ / 4 ≤ ‖c‖ ∧ ‖c‖ ≤ ρ := by
    intro c hc
    refine ⟨?_, ?_⟩
    · have := squareNorm_le_norm c
      rw [hc] at this
      linarith
    · have h1 := norm_le_of_squareNorm_eq hc
      have h2 := sqrt_two_div_three_lt_one
      calc ‖c‖ ≤ √2 * (ρ / 3) := h1
        _ = √2 / 3 * ρ := by ring
        _ ≤ 1 * ρ := by gcongr
        _ = ρ := one_mul ρ
  have hprop : ∀ p ∈ T, ∀ x ∈ closedBall (0 : Source 2) R, levelBaseMap A h x = p →
      x ∈ ball (0 : Source 2) R := by
    rintro ⟨s, c⟩ ⟨hs, hc⟩ x hx hxp
    simp only [levelBaseMap, Prod.mk.injEq] at hxp
    rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    · exfalso
      have h1 := hμS x heq
      rw [hxp.1, hxp.2] at h1
      have h2 : ‖s‖ < μ := by
        have := mem_closedBall_zero_iff.mp hs
        linarith [min_le_right ε μ]
      have h3 : ‖c‖ < μ := ((hcbound c hc).2).trans_lt hρμ
      exact absurd h1 (not_le.mpr (max_lt h2 h3))
  have hreg : ∀ p ∈ T, ∀ x ∈ ball (0 : Source 2) R, levelBaseMap A h x = p →
      Injective (fderiv ℂ (levelBaseMap A h) x) := by
    rintro ⟨s, c⟩ ⟨hs, hc⟩ x hx hxp
    simp only [levelBaseMap, Prod.mk.injEq] at hxp
    refine hεreg x hx ?_ ?_ ?_
    · rw [hxp.1]
      have := mem_closedBall_zero_iff.mp hs
      linarith [min_le_left ε μ]
    · rw [hxp.2]
      exact (hcbound c hc).1
    · rw [hxp.2]
      exact (hcbound c hc).2
  obtain ⟨κ, hκ, hκsep⟩ := exists_separation A (slope_coordinates t one_ne_zero) han hinj hTc
    hprop hreg
  -- small roots
  obtain ⟨m, hm, hmsmall⟩ := exists_small_roots A (ζ := slopeFibre 1) han hiso hκ
  -- points over `|h| < ρ`
  have hcont : ContinuousAt (fun x => h (A.H x)) 0 :=
    h.continuous.continuousAt.comp A.H_analytic.continuousAt
  have h0 : h (A.H 0) = 0 := by rw [A.H_zero, map_zero]
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.eventually (ball_mem_nhds (h (A.H 0)) hρpos))
  refine ⟨{
      radius := ρ
      radius_pos := hρpos
      margin := μ
      radius_lt_margin := hρμ
      sphere := hμS
      centralDisc := δ
      radius_lt_centralDisc := hρδ
      central_boundary := hbd
      levelDisc := η
      levelDisc_pos := hηpos
      levelDisc_le := min_le_right _ _
      annulus := fun x hx hxv h1 h2 => hεreg x hx (hxv.trans_le (min_le_left _ _)) h1 h2
      sep := κ
      sep_pos := hκ
      separation := fun s c hs hc x hx y hy hxp hyp hxy =>
        hκsep (s, c) ⟨mem_closedBall_zero_iff.mpr hs, hc⟩ x hx y hy hxp hyp hxy
      small := m
      small_pos := hm
      small_roots := hmsmall
      pointRadius := r
      pointRadius_pos := hr
      point_small := fun x hx => ?_ }⟩
  have := hrb x hx
  rw [h0, dist_zero_right] at this
  exact this

namespace SlopeChoice

variable {A : ResolutionSectionAssembly g hd hi} {R : ℝ} {t : ℂ}

/-- An admissible level for the radii of a slope projection: it is small, and its singular
points lie over `|h| < ρ`. -/
def Good (C : SlopeChoice A R t) (s : ℂ) : Prop :=
  ‖s‖ < min (C.levelDisc / 2) C.small ∧
    ∃ L : ResolutionSectionLevel A, L.radius = R ∧ L.parameter = s ∧
      ∀ x ∈ L.points, x ∈ ball (0 : Source 2) C.pointRadius

/-- **Every sufficiently small nonzero level is admissible.** -/
theorem eventually_good (C : SlopeChoice A R t) (hR : 0 < R) (hRA : R ≤ A.radius) :
    ∀ᶠ s in 𝓝 (0 : ℂ), s ≠ 0 → C.Good s := by
  set r₃ := min C.pointRadius R with hr₃
  have hr₃pos : 0 < r₃ := lt_min C.pointRadius_pos hR
  have hr₃A : r₃ ≤ A.radius := (min_le_right _ _).trans hRA
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), ‖s‖ < min (C.levelDisc / 2) C.small := by
    have hpos : 0 < min (C.levelDisc / 2) C.small :=
      lt_min (half_pos C.levelDisc_pos) C.small_pos
    filter_upwards [ball_mem_nhds (0 : ℂ) hpos] with s hs
    simpa using hs
  filter_upwards [hsmall, A.levels R hR hRA, A.levels r₃ hr₃pos hr₃A] with s hs hL hL₃ hs0
  obtain ⟨Z, hZ, hcard, hinj, hemb, hreg, hsing, hsum⟩ := hL hs0
  obtain ⟨Z₃, hZ₃, hcard₃, -⟩ := hL₃ hs0
  refine ⟨hs, ⟨R, hR, hRA, s, hs0, Z, hZ, hcard, hinj, hemb, hreg, hsing, hsum⟩, rfl, rfl, ?_⟩
  have hsub : Z₃ ⊆ Z := by
    intro x hx
    obtain ⟨hxb, hxs, hxni⟩ := (hZ₃ x).mp hx
    exact (hZ x).mpr ⟨ball_subset_ball (min_le_right _ _) hxb, hxs, hxni⟩
  have heq : Z₃ = Z := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard₃])
  intro x hx
  change x ∈ Z at hx
  rw [← heq] at hx
  exact ball_subset_ball (min_le_left _ _) ((hZ₃ x).mp hx).1

end SlopeChoice

end OnLeConjecture.Analytic
