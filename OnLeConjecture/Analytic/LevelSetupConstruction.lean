/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupSlope

/-!
# Construction of the projection setup of a level

This module proves `LevelSetupStatement` (`LevelSetupInterface.lean`): every assembly `A` has a
level `L` and a setup `P` with the exported properties `P.SetupProperties`, for which the fields
(A) `RootFamilyHolds` and (D) `ConnectedHolds` hold (`levelSetupStatement`).

The order of choices follows Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`), with one change: the final projection is chosen among an
uncountable family of slopes by two pigeonhole steps, so that no smallness condition needs to be
uniform in the slope.

1. The slopes `t` for which `h_t y = y₂ - t y₁` is transverse to the image curve `W` (`Λ₀`) are
   all but finitely many. For each of them the central curve is unramified on every
   sufficiently small ball (`exists_central_unramified`). A pigeonhole step gives one radius `R`
   that works for uncountably many slopes (`Λ₁`).
2. For each slope of `Λ₁` the radii of `SlopeChoice` exist, and all sufficiently small nonzero
   levels are admissible (`SlopeChoice.eventually_good`). A second pigeonhole step gives one
   threshold for uncountably many slopes (`Λ₂`). A level `s` below this threshold is fixed.
3. The slopes for which `h_t` fails to be transverse to the local image equation at one of the
   singular points of the level are finitely many (`Germ.finite_setOf_slope_vanishingOrder_ne`).
   The final slope `t` is chosen in `Λ₂` outside them.
4. The critical values `V` are finite (`LevelBall.finite_criticalValues`), and the fibre
   coordinate is rotated, `ζ = (1 + τ i) y₁`, so that the real part of `ζ` separates the points
   of each critical fibre (`exists_rotation`).

The properties of `OuterAdmissible`, the compactness and finiteness statements, the field (A)
(`rootFamilyHolds_of_admissible`) and the field (D) (`connectedHolds_of`) are then verified.
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The exact order of a germ is unique. -/
theorem exactOrder_unique {n : ℕ} {f : Germ n} {a b : ℕ} (ha : f ∈ Germ.maximalIdeal n ^ a)
    (ha' : f ∉ Germ.maximalIdeal n ^ (a + 1)) (hb : f ∈ Germ.maximalIdeal n ^ b)
    (hb' : f ∉ Germ.maximalIdeal n ^ (b + 1)) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ha' (Ideal.pow_le_pow_right (Nat.succ_le_of_lt h) hb)
  · exact hb' (Ideal.pow_le_pow_right (Nat.succ_le_of_lt h) ha)

/-- A critical point of `H` is a critical point of `x ↦ (v x, h (H x))`. -/
theorem not_injective_levelBaseMap (A : ResolutionSectionAssembly g hd hi)
    (h : Source 3 →L[ℂ] ℂ) {x : Source 2} (hx : AnalyticAt ℂ A.H x)
    (hni : ¬ Injective (fderiv ℂ A.H x)) :
    ¬ Injective (fderiv ℂ (levelBaseMap A h) x) := by
  intro hinj
  apply hni
  rw [injective_iff_map_eq_zero] at hinj ⊢
  intro w hw
  apply hinj
  rw [fderiv_levelBaseMap_apply A h hx]
  have h0 : fderiv ℂ (fun y => A.H y 0) x w = fderiv ℂ A.H x w 0 := by
    have hd' := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).hasFDerivAt
      (x := A.H x)).comp x hx.differentiableAt.hasFDerivAt
    rw [show (fun y => A.H y 0) = (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 3 => ℂ) 0) ∘ A.H from rfl, hd'.fderiv]
    rfl
  have h1 : fderiv ℂ (fun y => h (A.H y)) x w = h (fderiv ℂ A.H x w) := by
    have hd' := (h.hasFDerivAt (x := A.H x)).comp x hx.differentiableAt.hasFDerivAt
    rw [show (fun y => h (A.H y)) = h ∘ A.H from rfl, hd'.fderiv]
    rfl
  rw [h0, h1, hw]
  simp

/-- **The rotation of the fibre coordinate.** For finitely many nonzero complex numbers `d q`,
there is `τ ∈ ℝ` with `Re ((1 + τ i) d q) ≠ 0` for all of them. -/
theorem exists_rotation {X : Type*} {T : Set X} (hT : T.Finite) (d : X → ℂ)
    (hd : ∀ q ∈ T, d q ≠ 0) : ∃ τ : ℝ, ∀ q ∈ T, ((1 + τ * Complex.I) * d q).re ≠ 0 := by
  set bad : Set ℝ := (fun q => (d q).re / (d q).im) '' T with hbad
  obtain ⟨τ, hτ⟩ := ((hT.image (fun q => (d q).re / (d q).im)).infinite_compl).nonempty
  refine ⟨τ, fun q hq hzero => ?_⟩
  have hre : ((1 + τ * Complex.I) * d q).re = (d q).re - τ * (d q).im := by
    simp [Complex.mul_re]
  rw [hre] at hzero
  by_cases him : (d q).im = 0
  · rw [him, mul_zero, sub_zero] at hzero
    exact hd q hq (Complex.ext hzero him)
  · apply hτ
    refine ⟨q, hq, ?_⟩
    field_simp
    linarith

/-- The central properties for every transverse slope, on every sufficiently small ball. -/
theorem exists_centralProps (A : ResolutionSectionAssembly g hd hi) {t : ℂ}
    (ht : vanishingOrder (lineRestriction ![1, t] A.imageEquation) = (A.squareSum : ℕ∞)) :
    ∃ R₀ > 0, ∀ R, 0 < R → R ≤ R₀ → CentralProps A R t := by
  have htr : ∃ u : Source 2, slopeBase t (hyperplaneInclusion 2 u) = 0 ∧
      slopeFibre 1 (hyperplaneInclusion 2 u) = 1 ∧
      vanishingOrder (lineRestriction u A.imageEquation) = (A.squareSum : ℕ∞) :=
    ⟨slopeVector t 1, slopeBase_slopeVector t 1, slopeFibre_slopeVector t one_ne_zero,
      (vanishingOrder_slopeVector_iff A.imageEquation_mem A.imageEquation_not_mem t
        one_ne_zero).mpr ht⟩
  obtain ⟨R₀, hR₀, hprops⟩ := exists_central_unramified A (slope_coordinates t one_ne_zero) htr
  exact ⟨R₀, hR₀, fun R hR hRR₀ => hprops R hR hRR₀⟩

/-- **The setup for a final slope.** Given a level `L` of radius `R`, a slope `t` transverse to
the image curve and to the local image equations at the singular points of `L`, the central
properties and the radii `C` for this slope, a small level, and singular points over `|h| < ρ`,
there is a setup with the exported properties for which the fields (A) and (D) hold. -/
theorem exists_setup_of_slope (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)
    {R : ℝ} (hLR : L.radius = R) {t : ℂ}
    (htW : vanishingOrder (lineRestriction ![1, t] A.imageEquation) = (A.squareSum : ℕ∞))
    (hCP : CentralProps A R t) (C : SlopeChoice A R t)
    (hs : ‖L.parameter‖ < min (C.levelDisc / 2) C.small)
    (hpts : ∀ x ∈ L.points, x ∈ ball (0 : Source 2) C.pointRadius)
    (htr : ∀ (j : Fin L.points.card) (a : ℕ),
      localSectionEquation A.H (L.point j) ∈ Germ.maximalIdeal 2 ^ a →
      localSectionEquation A.H (L.point j) ∉ Germ.maximalIdeal 2 ^ (a + 1) →
      vanishingOrder (lineRestriction ![1, t] (localSectionEquation A.H (L.point j))) = a) :
    ∃ P : LevelProjectionSetup A L, Nonempty P.SetupProperties ∧ P.RootFamilyHolds ∧
      P.ConnectedHolds := by
  classical
  obtain ⟨han, hinj, hiso, hunr⟩ := hCP
  set h := slopeBase t with hhdef
  set ζ₀ := slopeFibre 1 with hζ₀def
  set s := L.parameter with hsdef
  set ρ := C.radius with hρdef
  have hρ := C.radius_pos
  have hs₁ : ‖s‖ < C.levelDisc / 2 := hs.trans_le (min_le_left _ _)
  have hs₂ : ‖s‖ < C.small := hs.trans_le (min_le_right _ _)
  have hsη : ‖s‖ < C.levelDisc := hs₁.trans (half_lt_self C.levelDisc_pos)
  have hsμ : ‖s‖ < C.margin := hsη.trans_le C.levelDisc_le
  have hρμ := C.radius_lt_margin
  have hball : ∀ x, x ∈ ball (0 : Source 2) L.radius ↔ x ∈ ball (0 : Source 2) R := by
    intro x
    rw [hLR]
  -- the level over the disc
  have hLB : LevelBall A L.radius s h ρ := by
    refine ⟨hLR ▸ L.radius_pos, fun x hx => han x (hLR ▸ hx), L.injective,
      fun x hx hxs => (L.regular x hx hxs).1, fun x hx hxs => ?_⟩
    have h1 := C.sphere x (hLR ▸ hx)
    rw [hxs] at h1
    by_contra hle
    push Not at hle
    exact absurd h1 (not_le.mpr (max_lt hsμ (hle.trans_lt hρμ)))
  have hcoord₀ := slope_coordinates t (one_ne_zero (α := ℂ))
  have hVfin := hLB.finite_criticalValues hcoord₀
  set CV := LevelBall.criticalValues A L.radius s h ρ with hCVdef
  -- the critical values lie in the open square
  have hCVsq : ∀ c ∈ CV, c.re ∈ Ioo (-(ρ / 3)) (ρ / 3) ∧ c.im ∈ Ioo (-(ρ / 3)) (ρ / 3) := by
    rintro c ⟨hc, x, ⟨hx, hxs, hxc⟩, hni⟩
    by_contra hout
    have hsq : ρ / 3 ≤ squareNorm c := by
      by_contra hlt
      push Not at hlt
      apply hout
      simp only [squareNorm, max_lt_iff, abs_lt] at hlt
      exact ⟨⟨hlt.1.1, hlt.1.2⟩, hlt.2.1, hlt.2.2⟩
    apply hni
    refine C.annulus x ((hball x).mp hx) (by rw [hxs]; exact hsη) ?_ ?_
    · rw [hxc]
      have := squareNorm_le_norm c
      linarith
    · rw [hxc]
      exact (mem_ball_zero_iff.mp hc).le
  -- the rotation of the fibre coordinate
  set T : Set (Source 2 × Source 2) := {q | ∃ c ∈ CV, q.1 ∈ LevelBall.fibre A L.radius s h c ∧
    q.2 ∈ LevelBall.fibre A L.radius s h c ∧ q.1 ≠ q.2} with hTdef
  have hTfin : T.Finite := by
    have hU : (⋃ c ∈ CV, LevelBall.fibre A L.radius s h c).Finite :=
      hVfin.biUnion fun c hc => hLB.finite_fibre hcoord₀ (ball_subset_closedBall hc.1)
    refine (hU.prod hU).subset ?_
    rintro ⟨x, y⟩ ⟨c, hc, hx, hy, -⟩
    exact ⟨mem_biUnion hc hx, mem_biUnion hc hy⟩
  have hd : ∀ q ∈ T, ζ₀ (A.H q.1) - ζ₀ (A.H q.2) ≠ 0 := by
    rintro ⟨x, y⟩ ⟨c, -, ⟨hx, hxs, hxc⟩, ⟨hy, hys, hyc⟩, hxy⟩ hzero
    apply hxy
    apply L.injective hx hy
    apply hcoord₀
    exact Prod.ext (hxs.trans hys.symm) (Prod.ext (hxc.trans hyc.symm) (sub_eq_zero.mp hzero))
  obtain ⟨τ, hτ⟩ := exists_rotation hTfin (fun q => ζ₀ (A.H q.1) - ζ₀ (A.H q.2)) hd
  set κr : ℂ := 1 + τ * Complex.I with hκrdef
  have hκr : κr ≠ 0 := by
    intro h0
    have h1 : κr.re = 1 := by simp [hκrdef]
    rw [h0, Complex.zero_re] at h1
    exact zero_ne_one h1
  set ζ := slopeFibre κr with hζdef
  have hζ : ∀ y, ζ y = κr * ζ₀ y := by
    intro y
    simp [hζdef, hζ₀def]
  have hcoord := slope_coordinates t hκr
  -- the setup
  have hsqpos : 0 < ρ / 3 := by positivity
  have hsqle : ρ / 3 ≤ ρ / 2 * (√2 / 2) := by
    have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have h3 := Real.sqrt_nonneg 2
    nlinarith
  let P : LevelProjectionSetup A L :=
    { baseCoord := h
      fibreCoord := ζ
      coordinates := hcoord
      radius := ρ
      critical := hVfin.toFinset
      square := ρ / 3
      square_pos := hsqpos
      critical_mem := fun c hc => hCVsq c (hVfin.mem_toFinset.mp hc)
      outerRadius := ρ / 2
      square_le := hsqle
      outerRadius_lt := half_lt_self hρ }
  have hPcrit : ∀ c : ℂ, c ∈ P.critical ↔ c ∈ CV := fun c => hVfin.mem_toFinset
  have hcrit : ∀ c ∈ ball (0 : ℂ) P.radius, c ∉ P.critical → ∀ x ∈ P.levelFibre c,
      Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x) := by
    intro c hc hcV x hx
    by_contra hni
    exact hcV ((hPcrit c).mpr ⟨hc, x, hx, hni⟩)
  -- the hypotheses of the outer braid
  have hP : P.OuterAdmissible := by
    refine
      { analyticAt := fun x hx => han x (hLR ▸ hx)
        transverse := ⟨slopeVector t κr, slopeBase_slopeVector t κr, slopeFibre_slopeVector t hκr,
          (vanishingOrder_slopeVector_iff A.imageEquation_mem A.imageEquation_not_mem t hκr).mpr
            htW⟩
        isolated := fun x hx => hiso x (hLR ▸ hx)
        levelDisc := C.levelDisc
        parameter_lt := hsη
        outer_boundary := fun x hx hxv => ?_
        outer_unramified := fun x hx hxv hxρ => ?_
        centralDisc := C.centralDisc
        outerRadius_lt := (half_lt_self hρ).trans C.radius_lt_centralDisc
        central_boundary := fun x hx hx0 => C.central_boundary x (hLR ▸ hx) hx0
        central_unramified := fun x hx hx0 hpos _ =>
          hunr x ((hball x).mp hx) hx0 (norm_pos_iff.mp hpos) }
    · intro heq
      have h1 := C.sphere x (hLR ▸ hx)
      have h2 : ‖A.H x 0‖ < C.margin := hxv.trans_le C.levelDisc_le
      have h3 : ‖h (A.H x)‖ < C.margin := by
        change ‖h (A.H x)‖ = ρ / 2 at heq
        rw [heq]
        linarith
      exact absurd h1 (not_le.mpr (max_lt h2 h3))
    · change ‖h (A.H x)‖ = ρ / 2 at hxρ
      exact C.annulus x ((hball x).mp hx) hxv (by rw [hxρ]; linarith) (by rw [hxρ]; linarith)
  -- the separation and the small roots for the rotated fibre coordinate
  have hκf : 0 < ‖κr‖ * C.sep := mul_pos (norm_pos_iff.mpr hκr) C.sep_pos
  have hsep : ∀ c, squareNorm c = P.square → ∀ x ∈ P.levelFibre c, ∀ y ∈ P.levelFibre c,
      x ≠ y → ‖κr‖ * C.sep ≤ ‖P.fibreCoord (A.H x) - P.fibreCoord (A.H y)‖ := by
    rintro c hc x ⟨hx, hxs, hxc⟩ y ⟨hy, hys, hyc⟩ hxy
    have h1 := C.separation s c hs₁.le hc x ((hball x).mp hx) y ((hball y).mp hy)
      (Prod.ext hxs hxc) (Prod.ext hys hyc) hxy
    change ‖κr‖ * C.sep ≤ ‖ζ (A.H x) - ζ (A.H y)‖
    rw [hζ, hζ, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  -- a small regular value inside the square
  have hb : 0 < min (ρ / 3) C.small := lt_min hsqpos C.small_pos
  have hbadR : {r : ℝ | (r : ℂ) ∈ CV}.Finite :=
    hVfin.preimage (Complex.ofReal_injective.injOn)
  obtain ⟨r₁, ⟨hr₁0, hr₁b⟩, hr₁V⟩ := ((Set.Ioo_infinite hb).sdiff hbadR).nonempty
  set c₁ : ℂ := (r₁ : ℂ) with hc₁def
  have hsqc₁ : squareNorm c₁ = r₁ := by
    simp only [squareNorm, hc₁def, Complex.ofReal_re, Complex.ofReal_im, abs_zero,
      abs_of_pos hr₁0]
    exact max_eq_left hr₁0.le
  have hnc₁ : ‖c₁‖ = r₁ := by
    rw [hc₁def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₁0]
  have hc₁ : squareNorm c₁ < P.square := by
    rw [hsqc₁]
    exact hr₁b.trans_le (min_le_left _ _)
  have hc₁V : c₁ ∉ P.critical := fun h' => hr₁V ((hPcrit c₁).mp h')
  have hsmall : ∀ x ∈ P.levelFibre c₁, ‖P.fibreCoord (A.H x)‖ < ‖κr‖ * C.sep / 2 := by
    rintro x ⟨hx, hxs, hxc⟩
    have h1 := C.small_roots x (ball_subset_closedBall ((hball x).mp hx))
      (by rw [hxs]; exact hs₂)
      (by change ‖h (A.H x)‖ < C.small; rw [hxc, hnc₁]; exact hr₁b.trans_le (min_le_right _ _))
    change ‖ζ (A.H x)‖ < ‖κr‖ * C.sep / 2
    rw [hζ, norm_mul, mul_div_assoc]
    exact mul_lt_mul_of_pos_left h1 (norm_pos_iff.mpr hκr)
  -- the exported properties
  have hprops : P.SetupProperties := by
    refine
      { outer := hP
        compact := hLB.isCompact_locus
        critical_iff := fun c => hPcrit c
        fibre_finite := fun c hc => hLB.finite_fibre hcoord₀ (ball_subset_closedBall hc)
        point_critical := fun j => ?_
        critical_re_injOn := fun c hc x hx y hy hxy => ?_
        point_transverse := fun j a ha ha' => ?_ }
    · have hmem : L.point j ∈ L.points := (L.points.equivFin.symm j).2
      obtain ⟨hx, hxs, hni⟩ := (L.points_iff _).mp hmem
      have hHx : AnalyticAt ℂ A.H (L.point j) := han _ (ball_subset_closedBall ((hball _).mp hx))
      refine (hPcrit _).mpr ⟨?_, L.point j, ⟨hx, hxs, rfl⟩, not_injective_levelBaseMap A h hHx hni⟩
      exact mem_ball_zero_iff.mpr (C.point_small _ (hpts _ hmem))
    · by_contra hne
      have hq : (x, y) ∈ T := ⟨c, (hPcrit c).mp hc, hx, hy, hne⟩
      apply hτ (x, y) hq
      have e : (1 + τ * Complex.I) * (ζ₀ (A.H x) - ζ₀ (A.H y)) = ζ (A.H x) - ζ (A.H y) := by
        rw [hζ, hζ, mul_sub]
      rw [e, Complex.sub_re]
      change (ζ (A.H x)).re = (ζ (A.H y)).re at hxy
      rw [hxy, sub_self]
    · unfold LevelProjectionSetup.planeChart
      rw [isRegularInFirstCoordinateOfOrder_planeChartOf_iff P.coordinates
        (slopeBase_slopeVector t κr) (slopeFibre_slopeVector t hκr),
        vanishingOrder_slopeVector_iff ha ha' t hκr]
      exact htr j a ha ha'
  refine ⟨P, ⟨hprops⟩, ?_, ?_⟩
  · exact P.rootFamilyHolds_of_admissible hP hLB.boundary hcrit
  · exact P.connectedHolds_of hLB hcrit hκf hsep hc₁ hc₁V hsmall

/-- **The construction of the projection setup of a level** (fields (A) and (D), with the
exported properties for (B) and (C)). -/
theorem levelSetupStatement : LevelSetupStatement := by
  intro g hd hi A
  classical
  -- 1. the slopes transverse to the image curve, and one radius for uncountably many of them
  set Λ₀ : Set ℂ :=
    {t | vanishingOrder (lineRestriction ![1, t] A.imageEquation) = (A.squareSum : ℕ∞)}
    with hΛ₀def
  have hΛ₀ : ¬ Λ₀.Countable := by
    have hfin := Germ.finite_setOf_slope_vanishingOrder_ne A.imageEquation_mem
      A.imageEquation_not_mem
    have heq : Λ₀ = {t : ℂ | vanishingOrder (lineRestriction ![1, t] A.imageEquation) ≠
        ((∑ p, (A.tree.multiplicity p) ^ 2 : ℕ) : ℕ∞)}ᶜ := by
      ext t
      simp only [hΛ₀def, mem_ofPred_eq, mem_compl_iff, not_not]
      rfl
    rw [heq]
    exact not_countable_compl_of_countable hfin.countable
  have hcentral : ∀ t ∈ Λ₀, ∃ m : ℕ, ∀ R, 0 < R → R ≤ 1 / ((m : ℝ) + 1) → CentralProps A R t := by
    intro t ht
    obtain ⟨R₀, hR₀, hprops⟩ := exists_centralProps A ht
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hR₀
    exact ⟨m, fun R hR hRm => hprops R hR (hRm.trans hm.le)⟩
  obtain ⟨m, hΛ₁⟩ := exists_not_countable_of_forall_exists hΛ₀ hcentral
  set Λ₁ : Set ℂ := {t | t ∈ Λ₀ ∧ ∀ R, 0 < R → R ≤ 1 / ((m : ℝ) + 1) → CentralProps A R t}
    with hΛ₁def
  set R : ℝ := min (1 / ((m : ℝ) + 1)) A.radius with hRdef
  have hR : 0 < R := lt_min (by positivity) A.radius_pos
  have hRA : R ≤ A.radius := min_le_right _ _
  have hRm : R ≤ 1 / ((m : ℝ) + 1) := min_le_left _ _
  -- 2. the radii of each slope, and one threshold of levels for uncountably many slopes
  have hslope : ∀ t ∈ Λ₁, ∃ n : ℕ, ∃ C : SlopeChoice A R t,
      ∀ s : ℂ, ‖s‖ < 1 / ((n : ℝ) + 1) → s ≠ 0 → C.Good s := by
    intro t ht
    obtain ⟨C⟩ := exists_slopeChoice A hR (ht.2 R hR hRm)
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp (C.eventually_good hR hRA)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, C, fun s hs hs0 => hεb ?_ hs0⟩
    rw [dist_zero_right]
    exact hs.trans hn
  obtain ⟨n, hΛ₂⟩ := exists_not_countable_of_forall_exists hΛ₁ hslope
  set Λ₂ : Set ℂ := {t | t ∈ Λ₁ ∧ ∃ C : SlopeChoice A R t,
      ∀ s : ℂ, ‖s‖ < 1 / ((n : ℝ) + 1) → s ≠ 0 → C.Good s} with hΛ₂def
  -- 3. the level
  set s₀ : ℂ := ((1 / (2 * ((n : ℝ) + 1)) : ℝ) : ℂ) with hs₀def
  have hs₀pos : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hs₀norm : ‖s₀‖ < 1 / ((n : ℝ) + 1) := by
    rw [hs₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs₀pos]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) hpos]
    linarith
  have hs₀ne : s₀ ≠ 0 := by
    rw [hs₀def]
    exact_mod_cast hs₀pos.ne'
  obtain ⟨t₀, ht₀⟩ : Λ₂.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    exact hΛ₂ (hemp ▸ countable_empty)
  obtain ⟨-, C₀, hC₀⟩ := ht₀
  obtain ⟨-, L, hLR, hLs, -⟩ := hC₀ s₀ hs₀norm hs₀ne
  -- 4. the slopes transverse at the singular points of the level
  have hord : ∀ j : Fin L.points.card, ∃ a : ℕ,
      localSectionEquation A.H (L.point j) ∈ Germ.maximalIdeal 2 ^ a ∧
        localSectionEquation A.H (L.point j) ∉ Germ.maximalIdeal 2 ^ (a + 1) := by
    intro j
    obtain ⟨-, -, -, -, a, -, -, ha, ha', -⟩ := L.singular (L.point j)
      (L.points.equivFin.symm j).2
    exact ⟨a, ha, ha'⟩
  choose a ha using hord
  set B : Set ℂ := ⋃ j : Fin L.points.card,
    {t | vanishingOrder (lineRestriction ![1, t] (localSectionEquation A.H (L.point j))) ≠ a j}
    with hBdef
  have hB : B.Countable :=
    (Set.finite_iUnion fun j => Germ.finite_setOf_slope_vanishingOrder_ne (ha j).1
      (ha j).2).countable
  obtain ⟨t, ⟨⟨htΛ₀, htCP⟩, C, hCgood⟩, htB⟩ := nonempty_diff_of_not_countable hΛ₂ hB
  obtain ⟨hsmall, L', hL'R, hL's, hL'pts⟩ := hCgood s₀ hs₀norm hs₀ne
  -- the singular points of `L` and of `L'` coincide
  have hpts : ∀ x ∈ L.points, x ∈ ball (0 : Source 2) C.pointRadius := by
    intro x hx
    apply hL'pts
    rw [L'.points_iff, hL'R, hL's]
    rw [L.points_iff, hLR, hLs] at hx
    exact hx
  have htr : ∀ (j : Fin L.points.card) (a' : ℕ),
      localSectionEquation A.H (L.point j) ∈ Germ.maximalIdeal 2 ^ a' →
      localSectionEquation A.H (L.point j) ∉ Germ.maximalIdeal 2 ^ (a' + 1) →
      vanishingOrder (lineRestriction ![1, t] (localSectionEquation A.H (L.point j))) = a' := by
    intro j a' ha₁ ha₂
    have heq : a j = a' := exactOrder_unique (ha j).1 (ha j).2 ha₁ ha₂
    rw [← heq]
    by_contra hne
    exact htB (mem_iUnion.mpr ⟨j, hne⟩)
  -- 5. the setup
  obtain ⟨P, hP⟩ := exists_setup_of_slope A L hLR htΛ₀ (htCP R hR hRm) C (hLs ▸ hsmall) hpts htr
  exact ⟨L, P, hP⟩

end OnLeConjecture.Analytic
