/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelOuterFibration
public import OnLeConjecture.Analytic.LevelOuterCentral

/-!
# The outer braid of an admissible setup

This module proves the field (B) `OuterHolds` of a setup `P : LevelProjectionSetup A L` from the
hypotheses `P.OuterAdmissible` (`LevelOuterAdmissible.lean`). It formalizes the paragraph "Over
`|h| = ρ` the source sheets vary by the implicit function theorem without collision as `v` moves
from zero to the chosen level ... their outer configurations form a homotopy of closed `S`-braids
... The central branch construction then compares this outer word with `d_S w`" of the subsection
"Global factorization, exponent count, and transitivity" of Section 3 of the written proof of
Statement E (`statement-E-complete-proof.tex`).

Write `R = L.radius`, `s = L.parameter`, `ρ₂ = P.outerRadius`, `η = levelDisc`,
`δ = centralDisc`, and `Φ = levelBaseMap A h : x ↦ (v x, h (H x))`.

* `exists_isLocalInverse_levelBaseMap`: the inverse function theorem for `Φ` at a point where `H`
  is analytic and the differential of `Φ` is injective.
* `isRootFamily_central`: the roots of the central level `v = 0` form a root family over the
  punctured disc `0 < |c| < δ` (`isRootFamily_of_fibration`, with the number of points computed at
  one small circle).
* `isRootFamily_deformation`: the roots of the levels `v = Re w · s` over the base points
  `ρ₂ e^{i Im w}` form a root family over the strip `|Re w| < η / |s|`, which contains the square
  `[0, 1] × ℝ`.
* `signedBraidConj_deformation`: the square relation (`IsRootFamily.square_relation`) on the strip
  gives a conjugacy between the root path words of the outer circle at the levels `0` and `s`; the
  two vertical sides of the square have the same base points.
* `signedBraidConj_central`: the square relation on the punctured disc, for the radial homotopy
  between two circles, gives a conjugacy between the root path words of the central level over
  the two circles.
* `LevelProjectionSetup.outerHolds_of_admissible`: `P.OuterAdmissible → P.OuterHolds`. The word
  `w` and its identities come from `exists_centralRootBraid` (job J14 at a small radius).
-/

@[expose] public noncomputable section

open Set Function Filter Metric Real
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory PlaneCurve OnLeConjecture.Analytic.Germ

variable {S : ℕ}

/-! ### Changing the set-valued family along a path -/

theorem IsRootLabellingOn.congr_fibre {X : Type*} [TopologicalSpace X] {Z Z' : ℂ → Set ℂ}
    {γ γ' : X → ℂ} {A : Set X} {K : Fin S → X → ℂ} (h : IsRootLabellingOn Z γ A K)
    (hZ : ∀ x ∈ A, Z (γ x) = Z' (γ' x)) : IsRootLabellingOn Z' γ' A K :=
  ⟨h.continuousOn, h.injective, fun x hx => (h.range_eq x hx).trans (hZ x hx)⟩

theorem IsRootPathWord.congr_fibre {Z Z' : ℂ → Set ℂ} {γ γ' : ℝ → ℂ} {u v : ℝ}
    {W : SignedAdjacentWord S} (h : IsRootPathWord Z γ u v W)
    (hZ : ∀ t ∈ Icc u v, Z (γ t) = Z' (γ' t)) : IsRootPathWord Z' γ' u v W := by
  obtain ⟨K, hK, hW⟩ := h
  exact ⟨K, hK.congr_fibre hZ, hW⟩

/-- A root path word over the circle `θ ∈ [b, b + 2π]` is a root path word of the circle
parametrized by `t ↦ 2π t + b`, `t ∈ [0, 1]`. -/
theorem IsRootPathWord.circle_unit {Z : ℂ → Set ℂ} {r b : ℝ} {W : SignedAdjacentWord S}
    (h : IsRootPathWord Z (circlePath r) b (b + 2 * π) W) :
    IsRootPathWord Z (fun t => circlePath r (2 * π * t + b)) 0 1 W := by
  have h0 : 2 * π * 0 + b = b := by ring
  have h1 : 2 * π * 1 + b = b + 2 * π := by ring
  refine IsRootPathWord.comp_affine (φ := fun t => 2 * π * t + b) (α := 2 * π) (β := b)
    (by positivity) (fun t => rfl) ?_
  simp only [h0, h1]
  exact h

theorem ncard_range_fin {f : Fin S → ℂ} (hf : Injective f) : (range f).ncard = S := by
  rw [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem continuous_circlePath_prod {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun p => circlePath (f p) (g p) := by
  simp only [circlePath]
  fun_prop

/-! ### The map `x ↦ (v x, h (H x))` -/

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

theorem levelBaseMap_analyticAt (A : ResolutionSectionAssembly g hd hi)
    (baseCoord : Source 3 →L[ℂ] ℂ) {x : Source 2} (hx : AnalyticAt ℂ A.H x) :
    AnalyticAt ℂ (levelBaseMap A baseCoord) x := by
  have h0 : AnalyticAt ℂ (fun y => A.H y 0) x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp hx
  have h1 : AnalyticAt ℂ (fun y => baseCoord (A.H y)) x := (baseCoord.analyticAt _).comp hx
  exact h0.prod h1

/-- **The inverse function theorem for `x ↦ (v x, h (H x))`.** -/
theorem exists_isLocalInverse_levelBaseMap (A : ResolutionSectionAssembly g hd hi)
    (baseCoord : Source 3 →L[ℂ] ℂ) {x : Source 2} (hx : AnalyticAt ℂ A.H x)
    (hinj : Injective (fderiv ℂ (levelBaseMap A baseCoord) x)) :
    ∃ (V : Set (Source 2)) (T : Set (ℂ × ℂ)) (ψ : ℂ × ℂ → Source 2),
      IsLocalInverse (levelBaseMap A baseCoord) V T ψ ∧ x ∈ V := by
  have hd := (levelBaseMap_analyticAt A baseCoord hx).hasStrictFDerivAt
  set f' := fderiv ℂ (levelBaseMap A baseCoord) x with hf'
  have hdim : Module.finrank ℂ (Source 2) = Module.finrank ℂ (ℂ × ℂ) := by simp
  set e : Source 2 ≃L[ℂ] ℂ × ℂ :=
    (LinearMap.linearEquivOfInjective (f' : Source 2 →ₗ[ℂ] ℂ × ℂ) hinj hdim).toContinuousLinearEquiv
  have he : (e : Source 2 →L[ℂ] ℂ × ℂ) = f' := ContinuousLinearMap.ext fun v => rfl
  have hd' : HasStrictFDerivAt (levelBaseMap A baseCoord) (e : Source 2 →L[ℂ] ℂ × ℂ) x := by
    rw [he]
    exact hd
  exact HasStrictFDerivAt.exists_isLocalInverse hd'

theorem continuousOn_levelBaseMap (A : ResolutionSectionAssembly g hd hi)
    (baseCoord : Source 3 →L[ℂ] ℂ) {R : ℝ}
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x) :
    ContinuousOn (levelBaseMap A baseCoord) (closedBall 0 R) := fun x hx =>
  (levelBaseMap_analyticAt A baseCoord (han x hx)).continuousAt.continuousWithinAt

theorem continuousOn_fibreCoord (A : ResolutionSectionAssembly g hd hi)
    (fibreCoord : Source 3 →L[ℂ] ℂ) {R : ℝ}
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x) :
    ContinuousOn (fun x => fibreCoord (A.H x)) (ball 0 R) := fun x hx =>
  (fibreCoord.continuous.continuousAt.comp
    (han x (ball_subset_closedBall hx)).continuousAt).continuousWithinAt

theorem fibre_injective (A : ResolutionSectionAssembly g hd hi)
    {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y)) {R : ℝ}
    (hinj : InjOn A.H (ball (0 : Source 2) R)) {x y : Source 2} (hx : x ∈ ball (0 : Source 2) R)
    (hy : y ∈ ball (0 : Source 2) R)
    (hxy : levelBaseMap A baseCoord x = levelBaseMap A baseCoord y)
    (hζ : fibreCoord (A.H x) = fibreCoord (A.H y)) : x = y := by
  simp only [levelBaseMap, Prod.mk.injEq] at hxy
  apply hinj hx hy
  apply hcoord
  simp only [hxy.1, hxy.2, hζ]

theorem levelRootsAt_eq_image (A : ResolutionSectionAssembly g hd hi) (R : ℝ)
    (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) (s c : ℂ) :
    levelRootsAt A R baseCoord fibreCoord s c = (fun x => fibreCoord (A.H x)) ''
      {x | x ∈ ball (0 : Source 2) R ∧ levelBaseMap A baseCoord x = (s, c)} := by
  simp only [levelRootsAt, levelBaseMap, Prod.mk.injEq]

theorem ncard_fibre (A : ResolutionSectionAssembly g hd hi)
    {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y)) {R : ℝ}
    (hinj : InjOn A.H (ball (0 : Source 2) R)) (s c : ℂ) :
    {x | x ∈ ball (0 : Source 2) R ∧ levelBaseMap A baseCoord x = (s, c)}.ncard =
      (levelRootsAt A R baseCoord fibreCoord s c).ncard := by
  rw [levelRootsAt_eq_image]
  refine (InjOn.ncard_image fun x hx y hy hxy => ?_).symm
  exact fibre_injective A hcoord hinj hx.1 hy.1 (hx.2.trans hy.2.symm) hxy

/-! ### The two root families -/

/-- **The central root family.** The roots of the central level `v = 0` form a root family over
the punctured disc `0 < |c| < δ`. -/
theorem isRootFamily_central (A : ResolutionSectionAssembly g hd hi) {R δ : ℝ}
    {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y))
    (hinj : InjOn A.H (ball (0 : Source 2) R))
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x)
    (hbd : ∀ x : Source 2, ‖x‖ = R → A.H x 0 = 0 → δ ≤ ‖baseCoord (A.H x)‖)
    (hunr : ∀ x ∈ ball (0 : Source 2) R, A.H x 0 = 0 → 0 < ‖baseCoord (A.H x)‖ →
      ‖baseCoord (A.H x)‖ < δ → Injective (fderiv ℂ (levelBaseMap A baseCoord) x))
    {c₀ : ℂ} (hc₀ : 0 < ‖c₀‖) (hc₀δ : ‖c₀‖ < δ)
    (hcount : (levelRootsAt A R baseCoord fibreCoord 0 c₀).ncard = S) :
    IsRootFamily (levelRootsAt A R baseCoord fibreCoord 0) S {c | 0 < ‖c‖ ∧ ‖c‖ < δ} := by
  set U : Set ℂ := {c | 0 < ‖c‖ ∧ ‖c‖ < δ} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hUc : IsPreconnected U := by
    have himage : U = (fun p : ℝ × ℝ => circlePath p.1 p.2) '' (Ioo 0 δ ×ˢ univ) := by
      ext c
      constructor
      · rintro ⟨hc0, hcδ⟩
        refine ⟨(‖c‖, Complex.arg c), ⟨⟨hc0, hcδ⟩, mem_univ _⟩, ?_⟩
        simp only [circlePath]
        exact Complex.norm_mul_exp_arg_mul_I c
      · rintro ⟨p, ⟨⟨hp0, hpδ⟩, -⟩, rfl⟩
        change 0 < ‖circlePath p.1 p.2‖ ∧ ‖circlePath p.1 p.2‖ < δ
        rw [norm_circlePath hp0.le]
        exact ⟨hp0, hpδ⟩
    rw [himage]
    exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
      (continuous_circlePath_prod continuous_fst continuous_snd).continuousOn
  have hfam := isRootFamily_of_fibration (Φ := levelBaseMap A baseCoord)
    (ψ := fun x => fibreCoord (A.H x)) (R := R) (γ := fun c => ((0 : ℂ), c)) (U := U) (S := S)
    hUo hUc (by fun_prop) (continuousOn_levelBaseMap A baseCoord han)
    (continuousOn_fibreCoord A fibreCoord han) ?_ ?_ ?_ (w₀ := c₀) ⟨hc₀, hc₀δ⟩
    (by rw [ncard_fibre A hcoord hinj]; exact hcount)
  · have hfun : (fun c => (fun x => fibreCoord (A.H x)) ''
        {x | x ∈ ball (0 : Source 2) R ∧ levelBaseMap A baseCoord x = ((0 : ℂ), c)}) =
        levelRootsAt A R baseCoord fibreCoord 0 := by
      funext c
      rw [levelRootsAt_eq_image]
    rw [hfun] at hfam
    exact hfam
  · intro c hc x hx hxc
    simp only [levelBaseMap, Prod.mk.injEq] at hxc
    refine mem_ball_zero_iff.mpr (lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx) fun hxR => ?_)
    have h := hbd x hxR hxc.1
    rw [hxc.2] at h
    exact absurd hc.2 (not_lt.mpr h)
  · intro c hc x hx hxc
    simp only [levelBaseMap, Prod.mk.injEq] at hxc
    refine exists_isLocalInverse_levelBaseMap A baseCoord (han x (ball_subset_closedBall hx)) ?_
    exact hunr x hx hxc.1 (by rw [hxc.2]; exact hc.1) (by rw [hxc.2]; exact hc.2)
  · intro c _ x hx y hy hxc hyc hxy
    exact fibre_injective A hcoord hinj hx hy (hxc.trans hyc.symm) hxy

/-- **The deformation root family.** The roots of the levels `v = Re w · s` over the base points
`ρ₂ e^{i Im w}` form a root family over the strip `|Re w| < η / |s|`. -/
theorem isRootFamily_deformation (A : ResolutionSectionAssembly g hd hi) {R η ρ₂ : ℝ} {s : ℂ}
    (hs : s ≠ 0) (hη : 0 < η) (hρ₂ : 0 ≤ ρ₂) {baseCoord fibreCoord : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, baseCoord y, fibreCoord y))
    (hinj : InjOn A.H (ball (0 : Source 2) R))
    (han : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x)
    (hbd : ∀ x : Source 2, ‖x‖ = R → ‖A.H x 0‖ < η → ‖baseCoord (A.H x)‖ ≠ ρ₂)
    (hunr : ∀ x ∈ ball (0 : Source 2) R, ‖A.H x 0‖ < η → ‖baseCoord (A.H x)‖ = ρ₂ →
      Injective (fderiv ℂ (levelBaseMap A baseCoord) x))
    (hcount : (levelRootsAt A R baseCoord fibreCoord 0 (circlePath ρ₂ 0)).ncard = S) :
    IsRootFamily (fun w => levelRootsAt A R baseCoord fibreCoord ((w.re : ℂ) * s)
      (circlePath ρ₂ w.im)) S (Complex.re ⁻¹' Ioo (-(η / ‖s‖)) (η / ‖s‖)) := by
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
  set U : Set ℂ := Complex.re ⁻¹' Ioo (-(η / ‖s‖)) (η / ‖s‖) with hU
  have hUo : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hUc : IsPreconnected U :=
    ((convex_Ioo _ _).linear_preimage Complex.reLm).isPreconnected
  have hlev : ∀ w ∈ U, ‖(w.re : ℂ) * s‖ < η := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h := abs_lt.mpr hw
    calc |w.re| * ‖s‖ < η / ‖s‖ * ‖s‖ := mul_lt_mul_of_pos_right h hsn
      _ = η := div_mul_cancel₀ η hsn.ne'
  have hfam := isRootFamily_of_fibration (Φ := levelBaseMap A baseCoord)
    (ψ := fun x => fibreCoord (A.H x)) (R := R)
    (γ := fun w : ℂ => ((w.re : ℂ) * s, circlePath ρ₂ w.im)) (U := U) (S := S)
    hUo hUc ?_ (continuousOn_levelBaseMap A baseCoord han)
    (continuousOn_fibreCoord A fibreCoord han) ?_ ?_ ?_ (w₀ := 0) ?_ ?_
  · have hfun : (fun w : ℂ => (fun x => fibreCoord (A.H x)) ''
        {x | x ∈ ball (0 : Source 2) R ∧
          levelBaseMap A baseCoord x = ((w.re : ℂ) * s, circlePath ρ₂ w.im)}) =
        fun w : ℂ =>
          levelRootsAt A R baseCoord fibreCoord ((w.re : ℂ) * s) (circlePath ρ₂ w.im) := by
      funext w
      rw [levelRootsAt_eq_image]
    rw [hfun] at hfam
    exact hfam
  · exact (Continuous.prodMk (by fun_prop)
      ((continuous_circlePath ρ₂).comp Complex.continuous_im)).continuousOn
  · intro w hw x hx hxw
    simp only [levelBaseMap, Prod.mk.injEq] at hxw
    refine mem_ball_zero_iff.mpr (lt_of_le_of_ne (mem_closedBall_zero_iff.mp hx) fun hxR => ?_)
    refine hbd x hxR (by rw [hxw.1]; exact hlev w hw) ?_
    rw [hxw.2, norm_circlePath hρ₂]
  · intro w hw x hx hxw
    simp only [levelBaseMap, Prod.mk.injEq] at hxw
    refine exists_isLocalInverse_levelBaseMap A baseCoord (han x (ball_subset_closedBall hx)) ?_
    exact hunr x hx (by rw [hxw.1]; exact hlev w hw) (by rw [hxw.2, norm_circlePath hρ₂])
  · intro w _ x hx y hy hxw hyw hxy
    exact fibre_injective A hcoord hinj hx hy (hxw.trans hyw.symm) hxy
  · change (0 : ℂ).re ∈ Ioo (-(η / ‖s‖)) (η / ‖s‖)
    have hηs : 0 < η / ‖s‖ := div_pos hη hsn
    simp only [Complex.zero_re]
    exact ⟨neg_lt_zero.mpr hηs, hηs⟩
  · rw [ncard_fibre A hcoord hinj]
    simpa using hcount

/-! ### The square relations -/

/-- **The deformation conjugacy.** For a root family of the levels `v = Re w · s` over the base
points `ρ₂ e^{i Im w}` on a strip `|Re w| < a` with `a > 1`, the root path words of the outer circle
at the levels `0` and `s` are conjugate. -/
theorem signedBraidConj_deformation {Z₂ : ℂ → ℂ → Set ℂ} {s : ℂ} {ρ₂ a b : ℝ}
    (hZ : IsRootFamily (fun w : ℂ => Z₂ ((w.re : ℂ) * s) (circlePath ρ₂ w.im)) S
      (Complex.re ⁻¹' Ioo (-a) a)) (ha : 1 < a) {W₀ W : SignedAdjacentWord S}
    (hW₀ : IsRootPathWord (Z₂ 0) (fun t => circlePath ρ₂ (2 * π * t + b)) 0 1 W₀)
    (hW : IsRootPathWord (Z₂ s) (fun t => circlePath ρ₂ (2 * π * t + b)) 0 1 W) :
    SignedBraidConj W₀ W := by
  set Zw : ℂ → Set ℂ := fun w => Z₂ ((w.re : ℂ) * s) (circlePath ρ₂ w.im) with hZw
  set P : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + ((2 * π * p.2 + b : ℝ) : ℂ) * Complex.I with hPdef
  have hPre : ∀ p, (P p).re = p.1 := fun p => by simp [hPdef]
  have hPim : ∀ p, (P p).im = 2 * π * p.2 + b := fun p => by simp [hPdef]
  have hZP : ∀ p, Zw (P p) = Z₂ ((p.1 : ℂ) * s) (circlePath ρ₂ (2 * π * p.2 + b)) := fun p => by
    simp only [hZw, hPre, hPim]
  have hPc : Continuous P := by
    simp only [hPdef]
    fun_prop
  have hPU : MapsTo P (Icc 0 1 ×ˢ Icc 0 1) (Complex.re ⁻¹' Ioo (-a) a) := by
    rintro p ⟨hp1, -⟩
    change (P p).re ∈ Ioo (-a) a
    rw [hPre]
    exact ⟨by linarith [hp1.1], by linarith [hp1.2]⟩
  have hb : IsRootPathWord Zw (fun t => P (0, t)) 0 1 W₀ :=
    hW₀.congr_fibre fun t _ => by rw [hZP]; simp
  have ht : IsRootPathWord Zw (fun t => P (1, t)) 0 1 W :=
    hW.congr_fibre fun t _ => by rw [hZP]; simp
  obtain ⟨X, hX⟩ := hZ.exists_isRootPathWord (γ := fun σ => P (σ, 0)) zero_lt_one
    (hPc.comp (Continuous.prodMk continuous_id continuous_const)).continuousOn
    fun σ hσ => hPU ⟨hσ, ⟨le_rfl, zero_le_one⟩⟩
  have hr : IsRootPathWord Zw (fun σ => P (σ, 1)) 0 1 X := by
    refine hX.congr_fibre fun σ _ => ?_
    rw [hZP, hZP]
    have h : 2 * π * (1 : ℝ) + b = (2 * π * 0 + b) + 2 * π := by ring
    rw [h, circlePath_add_two_pi]
  exact SignedBraidConj.of_equiv_conjugate (hZ.square_relation hPc.continuousOn hPU hb ht hX hr)

/-- **The radial conjugacy.** For a root family over the punctured disc `0 < |c| < δ`, the root path
words of two circles `|c| = r₁` and `|c| = r₂` with `0 < r₁, r₂ < δ` are conjugate. -/
theorem signedBraidConj_central {Z : ℂ → Set ℂ} {δ r₁ r₂ b : ℝ}
    (hZ : IsRootFamily Z S {c | 0 < ‖c‖ ∧ ‖c‖ < δ}) (hr₁ : 0 < r₁) (hr₁δ : r₁ < δ)
    (hr₂ : 0 < r₂) (hr₂δ : r₂ < δ) {W₁ W₂ : SignedAdjacentWord S}
    (hW₁ : IsRootPathWord Z (fun t => circlePath r₁ (2 * π * t + b)) 0 1 W₁)
    (hW₂ : IsRootPathWord Z (fun t => circlePath r₂ (2 * π * t + b)) 0 1 W₂) :
    SignedBraidConj W₁ W₂ := by
  set P : ℝ × ℝ → ℂ := fun p => circlePath ((1 - p.1) * r₁ + p.1 * r₂) (2 * π * p.2 + b)
    with hPdef
  have hPc : Continuous P :=
    continuous_circlePath_prod (by fun_prop) (by fun_prop)
  have hrad : ∀ σ ∈ Icc (0 : ℝ) 1, (1 - σ) * r₁ + σ * r₂ ∈ Ioo 0 δ := fun σ hσ => by
    have h := convex_Ioo (0 : ℝ) δ ⟨hr₁, hr₁δ⟩ ⟨hr₂, hr₂δ⟩ (sub_nonneg.mpr hσ.2) hσ.1
      (by ring)
    simpa only [smul_eq_mul] using h
  have hPU : MapsTo P (Icc 0 1 ×ˢ Icc 0 1) {c | 0 < ‖c‖ ∧ ‖c‖ < δ} := by
    rintro p ⟨hp1, -⟩
    have h := hrad p.1 hp1
    change 0 < ‖P p‖ ∧ ‖P p‖ < δ
    simp only [hPdef]
    rw [norm_circlePath h.1.le]
    exact h
  have hb : IsRootPathWord Z (fun t => P (0, t)) 0 1 W₁ :=
    hW₁.congr_fibre fun t _ => by simp [hPdef]
  have ht : IsRootPathWord Z (fun t => P (1, t)) 0 1 W₂ :=
    hW₂.congr_fibre fun t _ => by simp [hPdef]
  obtain ⟨X, hX⟩ := hZ.exists_isRootPathWord (γ := fun σ => P (σ, 0)) zero_lt_one
    (hPc.comp (Continuous.prodMk continuous_id continuous_const)).continuousOn
    fun σ hσ => hPU ⟨hσ, ⟨le_rfl, zero_le_one⟩⟩
  have hr : IsRootPathWord Z (fun σ => P (σ, 1)) 0 1 X := by
    refine hX.congr_fibre fun σ _ => ?_
    simp only [hPdef]
    have h : 2 * π * (1 : ℝ) + b = (2 * π * 0 + b) + 2 * π := by ring
    rw [h, circlePath_add_two_pi]
  exact SignedBraidConj.of_equiv_conjugate (hZ.square_relation hPc.continuousOn hPU hb ht hX hr)

/-! ### The outer braid -/

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}

/-- **The outer braid of an admissible setup** (field (B) of `LevelProjectionInput`). -/
theorem outerHolds_of_admissible (P : LevelProjectionSetup A L) (hP : P.OuterAdmissible) :
    P.OuterHolds := by
  have hR := L.radius_pos
  have hHc : ContinuousOn A.H (closedBall 0 L.radius) := fun x hx =>
    (hP.analyticAt x hx).continuousAt.continuousWithinAt
  have hρ₂ : 0 < P.outerRadius := by
    have h1 := P.square_pos
    have h2 := P.square_le
    have h3 : 0 < √2 / 2 := by positivity
    by_contra hneg
    have hneg' : P.outerRadius ≤ 0 := le_of_not_gt hneg
    nlinarith
  have hδ : 0 < hP.centralDisc := hρ₂.trans hP.outerRadius_lt
  obtain ⟨w, hcyc, hlen, hsmall⟩ :=
    exists_centralRootBraid A hR P.coordinates hHc hP.transverse hP.isolated
  refine ⟨w, hcyc, hlen, fun b K hK W hW => ?_⟩
  set Z₀ := levelRootsAt A L.radius P.baseCoord P.fibreCoord 0 with hZ₀def
  -- the central level over a small circle: job J14
  obtain ⟨r, hr, hrδ, y, hy, hyrep⟩ := hsmall hP.centralDisc hδ
  have hcount₀ : (Z₀ (circlePath r 0)).ncard = A.squareSum := by
    rw [← hy.range_eq 0 (mem_univ _)]
    exact ncard_range_fin (hy.injective 0 (mem_univ _))
  have hZ₀ : IsRootFamily Z₀ A.squareSum {c | 0 < ‖c‖ ∧ ‖c‖ < hP.centralDisc} :=
    isRootFamily_central A P.coordinates L.injective hP.analyticAt hP.central_boundary
      hP.central_unramified (c₀ := circlePath r 0) (by rw [norm_circlePath hr.le]; exact hr)
      (by rw [norm_circlePath hr.le]; exact hrδ) hcount₀
  have hcircle : ∀ θ, circlePath P.outerRadius θ ∈ {c | 0 < ‖c‖ ∧ ‖c‖ < hP.centralDisc} :=
    fun θ => by
      change 0 < ‖circlePath P.outerRadius θ‖ ∧ ‖circlePath P.outerRadius θ‖ < hP.centralDisc
      rw [norm_circlePath hρ₂.le]
      exact ⟨hρ₂, hP.outerRadius_lt⟩
  -- the deformation from the central level to the level `s`
  have hs := L.parameter_ne_zero
  have hsn : 0 < ‖L.parameter‖ := norm_pos_iff.mpr hs
  have hη : 0 < hP.levelDisc := (norm_nonneg _).trans_lt hP.parameter_lt
  have hcountρ : (Z₀ (circlePath P.outerRadius 0)).ncard = A.squareSum := by
    obtain ⟨g', hg', hg'Z⟩ := hZ₀.exists_labels_at (hcircle 0)
    rw [hg'Z]
    exact ncard_range_fin hg'
  have hZs := isRootFamily_deformation A hs hη hρ₂.le P.coordinates L.injective hP.analyticAt
    hP.outer_boundary hP.outer_unramified hcountρ
  have ha : 1 < hP.levelDisc / ‖L.parameter‖ := (one_lt_div hsn).mpr hP.parameter_lt
  -- the root path words
  have hWs : IsRootPathWord (levelRootsAt A L.radius P.baseCoord P.fibreCoord L.parameter)
      (fun t => circlePath P.outerRadius (2 * π * t + b)) 0 1 W :=
    IsRootPathWord.circle_unit ⟨K, hK, hW⟩
  obtain ⟨W₀, hW₀⟩ := hZ₀.exists_isRootPathWord
    (γ := fun t => circlePath P.outerRadius (2 * π * t + b)) zero_lt_one
    ((continuous_circlePath _).comp (by fun_prop)).continuousOn fun t _ => hcircle _
  obtain ⟨Wr, hWr⟩ := exists_isPathWord (K := y) (u := b) (v := b + 2 * π)
    (by linarith [Real.pi_pos]) (fun k => (hy.continuousOn k).mono (subset_univ _))
    (fun t _ => hy.injective t (mem_univ _))
  have hWr' : IsRootPathWord Z₀ (fun t => circlePath r (2 * π * t + b)) 0 1 Wr :=
    IsRootPathWord.circle_unit ⟨y, hy.mono (subset_univ _), hWr⟩
  have hJ := (hyrep b).signedBraidConj hWr
  have hdef : SignedBraidConj W₀ W :=
    signedBraidConj_deformation (Z₂ := levelRootsAt A L.radius P.baseCoord P.fibreCoord) hZs ha
      hW₀ hWs
  have hcen : SignedBraidConj Wr W₀ :=
    signedBraidConj_central hZ₀ hr hrδ hρ₂ hP.outerRadius_lt hWr' hW₀
  exact hdef.symm.trans (hcen.symm.trans hJ)

end LevelProjectionSetup

end OnLeConjecture.Analytic
