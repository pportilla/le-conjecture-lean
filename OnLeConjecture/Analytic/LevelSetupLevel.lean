/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupCentral
public import OnLeConjecture.Analytic.LevelSetupLabels
public import OnLeConjecture.Analytic.LevelOuterBraid
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.DerivedSet

/-!
# Finite fibres and finitely many critical values of a level

Let `v = H₀`, `h` a base coordinate and `ζ` a fibre coordinate of the target. For a level
`Lev = {x ∈ B_R | v x = s}` on which `dv` does not vanish, with `H` analytic on `B̄_R` and
injective on `B_R`, and with no point of the sphere `∂B_R` on the level over the closed disc
`B̄(0, ρ)` (`LevelBall A R s h ρ`):

* `LevelBall.isCompact_locus`: the part of the level over `B̄(0, ρ)` is compact;
* `LevelBall.exists_chart`: near each point of the level, the level is a holomorphic disc `γ`,
  and the differential of `x ↦ (v x, h (H x))` is injective at `γ t` exactly when
  `(h ∘ H ∘ γ)'(t) ≠ 0`;
* `LevelBall.finite_fibre`: the fibres over `B̄(0, ρ)` are finite. An accumulation point of a
  fibre would make `h ∘ H` constant on a disc of the level. The accumulation points then form a
  compact set containing a disc around each of its points, and the maximum modulus principle
  for `ζ ∘ H` along such a disc contradicts the injectivity of `H`;
* `LevelBall.finite_critical`: the critical points of `x ↦ (v x, h (H x))` on the level over
  `B̄(0, ρ)` are finite. An accumulation point would make `(h ∘ H ∘ γ)'` vanish identically,
  hence a fibre infinite.

These are the statements "Its fibres are compact analytic subsets and hence finite" and "On each
compact smooth level, `h` is nonconstant on each component because its fibres are finite. Its
critical points are therefore isolated and finite" of Section 3 of the written proof of
Statement E (`statement-E-complete-proof.tex`).

Finally, `LevelProjectionSetup.rootFamilyHolds_of_admissible` proves the field (A)
`RootFamilyHolds` of a setup from the hypotheses `OuterAdmissible` of the outer braid, the
boundary condition over `B̄(0, ρ)`, and the regularity of the fibres over `B(0, ρ) \ V`. The number
of roots is computed over the outer circle at the level `s` by the deformation from the central
level (`isRootFamily_central`, `isRootFamily_deformation` of `LevelOuterBraid.lean`).
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The kernel of a nonzero linear form on `ℂ²` is spanned by each of its nonzero vectors. -/
theorem exists_eq_smul_of_mem_ker {L : Source 2 →L[ℂ] ℂ} (hL : L ≠ 0) {b : Source 2}
    (hb0 : b ≠ 0) (hb : L b = 0) {a : Source 2} (ha : L a = 0) : ∃ c : ℂ, a = c • b := by
  have hrange : LinearMap.range (L : Source 2 →ₗ[ℂ] ℂ) = ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
      by_contra h
      push Not at h
      exact hL (ContinuousLinearMap.ext h)
    rw [eq_top_iff]
    intro w _
    refine ⟨(w / L v) • v, ?_⟩
    simp [hv]
  have hker : Module.finrank ℂ (LinearMap.ker (L : Source 2 →ₗ[ℂ] ℂ)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (L : Source 2 →ₗ[ℂ] ℂ)
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    omega
  have hspan : Submodule.span ℂ {b} = LinearMap.ker (L : Source 2 →ₗ[ℂ] ℂ) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hb
    · rw [finrank_span_singleton hb0, hker]
  have hmem : a ∈ Submodule.span ℂ {b} := by
    rw [hspan]
    exact ha
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The hypotheses on a level used for the finiteness statements: `H` is analytic on `B̄_R` and
injective on `B_R`, `dv` does not vanish on the level `v = s` in `B_R`, and no point of the
sphere `∂B_R` on the level lies over the closed disc `B̄(0, ρ)`. -/
structure LevelBall (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (s : ℂ)
    (h : Source 3 →L[ℂ] ℂ) (ρ : ℝ) : Prop where
  radius_pos : 0 < R
  analyticAt : ∀ x ∈ closedBall (0 : Source 2) R, AnalyticAt ℂ A.H x
  injOn : InjOn A.H (ball (0 : Source 2) R)
  regular : ∀ x ∈ ball (0 : Source 2) R, A.H x 0 = s → fderiv ℂ (fun y => A.H y 0) x ≠ 0
  boundary : ∀ x : Source 2, ‖x‖ = R → A.H x 0 = s → ρ < ‖h (A.H x)‖

namespace LevelBall

variable {A : ResolutionSectionAssembly g hd hi} {R : ℝ} {s : ℂ} {h : Source 3 →L[ℂ] ℂ} {ρ : ℝ}
  (hB : LevelBall A R s h ρ)

/-- The part of the level over the closed disc `B̄(0, ρ)`. -/
def locus (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (s : ℂ) (h : Source 3 →L[ℂ] ℂ)
    (ρ : ℝ) : Set (Source 2) :=
  {x | x ∈ ball (0 : Source 2) R ∧ A.H x 0 = s ∧ h (A.H x) ∈ closedBall (0 : ℂ) ρ}

/-- The fibre of the level over `c`. -/
def fibre (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (s : ℂ) (h : Source 3 →L[ℂ] ℂ)
    (c : ℂ) : Set (Source 2) :=
  {x | x ∈ ball (0 : Source 2) R ∧ A.H x 0 = s ∧ h (A.H x) = c}

include hB

theorem continuousOn_H : ContinuousOn A.H (closedBall (0 : Source 2) R) := fun x hx =>
  (hB.analyticAt x hx).continuousAt.continuousWithinAt

theorem mem_ball_of_mem_closedBall {x : Source 2} (hx : x ∈ closedBall (0 : Source 2) R)
    (hxs : A.H x 0 = s) (hxρ : ‖h (A.H x)‖ ≤ ρ) : x ∈ ball (0 : Source 2) R := by
  rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
  · exact mem_ball_zero_iff.mpr hlt
  · exact absurd hxρ (not_le.mpr (hB.boundary x heq hxs))

theorem locus_eq : locus A R s h ρ = closedBall (0 : Source 2) R ∩
    ((fun x => A.H x 0) ⁻¹' {s} ∩ (fun x => h (A.H x)) ⁻¹' closedBall (0 : ℂ) ρ) := by
  ext x
  constructor
  · rintro ⟨hx, hxs, hxρ⟩
    exact ⟨ball_subset_closedBall hx, hxs, hxρ⟩
  · rintro ⟨hx, hxs, hxρ⟩
    exact ⟨hB.mem_ball_of_mem_closedBall hx hxs (mem_closedBall_zero_iff.mp hxρ), hxs, hxρ⟩

/-- The part of the level over `B̄(0, ρ)` is compact. -/
theorem isCompact_locus : IsCompact (locus A R s h ρ) := by
  rw [hB.locus_eq]
  have hv : ContinuousOn (fun x => A.H x 0) (closedBall (0 : Source 2) R) :=
    (continuous_apply 0).comp_continuousOn hB.continuousOn_H
  have hφ : ContinuousOn (fun x => h (A.H x)) (closedBall (0 : Source 2) R) :=
    h.continuous.comp_continuousOn hB.continuousOn_H
  have h1 := hv.preimage_isClosed_of_isClosed isClosed_closedBall (isClosed_singleton (x := s))
  have hcl := (hφ.mono inter_subset_left).preimage_isClosed_of_isClosed h1
    (isClosed_closedBall (x := (0 : ℂ)) (ε := ρ))
  rw [inter_assoc] at hcl
  exact (isCompact_closedBall (0 : Source 2) R).of_isClosed_subset hcl inter_subset_left


/-- **The chart of the level at a point.** -/
theorem exists_chart {x : Source 2} (hx : x ∈ ball (0 : Source 2) R) (hxs : A.H x 0 = s) :
    ∃ (γ : ℂ → Source 2) (r : ℝ) (κ : Source 2 →L[ℂ] ℂ) (N : Set (Source 2)),
      0 < r ∧ IsOpen N ∧ x ∈ N ∧ N ⊆ ball (0 : Source 2) R ∧ γ 0 = x ∧
      (∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ γ t ∧ γ t ∈ N ∧ A.H (γ t) 0 = s) ∧
      InjOn γ (ball 0 r) ∧
      (∀ z ∈ N, A.H z 0 = s → κ (z - x) ∈ ball (0 : ℂ) r ∧ γ (κ (z - x)) = z) ∧
      (∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ (fun t => h (A.H (γ t))) t) ∧
      ∀ t ∈ ball (0 : ℂ) r, (Injective (fderiv ℂ (levelBaseMap A h) (γ t)) ↔
        deriv (fun t => h (A.H (γ t))) t ≠ 0) := by
  have hHx : AnalyticAt ℂ A.H x := hB.analyticAt x (ball_subset_closedBall hx)
  have hvan : AnalyticAt ℂ (fun y => A.H y 0) x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt _).comp hHx
  obtain ⟨γ, r, N, hr, hNo, hxN, hNB, hγ0, hγan, hγmem, hγinj, ⟨κ, hκ⟩, hγd, -⟩ :=
    exists_levelCurve hvan (hB.regular x hx hxs) (isOpen_ball.mem_nhds hx)
  rw [hxs] at hγmem hκ
  have hHγ : ∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ A.H (γ t) := fun t ht =>
    hB.analyticAt _ (ball_subset_closedBall (hNB (hγmem t ht).1))
  have hfan : ∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ (fun t => h (A.H (γ t))) t := fun t ht =>
    (h.analyticAt _).comp ((hHγ t ht).comp (hγan t ht))
  refine ⟨γ, r, κ, N, hr, hNo, hxN, hNB, hγ0, fun t ht => ⟨hγan t ht, hγmem t ht⟩, hγinj, hκ,
    hfan, fun t ht => ?_⟩
  obtain ⟨hγ'0, hdvγ⟩ := hγd t ht
  have hderiv : deriv (fun t => h (A.H (γ t))) t =
      fderiv ℂ (fun y => h (A.H y)) (γ t) (deriv γ t) := by
    have h1 : HasFDerivAt (fun y => h (A.H y)) (fderiv ℂ (fun y => h (A.H y)) (γ t)) (γ t) :=
      ((h.analyticAt _).comp (hHγ t ht)).differentiableAt.hasFDerivAt
    exact (h1.comp_hasDerivAt t (hγan t ht).differentiableAt.hasDerivAt).deriv
  constructor
  · intro hinj hzero
    apply hγ'0
    apply hinj
    rw [fderiv_levelBaseMap_apply A h (hHγ t ht), map_zero, hdvγ, ← hderiv, hzero]
    rfl
  · intro hne
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [fderiv_levelBaseMap_apply A h (hHγ t ht)] at ha
    have hav : fderiv ℂ (fun y => A.H y 0) (γ t) a = 0 := congrArg Prod.fst ha
    have haφ : fderiv ℂ (fun y => h (A.H y)) (γ t) a = 0 := congrArg Prod.snd ha
    have hreg := hB.regular (γ t) (hNB (hγmem t ht).1) (hγmem t ht).2
    obtain ⟨c, rfl⟩ := exists_eq_smul_of_mem_ker hreg hγ'0 hdvγ hav
    rw [map_smul, smul_eq_mul, ← hderiv] at haφ
    rw [(mul_eq_zero.mp haφ).resolve_right hne, zero_smul]

omit hB in
theorem fibre_subset_locus {c : ℂ} (hc : c ∈ closedBall (0 : ℂ) ρ) :
    fibre A R s h c ⊆ locus A R s h ρ := by
  rintro x ⟨hx, hxs, hxc⟩
  exact ⟨hx, hxs, by rw [hxc]; exact hc⟩

theorem isCompact_fibre {c : ℂ} (hc : c ∈ closedBall (0 : ℂ) ρ) :
    IsCompact (fibre A R s h c) := by
  refine hB.isCompact_locus.of_isClosed_subset ?_ (fibre_subset_locus hc)
  have hφ : ContinuousOn (fun x => h (A.H x)) (locus A R s h ρ) :=
    h.continuous.comp_continuousOn (hB.continuousOn_H.mono fun x hx => ball_subset_closedBall hx.1)
  have hcl := hφ.preimage_isClosed_of_isClosed hB.isCompact_locus.isClosed
    (isClosed_singleton (x := c))
  convert hcl using 1
  ext x
  constructor
  · intro hx
    exact ⟨fibre_subset_locus hc hx, hx.2.2⟩
  · rintro ⟨⟨hx, hxs, -⟩, hxc⟩
    exact ⟨hx, hxs, hxc⟩

/-- **The fibres of the level over `B̄(0, ρ)` are finite.** -/
theorem finite_fibre {ζ : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, h y, ζ y)) {c : ℂ}
    (hc : c ∈ closedBall (0 : ℂ) ρ) : (fibre A R s h c).Finite := by
  by_contra hinf
  set K := fibre A R s h c with hKdef
  have hKc : IsCompact K := hB.isCompact_fibre hc
  set D := derivedSet K with hDdef
  have hDK : D ⊆ K := (derivedSet_subset_closure K).trans hKc.isClosed.closure_subset
  obtain ⟨x₁, -, hx₁⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hKc subset_rfl
  have hDne : D.Nonempty := ⟨x₁, hx₁⟩
  have hDc : IsCompact D := hKc.of_isClosed_subset (isClosed_derivedSet K) hDK
  -- around every accumulation point, a disc of the level lies in `D`
  have hdisc : ∀ x ∈ D, ∃ (γ : ℂ → Source 2) (r : ℝ), 0 < r ∧ γ 0 = x ∧
      (∀ t ∈ ball (0 : ℂ) r, AnalyticAt ℂ γ t ∧ γ t ∈ D) ∧ InjOn γ (ball 0 r) := by
    intro x hxD
    obtain ⟨hx, hxs, hxc⟩ := hDK hxD
    obtain ⟨γ, r, κ, N, hr, hNo, hxN, hNB, hγ0, hγ, hγinj, hκ, hfan, -⟩ := hB.exists_chart hx hxs
    -- zeros of `h ∘ H ∘ γ - c` accumulate at `0`
    have hF : AnalyticAt ℂ (fun t => h (A.H (γ t)) - c) 0 :=
      (hfan 0 (mem_ball_self hr)).sub analyticAt_const
    have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), h (A.H (γ t)) - c = 0 := by
      intro hev
      obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.eventually_nhds_iff_ball.mp
        (eventually_nhdsWithin_iff.mp hev)
      have hNx : N ∩ (fun z => κ (z - x)) ⁻¹' ball 0 r₁ ∈ 𝓝 x := by
        refine inter_mem (hNo.mem_nhds hxN) ?_
        apply ContinuousAt.preimage_mem_nhds (by fun_prop)
        simpa using ball_mem_nhds (0 : ℂ) hr₁
      have hacc := (accPt_iff_frequently.mp hxD)
      obtain ⟨z, ⟨hzx, hzK⟩, hzN, hzr⟩ := (hacc.and_eventually hNx).exists
      obtain ⟨hzr', hγz⟩ := hκ z hzN hzK.2.1
      have ht0 : κ (z - x) ≠ 0 := by
        intro h0
        rw [h0, hγ0] at hγz
        exact hzx hγz.symm
      have hne : h (A.H (γ (κ (z - x)))) - c ≠ 0 := hr₁b _ hzr ht0
      rw [hγz, hzK.2.2, sub_self] at hne
      exact hne rfl
    have hev := hF.frequently_zero_iff_eventually_zero.mp hfreq
    obtain ⟨r₂, hr₂, hr₂b⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set r' := min r r₂ with hr'def
    have hr' : 0 < r' := lt_min hr hr₂
    have hγK : ∀ t ∈ ball (0 : ℂ) r', γ t ∈ K := by
      intro t ht
      have htr : t ∈ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _) ht
      obtain ⟨-, hγN, hγs⟩ := hγ t htr
      exact ⟨hNB hγN, hγs, sub_eq_zero.mp (hr₂b t (ball_subset_ball (min_le_right _ _) ht))⟩
    refine ⟨γ, r', hr', hγ0, fun t ht => ⟨(hγ t (ball_subset_ball (min_le_left _ _) ht)).1, ?_⟩,
      hγinj.mono (ball_subset_ball (min_le_left _ _))⟩
    -- `γ t` is an accumulation point of `K`
    have hγc : ContinuousAt γ t := (hγ t (ball_subset_ball (min_le_left _ _) ht)).1.continuousAt
    have htend : Tendsto γ (𝓝[≠] t) (𝓝 (γ t)) := hγc.tendsto.mono_left nhdsWithin_le_nhds
    rw [hDdef, mem_derivedSet, accPt_iff_frequently]
    refine htend.frequently (Filter.Eventually.frequently ?_)
    have hball : ∀ᶠ t' in 𝓝[≠] t, t' ∈ ball (0 : ℂ) r' ∧ t' ≠ t :=
      (eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds ht)).and
        self_mem_nhdsWithin
    filter_upwards [hball] with t' ⟨ht', hne⟩
    refine ⟨fun heq => hne (hγinj (ball_subset_ball (min_le_left _ _) ht')
      (ball_subset_ball (min_le_left _ _) ht) heq), hγK t' ht'⟩
  -- the maximum of `|ζ ∘ H|` on `D`
  have hζc : ContinuousOn (fun x => ‖ζ (A.H x)‖) D :=
    (continuous_norm.comp ζ.continuous).comp_continuousOn
      (hB.continuousOn_H.mono fun x hx => ball_subset_closedBall (hDK hx).1)
  obtain ⟨x₀, hx₀D, hmax⟩ := hDc.exists_isMaxOn hDne hζc
  obtain ⟨γ, r, hr, hγ0, hγ, hγinj⟩ := hdisc x₀ hx₀D
  have hlocmax : IsLocalMax (norm ∘ fun t => ζ (A.H (γ t))) 0 := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
    have h1 := hmax (hγ t ht).2
    simp only [comp_apply, hγ0]
    exact h1
  have hdiff : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun t => ζ (A.H (γ t))) t := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht
    have hHγ : AnalyticAt ℂ A.H (γ t) :=
      hB.analyticAt _ (ball_subset_closedBall (hDK (hγ t ht).2).1)
    exact ((ζ.analyticAt _).comp (hHγ.comp (hγ t ht).1)).differentiableAt
  have hconst := Complex.eventually_eq_of_isLocalMax_norm hdiff hlocmax
  obtain ⟨t, ⟨hteq, ht⟩, ht0⟩ := ((hconst.and (ball_mem_nhds (0 : ℂ) hr)).filter_mono
    nhdsWithin_le_nhds |>.and self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℂ))
  have hγtK := hDK (hγ t ht).2
  have hx₀K := hDK hx₀D
  have hHeq : A.H (γ t) = A.H (γ 0) := by
    apply hcoord
    rw [hγ0]
    simp only [hγtK.2.1, hx₀K.2.1, hγtK.2.2, hx₀K.2.2]
    rw [hγ0] at hteq
    simp only [hteq]
  rw [hγ0] at hHeq
  have hγt0 := hB.injOn hγtK.1 hx₀K.1 hHeq
  rw [← hγ0] at hγt0
  exact ht0 (hγinj ht (mem_ball_self hr) hγt0)

/-- The critical points of `x ↦ (v x, h (H x))` on the part of the level over `B̄(0, ρ)`. -/
def criticalLocus (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (s : ℂ)
    (h : Source 3 →L[ℂ] ℂ) (ρ : ℝ) : Set (Source 2) :=
  {x | x ∈ locus A R s h ρ ∧ ¬ Injective (fderiv ℂ (levelBaseMap A h) x)}

/-- **The critical points of the level over `B̄(0, ρ)` are finite.** -/
theorem finite_criticalLocus {ζ : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, h y, ζ y)) :
    (criticalLocus A R s h ρ).Finite := by
  -- the injectivity locus is open
  set I : Set (Source 2) :=
    {x | x ∈ ball (0 : Source 2) R ∧ Injective (fderiv ℂ (levelBaseMap A h) x)} with hIdef
  have hIo : IsOpen I := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hx, hxinj⟩
    have hHx : AnalyticAt ℂ A.H x := hB.analyticAt x (ball_subset_closedBall hx)
    filter_upwards [isOpen_ball.mem_nhds hx,
      eventually_injective_fderiv (levelBaseMap_analyticAt A h hHx) hxinj] with y hy hyinj
    exact ⟨hy, hyinj⟩
  have hCeq : criticalLocus A R s h ρ = locus A R s h ρ \ I := by
    ext x
    constructor
    · rintro ⟨hxL, hxni⟩
      exact ⟨hxL, fun hxI => hxni hxI.2⟩
    · rintro ⟨hxL, hxI⟩
      exact ⟨hxL, fun hinj => hxI ⟨hxL.1, hinj⟩⟩
  have hCc : IsCompact (criticalLocus A R s h ρ) := by
    rw [hCeq]
    exact hB.isCompact_locus.diff hIo
  by_contra hinf
  obtain ⟨x, hxC, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hCc subset_rfl
  obtain ⟨⟨hx, hxs, hxρ⟩, -⟩ := hxC
  obtain ⟨γ, r, κ, N, hr, hNo, hxN, hNB, hγ0, hγ, hγinj, hκ, hfan, hcrit⟩ := hB.exists_chart hx hxs
  -- the derivative of `h ∘ H ∘ γ` has zeros accumulating at `0`
  have hd : AnalyticAt ℂ (deriv fun t => h (A.H (γ t))) 0 := (hfan 0 (mem_ball_self hr)).deriv
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), deriv (fun t => h (A.H (γ t))) t = 0 := by
    intro hev
    obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hev)
    have hNx : N ∩ (fun z => κ (z - x)) ⁻¹' ball 0 (min r₁ r) ∈ 𝓝 x := by
      refine inter_mem (hNo.mem_nhds hxN) ?_
      apply ContinuousAt.preimage_mem_nhds (by fun_prop)
      simpa using ball_mem_nhds (0 : ℂ) (lt_min hr₁ hr)
    obtain ⟨z, ⟨hzx, hzC⟩, hzN, hzr⟩ := ((accPt_iff_frequently.mp hacc).and_eventually hNx).exists
    obtain ⟨hzr', hγz⟩ := hκ z hzN hzC.1.2.1
    have ht0 : κ (z - x) ≠ 0 := by
      intro h0
      rw [h0, hγ0] at hγz
      exact hzx hγz.symm
    have hne : deriv (fun t => h (A.H (γ t))) (κ (z - x)) ≠ 0 :=
      hr₁b _ (ball_subset_ball (min_le_left _ _) hzr) ht0
    apply hzC.2
    rw [← hγz]
    exact (hcrit _ hzr').mpr hne
  have hev := hd.frequently_zero_iff_eventually_zero.mp hfreq
  obtain ⟨r₂, hr₂, hr₂b⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set r' := min r r₂ with hr'def
  have hr' : 0 < r' := lt_min hr hr₂
  have hconst : ∀ t ∈ ball (0 : ℂ) r', h (A.H (γ t)) = h (A.H (γ 0)) := by
    intro t ht
    refine isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r').isPreconnected
      (fun t' ht' => (hfan t' (ball_subset_ball (min_le_left _ _) ht')).differentiableAt
        |>.differentiableWithinAt) (fun t' ht' => hr₂b t' (ball_subset_ball (min_le_right _ _) ht'))
      ht (mem_ball_self hr')
  -- an infinite fibre
  have hsub : γ '' ball (0 : ℂ) r' ⊆ fibre A R s h (h (A.H x)) := by
    rintro _ ⟨t, ht, rfl⟩
    have htr : t ∈ ball (0 : ℂ) r := ball_subset_ball (min_le_left _ _) ht
    obtain ⟨-, hγN, hγs⟩ := hγ t htr
    refine ⟨hNB hγN, hγs, ?_⟩
    rw [hconst t ht, hγ0]
  have hinfim : (γ '' ball (0 : ℂ) r').Infinite :=
    Set.Infinite.image (hγinj.mono (ball_subset_ball (min_le_left _ _)))
      (infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 hr'))
  exact hinfim ((hB.finite_fibre hcoord hxρ).subset hsub)

/-- The critical values of `h ∘ H` on the level over the open disc `B(0, ρ)`. -/
def criticalValues (A : ResolutionSectionAssembly g hd hi) (R : ℝ) (s : ℂ)
    (h : Source 3 →L[ℂ] ℂ) (ρ : ℝ) : Set ℂ :=
  {c | c ∈ ball (0 : ℂ) ρ ∧ ∃ x ∈ fibre A R s h c, ¬ Injective (fderiv ℂ (levelBaseMap A h) x)}

/-- **There are finitely many critical values.** -/
theorem finite_criticalValues {ζ : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, h y, ζ y)) :
    (criticalValues A R s h ρ).Finite := by
  refine ((hB.finite_criticalLocus hcoord).image fun x => h (A.H x)).subset ?_
  rintro c ⟨hc, x, ⟨hx, hxs, hxc⟩, hni⟩
  exact ⟨x, ⟨⟨hx, hxs, by rw [hxc]; exact ball_subset_closedBall hc⟩, hni⟩, hxc⟩

end LevelBall

/-! ### Connectedness of discs and squares minus finitely many points -/

/-- A disc minus a countable set is preconnected. -/
theorem isPreconnected_ball_diff_countable {ρ : ℝ} (hρ : 0 < ρ) {V : Set ℂ} (hV : V.Countable) :
    IsPreconnected (ball (0 : ℂ) ρ \ V) := by
  set Ψ : ℂ → ℂ := fun z => ((ρ / (1 + ‖z‖) : ℝ) : ℂ) * z with hΨ
  set Φ : ℂ → ℂ := fun w => ((1 / (ρ - ‖w‖) : ℝ) : ℂ) * w with hΦ
  have hpos : ∀ z : ℂ, 0 < 1 + ‖z‖ := fun z => by positivity
  have hΨc : Continuous Ψ := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_id
    exact continuous_const.div (continuous_const.add continuous_norm) fun z => (hpos z).ne'
  have hnormΨ : ∀ z, ‖Ψ z‖ = ρ * ‖z‖ / (1 + ‖z‖) := by
    intro z
    rw [hΨ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hρ (hpos z))]
    ring
  have hΨball : ∀ z, Ψ z ∈ ball (0 : ℂ) ρ := by
    intro z
    rw [mem_ball_zero_iff, hnormΨ, div_lt_iff₀ (hpos z)]
    nlinarith [norm_nonneg z]
  have hΦΨ : ∀ z, Φ (Ψ z) = z := by
    intro z
    have hden : ρ - ‖Ψ z‖ = ρ / (1 + ‖z‖) := by
      rw [hnormΨ]
      field_simp
      ring
    rw [hΦ]
    simp only
    rw [hden, hΨ]
    simp only
    rw [← mul_assoc, ← Complex.ofReal_mul]
    have h1 : 1 / (ρ / (1 + ‖z‖)) * (ρ / (1 + ‖z‖)) = 1 := by
      field_simp
    rw [h1, Complex.ofReal_one, one_mul]
  have hΨΦ : ∀ w ∈ ball (0 : ℂ) ρ, Ψ (Φ w) = w := by
    intro w hw
    have hw' : ‖w‖ < ρ := mem_ball_zero_iff.mp hw
    have hd : 0 < ρ - ‖w‖ := by linarith
    have hnΦ : ‖Φ w‖ = ‖w‖ / (ρ - ‖w‖) := by
      rw [hΦ]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hd)]
      ring
    rw [hΨ]
    simp only
    rw [hnΦ]
    have h1 : ρ / (1 + ‖w‖ / (ρ - ‖w‖)) = ρ - ‖w‖ := by
      field_simp
      ring
    rw [h1, hΦ]
    simp only
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_one_div_cancel hd.ne', Complex.ofReal_one, one_mul]
  have hW : (Φ '' (V ∩ ball 0 ρ)).Countable := (hV.mono inter_subset_left).image Φ
  have hpc : IsPathConnected (Φ '' (V ∩ ball 0 ρ))ᶜ :=
    hW.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have himage : Ψ '' (Φ '' (V ∩ ball 0 ρ))ᶜ = ball (0 : ℂ) ρ \ V := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hΨball z, fun hV' => hz ⟨Ψ z, ⟨hV', hΨball z⟩, hΦΨ z⟩⟩
    · rintro ⟨hw, hwV⟩
      refine ⟨Φ w, ?_, hΨΦ w hw⟩
      rintro ⟨w', ⟨hw'V, hw'b⟩, heq⟩
      apply hwV
      have := congrArg Ψ heq
      rw [hΨΦ w' hw'b, hΨΦ w hw] at this
      rw [← this]
      exact hw'V
  rw [← himage]
  exact (hpc.image hΨc).isConnected.isPreconnected

/-- A closed square minus a countable subset of the open square is preconnected. -/
theorem isPreconnected_baseSquare_diff_countable {a : ℝ} (ha : 0 < a) {V : Set ℂ}
    (hV : V.Countable) (hVsq : ∀ c ∈ V, c.re ∈ Ioo (-a) a ∧ c.im ∈ Ioo (-a) a) :
    IsPreconnected (baseSquare a \ V) := by
  have hsq : ∀ z : ℂ, z ∈ baseSquare a ↔ squareNorm z ≤ a := by
    intro z
    simp only [baseSquare, mem_ofPred_eq, mem_Icc, squareNorm, max_le_iff, abs_le]
  set r : ℂ → ℂ := fun z => ((a / max a (squareNorm z) : ℝ) : ℂ) * z with hr
  have hmax : ∀ z, 0 < max a (squareNorm z) := fun z => lt_max_of_lt_left ha
  have hrc : Continuous r := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_id
    exact continuous_const.div (continuous_const.max continuous_squareNorm) fun z => (hmax z).ne'
  have hrsq : ∀ z, squareNorm (r z) = a * squareNorm z / max a (squareNorm z) := by
    intro z
    have h := squareNorm_smul_of_nonneg (div_pos ha (hmax z)).le z
    rw [hr]
    simp only
    rw [h]
    ring
  have hrfix : ∀ z, squareNorm z ≤ a → r z = z := by
    intro z hz
    rw [hr]
    simp only
    rw [max_eq_left hz, div_self ha.ne', Complex.ofReal_one, one_mul]
  have himage : r '' Vᶜ = baseSquare a \ V := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      by_cases hzs : squareNorm z ≤ a
      · rw [hrfix z hzs]
        exact ⟨(hsq z).mpr hzs, hz⟩
      · push Not at hzs
        have hval : squareNorm (r z) = a := by
          rw [hrsq, max_eq_right hzs.le, mul_div_assoc, div_self (by linarith), mul_one]
        refine ⟨(hsq _).mpr hval.le, fun hVr => ?_⟩
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hVsq _ hVr
        have : squareNorm (r z) < a := by
          simp only [squareNorm]
          exact max_lt (abs_lt.mpr ⟨h1, h2⟩) (abs_lt.mpr ⟨h3, h4⟩)
        linarith
    · rintro ⟨hw, hwV⟩
      exact ⟨w, hwV, hrfix w ((hsq w).mp hw)⟩
  have hpc : IsPathConnected Vᶜ :=
    hV.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  rw [← himage]
  exact (hpc.image hrc).isConnected.isPreconnected

/-- A point of the open square `(-a, a)²` has norm less than `√2 a`. -/
theorem norm_lt_of_mem_openSquare {a : ℝ} {c : ℂ} (hc : c.re ∈ Ioo (-a) a ∧ c.im ∈ Ioo (-a) a) :
    ‖c‖ < √2 * a := by
  have ha : 0 < a := by linarith [hc.1.1, hc.1.2]
  have hre : c.re ^ 2 < a ^ 2 := by nlinarith [hc.1.1, hc.1.2]
  have him : c.im ^ 2 < a ^ 2 := by nlinarith [hc.2.1, hc.2.2]
  have hn : ‖c‖ ^ 2 < (√2 * a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hn

/-! ### The field (A) -/

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}

theorem outerRadius_pos (P : LevelProjectionSetup A L) : 0 < P.outerRadius := by
  have h1 := P.square_pos
  have h2 := P.square_le
  have h3 : 0 < √2 / 2 := by positivity
  by_contra hneg
  have hneg' : P.outerRadius ≤ 0 := le_of_not_gt hneg
  nlinarith

/-- The base point `ρ₂` of the outer circle is not a critical value. -/
theorem outerRadius_not_mem_critical (P : LevelProjectionSetup A L) :
    (P.outerRadius : ℂ) ∉ P.critical := by
  intro hc
  have h := norm_lt_of_mem_openSquare (P.critical_mem _ hc)
  have h2 := P.square_le
  have hsq : √2 * (√2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hρ₂ : 0 < P.outerRadius := by
    have h1 := P.square_pos
    nlinarith [Real.sqrt_nonneg 2]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ₂] at h
  nlinarith [Real.sqrt_nonneg 2]

/-- **The number of roots over the outer circle** of an admissible setup is `S`. -/
theorem ncard_levelRootsAt_outer (P : LevelProjectionSetup A L) (hP : P.OuterAdmissible) :
    (levelRootsAt A L.radius P.baseCoord P.fibreCoord L.parameter
      (circlePath P.outerRadius 0)).ncard = A.squareSum := by
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
  obtain ⟨w, -, -, hsmall⟩ :=
    exists_centralRootBraid A hR P.coordinates hHc hP.transverse hP.isolated
  set Z₀ := levelRootsAt A L.radius P.baseCoord P.fibreCoord 0 with hZ₀def
  obtain ⟨r, hr, hrδ, y, hy, -⟩ := hsmall hP.centralDisc hδ
  have hcount₀ : (Z₀ (circlePath r 0)).ncard = A.squareSum := by
    rw [← hy.range_eq 0 (mem_univ _)]
    exact ncard_range_fin (hy.injective 0 (mem_univ _))
  have hZ₀ : IsRootFamily Z₀ A.squareSum {c | 0 < ‖c‖ ∧ ‖c‖ < hP.centralDisc} :=
    isRootFamily_central A P.coordinates L.injective hP.analyticAt hP.central_boundary
      hP.central_unramified (c₀ := circlePath r 0) (by rw [norm_circlePath hr.le]; exact hr)
      (by rw [norm_circlePath hr.le]; exact hrδ) hcount₀
  have hcircle : circlePath P.outerRadius 0 ∈ {c | 0 < ‖c‖ ∧ ‖c‖ < hP.centralDisc} := by
    change 0 < ‖circlePath P.outerRadius 0‖ ∧ ‖circlePath P.outerRadius 0‖ < hP.centralDisc
    rw [norm_circlePath hρ₂.le]
    exact ⟨hρ₂, hP.outerRadius_lt⟩
  have hs := L.parameter_ne_zero
  have hsn : 0 < ‖L.parameter‖ := norm_pos_iff.mpr hs
  have hη : 0 < hP.levelDisc := (norm_nonneg _).trans_lt hP.parameter_lt
  have hcountρ : (Z₀ (circlePath P.outerRadius 0)).ncard = A.squareSum := by
    obtain ⟨g', hg', hg'Z⟩ := hZ₀.exists_labels_at hcircle
    rw [hg'Z]
    exact ncard_range_fin hg'
  have hZs := isRootFamily_deformation A hs hη hρ₂.le P.coordinates L.injective hP.analyticAt
    hP.outer_boundary hP.outer_unramified hcountρ
  have h1 : (1 : ℂ) ∈ Complex.re ⁻¹' Ioo (-(hP.levelDisc / ‖L.parameter‖))
      (hP.levelDisc / ‖L.parameter‖) := by
    have hlt : 1 < hP.levelDisc / ‖L.parameter‖ := (one_lt_div hsn).mpr hP.parameter_lt
    simp only [mem_preimage, Complex.one_re, mem_Ioo]
    constructor <;> linarith
  obtain ⟨g', hg', hg'Z⟩ := hZs.exists_labels_at h1
  simp only [Complex.one_re, Complex.ofReal_one, one_mul, Complex.one_im] at hg'Z
  rw [hg'Z]
  exact ncard_range_fin hg'

/-- **The field (A).** For an admissible setup whose level has no point of the sphere `∂B_R`
over the closed disc `B̄(0, ρ)` and whose fibres over `B(0, ρ) \ V` are unramified, the roots
form a root family of `S` points over `B(0, ρ) \ V`. -/
theorem rootFamilyHolds_of_admissible (P : LevelProjectionSetup A L) (hP : P.OuterAdmissible)
    (hbd : ∀ x : Source 2, ‖x‖ = L.radius → A.H x 0 = L.parameter →
      P.radius < ‖P.baseCoord (A.H x)‖)
    (hcrit : ∀ c ∈ ball (0 : ℂ) P.radius, c ∉ P.critical → ∀ x ∈ P.levelFibre c,
      Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)) :
    P.RootFamilyHolds := by
  set U : Set ℂ := ball (0 : ℂ) P.radius \ ↑P.critical with hUdef
  have hUo : IsOpen U := isOpen_ball.sdiff P.critical.finite_toSet.isClosed
  have hUc : IsPreconnected U :=
    isPreconnected_ball_diff_countable (P.outerRadius_pos.trans P.outerRadius_lt)
      P.critical.finite_toSet.countable
  set Φ := levelBaseMap A P.baseCoord with hΦdef
  set ψ : Source 2 → ℂ := fun x => P.fibreCoord (A.H x) with hψdef
  set γ : ℂ → ℂ × ℂ := fun w => (L.parameter, w) with hγdef
  have hγc : ContinuousOn γ U := (continuous_const.prodMk continuous_id).continuousOn
  have hΦc := continuousOn_levelBaseMap A P.baseCoord hP.analyticAt
  have hψc := continuousOn_fibreCoord A P.fibreCoord hP.analyticAt
  have hΦeq : ∀ x w, Φ x = γ w ↔ A.H x 0 = L.parameter ∧ P.baseCoord (A.H x) = w := by
    intro x w
    simp only [hΦdef, levelBaseMap, hγdef, Prod.mk.injEq]
  have hint : ∀ w ∈ U, ∀ x ∈ closedBall (0 : Source 2) L.radius, Φ x = γ w →
      x ∈ ball (0 : Source 2) L.radius := by
    intro w hw x hx hxw
    obtain ⟨hxs, hxc⟩ := (hΦeq x w).mp hxw
    rcases (mem_closedBall_zero_iff.mp hx).lt_or_eq with hlt | heq
    · exact mem_ball_zero_iff.mpr hlt
    · have h1 := hbd x heq hxs
      rw [hxc] at h1
      exact absurd (mem_ball_zero_iff.mp hw.1) (not_lt.mpr h1.le)
  have hloc : ∀ w ∈ U, ∀ x ∈ ball (0 : Source 2) L.radius, Φ x = γ w →
      ∃ (V : Set (Source 2)) (T : Set (ℂ × ℂ)) (ψ' : ℂ × ℂ → Source 2),
        IsLocalInverse Φ V T ψ' ∧ x ∈ V := by
    intro w hw x hx hxw
    obtain ⟨hxs, hxc⟩ := (hΦeq x w).mp hxw
    exact exists_isLocalInverse_levelBaseMap A P.baseCoord
      (hP.analyticAt x (ball_subset_closedBall hx)) (hcrit w hw.1 hw.2 x ⟨hx, hxs, hxc⟩)
  have hinj : ∀ w ∈ U, ∀ x ∈ ball (0 : Source 2) L.radius, ∀ y ∈ ball (0 : Source 2) L.radius,
      Φ x = γ w → Φ y = γ w → ψ x = ψ y → x = y := by
    intro w _ x hx y hy hxw hyw hxy
    obtain ⟨hxs, hxc⟩ := (hΦeq x w).mp hxw
    obtain ⟨hys, hyc⟩ := (hΦeq y w).mp hyw
    apply P.injOn_level ⟨hx, hxs⟩ ⟨hy, hys⟩
    simp only [Prod.mk.injEq]
    exact ⟨hxc.trans hyc.symm, hxy⟩
  have hw₀ : (P.outerRadius : ℂ) ∈ U := by
    refine ⟨?_, P.outerRadius_not_mem_critical⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos P.outerRadius_pos]
    exact P.outerRadius_lt
  have hfibeq : ∀ w, {x | x ∈ ball (0 : Source 2) L.radius ∧ Φ x = γ w} =
      {x | x ∈ ball (0 : Source 2) L.radius ∧ A.H x 0 = L.parameter ∧
        P.baseCoord (A.H x) = w} := by
    intro w
    ext x
    simp only [mem_ofPred_eq, hΦeq]
  have hcount : {x | x ∈ ball (0 : Source 2) L.radius ∧ Φ x = γ P.outerRadius}.ncard =
      A.squareSum := by
    have h := P.ncard_levelRootsAt_outer hP
    have hc0 : circlePath P.outerRadius 0 = (P.outerRadius : ℂ) := by simp [circlePath]
    rw [hc0, levelRootsAt, Set.InjOn.ncard_image] at h
    · rw [hfibeq]
      exact h
    · rintro x ⟨hx, hxs, hxc⟩ y ⟨hy, hys, hyc⟩ hxy
      apply P.injOn_level ⟨hx, hxs⟩ ⟨hy, hys⟩
      simp only [Prod.mk.injEq]
      exact ⟨hxc.trans hyc.symm, hxy⟩
  have hfam := isRootFamily_of_fibration hUo hUc hγc hΦc hψc hint hloc hinj hw₀ hcount
  have hZ : (fun w => ψ '' {x | x ∈ ball (0 : Source 2) L.radius ∧ Φ x = γ w}) = P.roots := by
    funext w
    rw [hfibeq]
    rfl
  rw [hZ] at hfam
  exact hfam

end LevelProjectionSetup

end OnLeConjecture.Analytic
