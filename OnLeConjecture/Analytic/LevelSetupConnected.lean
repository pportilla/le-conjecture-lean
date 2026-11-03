/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelSetupLevel
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Topology.Sequences

/-!
# Connectedness of the level over the square

Let `P` be a setup with square `Q = [-a, a]²` and critical values `V`. This module proves the
field (D) `ConnectedHolds`: the part `E` of the level `{v = s}` in `B_R` over `Q \ V` is
preconnected (`LevelProjectionSetup.connectedHolds_of`).

The proof is the resultant argument of `PlaneMilnorFibreConnected.lean`, adapted to the level.
Suppose that open sets `U₁`, `U₂` cover `E`, meet it, and do not meet in `E`. For `c ∈ Q \ V` let
`R(c)` be the product of the differences `ζ (H x) - ζ (H y)` over the points `x ∈ U₁`, `y ∈ U₂`
of the fibre over `c`.

* Over a regular value the fibre has local labels (`exists_levelLabels`), and the labels stay in
  `U₁` or `U₂`. Hence the numbers `n₁`, `n₂` of points of the fibres in `U₁`, `U₂` are locally
  constant on `Q \ V`, hence constant and positive, and `R` is continuous on `Q \ V` and
  holomorphic in its interior. It does not vanish, because distinct points of a fibre have
  distinct `ζ`.
* Near a critical value `c`, `|R|` is bounded below (`exists_lowerBound_near_critical`): if
  points of a fibre in `U₁` and in `U₂` had nearly equal `ζ` over values tending to `c`, a
  convergent subsequence would give a point `x*` of the fibre over `c` approached from both
  sides, whereas a punctured disc of the level around `x*` is connected and lies in `E`.
* Hence `1 / R` extends holomorphically across `V` (removable singularities), and the maximum
  modulus principle on the open square gives `|R(c₁)| ≥ min_{∂Q} |R|`. This contradicts the
  hypotheses: distinct roots over `∂Q` are at distance at least `κ`, and the roots over some
  `c₁ ∈ Q \ V` have modulus less than `κ / 2`.

The two quantitative hypotheses (separation over `∂Q` and smallness over `c₁`) are supplied when
the level is chosen close to the central level (Section 3 of the written proof of Statement E,
`statement-E-complete-proof.tex`, subsection "Connectedness of the compact level").
-/

@[expose] public noncomputable section

open Set Function Metric Filter
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

namespace LevelBall

variable {A : ResolutionSectionAssembly g hd hi} {R : ℝ} {s : ℂ} {h : Source 3 →L[ℂ] ℂ} {ρ : ℝ}
  (hB : LevelBall A R s h ρ)

include hB in
/-- **Local labels of a regular fibre of the level.** -/
theorem exists_levelLabels {c : ℂ} (hc : c ∈ closedBall (0 : ℂ) ρ)
    (hreg : ∀ x ∈ fibre A R s h c, Injective (fderiv ℂ (levelBaseMap A h) x)) :
    ∃ Z : Finset (Source 2), (∀ x, x ∈ Z ↔ x ∈ fibre A R s h c) ∧ ∃ r > 0,
      ∃ G : Source 2 → ℂ → Source 2,
      (∀ z ∈ Z, G z c = z ∧ ContinuousOn (G z) (ball c r) ∧ DifferentiableAt ℂ (G z) c) ∧
      ∀ c' ∈ ball c r, (∀ z ∈ Z, G z c' ∈ fibre A R s h c') ∧
        (∀ x ∈ fibre A R s h c', ∃ z ∈ Z, G z c' = x) ∧ InjOn (fun z => G z c') Z := by
  have hK : IsCompact (closedBall (0 : Source 2) R) := isCompact_closedBall 0 R
  have hcont := continuousOn_levelBaseMap A h hB.analyticAt
  have hfr : ∀ x ∈ closedBall (0 : Source 2) R, levelBaseMap A h x = (s, c) →
      x ∈ ball (0 : Source 2) R := by
    intro x hx hxc
    simp only [levelBaseMap, Prod.mk.injEq] at hxc
    exact hB.mem_ball_of_mem_closedBall hx hxc.1
      (by rw [hxc.2]; exact mem_closedBall_zero_iff.mp hc)
  have hreg' : ∀ x ∈ ball (0 : Source 2) R, levelBaseMap A h x = (s, c) →
      ∃ f' : Source 2 ≃L[ℂ] ℂ × ℂ,
        HasStrictFDerivAt (levelBaseMap A h) (f' : Source 2 →L[ℂ] ℂ × ℂ) x := by
    intro x hx hxc
    simp only [levelBaseMap, Prod.mk.injEq] at hxc
    obtain ⟨e, -, he⟩ := exists_hasStrictFDerivAt_equiv
      (levelBaseMap_analyticAt A h (hB.analyticAt x (ball_subset_closedBall hx)))
      (hreg x ⟨hx, hxc.1, hxc.2⟩)
    exact ⟨e, he⟩
  obtain ⟨Z, hZ, r, hr, g', hg'0, hg'⟩ := exists_localLabels hK isOpen_ball ball_subset_closedBall
    hcont hfr hreg'
  have hpair : ∀ c', (s, c') ∈ ball (s, c) r ↔ c' ∈ ball c r := by
    intro c'
    simp [mem_ball, Prod.dist_eq]
  have hpc : Continuous fun c' : ℂ => (s, c') := continuous_const.prodMk continuous_id
  refine ⟨Z, fun x => ?_, r, hr, fun z c' => g' z (s, c'), fun z hz => ?_, fun c' hc' => ?_⟩
  · rw [hZ x]
    simp only [levelBaseMap, Prod.mk.injEq, fibre, mem_ofPred_eq]
  · obtain ⟨h1, h2, h3⟩ := hg'0 z hz
    refine ⟨h1, h2.comp hpc.continuousOn fun c' hc' => (hpair c').mpr hc', ?_⟩
    exact h3.comp c ((differentiableAt_const _).prodMk differentiableAt_id)
  · obtain ⟨h1, h2, h3⟩ := hg' (s, c') ((hpair c').mpr hc')
    refine ⟨fun z hz => ?_, fun x hx => ?_, h3⟩
    · obtain ⟨hzΩ, hzf⟩ := h1 z hz
      simp only [levelBaseMap, Prod.mk.injEq] at hzf
      exact ⟨hzΩ, hzf.1, hzf.2⟩
    · obtain ⟨hx, hxs, hxc⟩ := hx
      exact h2 x (ball_subset_closedBall hx) (by simp only [levelBaseMap, hxs, hxc])

include hB in
/-- **The resultant is bounded below near a critical value.** Let open sets `U₁`, `U₂` cover the
part `E` of the level over `Q \ V` without meeting in `E`. Near a value `c` such that `Q` is a
neighbourhood of `c` and the points of `V` near `c` are isolated, the points of a fibre in `U₁`
and in `U₂` have `ζ`-coordinates at distance bounded below. -/
theorem exists_lowerBound_near_critical {ζ : Source 3 →L[ℂ] ℂ}
    (hcoord : Injective fun y : Source 3 => (y 0, h y, ζ y)) {Q V : Set ℂ}
    (hQρ : Q ⊆ closedBall (0 : ℂ) ρ) {U₁ U₂ : Set (Source 2)} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hcover : {x | x ∈ ball (0 : Source 2) R ∧ A.H x 0 = s ∧ h (A.H x) ∈ Q \ V} ⊆ U₁ ∪ U₂)
    (hdisj : ∀ x, x ∈ ball (0 : Source 2) R → A.H x 0 = s → h (A.H x) ∈ Q \ V →
      x ∈ U₁ → x ∉ U₂)
    {c : ℂ} (hcρ : c ∈ closedBall (0 : ℂ) ρ) (hcQ : Q ∈ 𝓝 c) (hVc : ∀ᶠ c' in 𝓝[≠] c, c' ∉ V) :
    ∃ m > 0, ∃ r > 0, ∀ c' ∈ ball c r, c' ≠ c → c' ∈ Q \ V → ∀ x ∈ fibre A R s h c',
      ∀ y ∈ fibre A R s h c', x ∈ U₁ → y ∈ U₂ → m ≤ ‖ζ (A.H x) - ζ (A.H y)‖ := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ c' x y, c' ∈ ball c (1 / ((n : ℝ) + 1)) ∧ c' ≠ c ∧ c' ∈ Q \ V ∧
      x ∈ fibre A R s h c' ∧ y ∈ fibre A R s h c' ∧ x ∈ U₁ ∧ y ∈ U₂ ∧
      ‖ζ (A.H x) - ζ (A.H y)‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨c', hc', hne, hcQV, x, hx, y, hy, hxU, hyU, hlt⟩ := hcon _ hpos _ hpos
    exact ⟨c', x, y, hc', hne, hcQV, hx, hy, hxU, hyU, hlt⟩
  choose cs xs ys hcs hcne hcQV hxs hys hxU hyU hlt using hseq
  have hloc : ∀ n, (xs n, ys n) ∈ locus A R s h ρ ×ˢ locus A R s h ρ := by
    intro n
    have hcn : cs n ∈ closedBall (0 : ℂ) ρ := hQρ (hcQV n).1
    exact ⟨fibre_subset_locus hcn (hxs n), fibre_subset_locus hcn (hys n)⟩
  obtain ⟨⟨xa, ya⟩, ⟨hxaL, hyaL⟩, φ, hφ, htend⟩ :=
    (hB.isCompact_locus.prod hB.isCompact_locus).tendsto_subseq hloc
  have htx : Tendsto (xs ∘ φ) atTop (𝓝 xa) := (continuous_fst.tendsto _).comp htend
  have hty : Tendsto (ys ∘ φ) atTop (𝓝 ya) := (continuous_snd.tendsto _).comp htend
  -- the base values converge to `c`
  have hone : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htc : Tendsto (cs ∘ φ) atTop (𝓝 c) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (hone.comp hφ.tendsto_atTop)
    have h1 := mem_ball.mp (hcs (φ n))
    simp only [comp_apply]
    exact h1.le
  have hHc : ContinuousOn (fun x => h (A.H x)) (locus A R s h ρ) :=
    h.continuous.comp_continuousOn (hB.continuousOn_H.mono fun x hx => ball_subset_closedBall hx.1)
  have hζc : ContinuousOn (fun x => ζ (A.H x)) (locus A R s h ρ) :=
    ζ.continuous.comp_continuousOn (hB.continuousOn_H.mono fun x hx => ball_subset_closedBall hx.1)
  have hxmem : ∀ n, xs n ∈ locus A R s h ρ := fun n => (hloc n).1
  have hymem : ∀ n, ys n ∈ locus A R s h ρ := fun n => (hloc n).2
  have hφx : Tendsto (fun n => h (A.H ((xs ∘ φ) n))) atTop (𝓝 (h (A.H xa))) :=
    (hHc xa hxaL).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨htx, Eventually.of_forall
      fun n => hxmem _⟩)
  have hφy : Tendsto (fun n => h (A.H ((ys ∘ φ) n))) atTop (𝓝 (h (A.H ya))) :=
    (hHc ya hyaL).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hty, Eventually.of_forall
      fun n => hymem _⟩)
  have hxac : h (A.H xa) = c := by
    refine tendsto_nhds_unique hφx ?_
    refine htc.congr fun n => ?_
    simp only [comp_apply]
    exact ((hxs (φ n)).2.2).symm
  have hyac : h (A.H ya) = c := by
    refine tendsto_nhds_unique hφy ?_
    refine htc.congr fun n => ?_
    simp only [comp_apply]
    exact ((hys (φ n)).2.2).symm
  have hζx : Tendsto (fun n => ζ (A.H ((xs ∘ φ) n))) atTop (𝓝 (ζ (A.H xa))) :=
    (hζc xa hxaL).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨htx, Eventually.of_forall
      fun n => hxmem _⟩)
  have hζy : Tendsto (fun n => ζ (A.H ((ys ∘ φ) n))) atTop (𝓝 (ζ (A.H ya))) :=
    (hζc ya hyaL).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hty, Eventually.of_forall
      fun n => hymem _⟩)
  have hζeq : ζ (A.H xa) = ζ (A.H ya) := by
    have h1 := (hζx.sub hζy).norm
    have h2 : Tendsto (fun n => ‖ζ (A.H ((xs ∘ φ) n)) - ζ (A.H ((ys ∘ φ) n))‖) atTop (𝓝 0) :=
      squeeze_zero (fun n => norm_nonneg _) (fun n => (hlt (φ n)).le)
        (hone.comp hφ.tendsto_atTop)
    have h3 := tendsto_nhds_unique h1 h2
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hxy : xa = ya := by
    apply hB.injOn hxaL.1 hyaL.1
    apply hcoord
    simp only [hxaL.2.1, hyaL.2.1, hxac, hyac, hζeq]
  subst hxy
  -- the chart of the level at the limit point
  obtain ⟨γ, rγ, κ, N, hrγ, hNo, hxN, hNB, hγ0, hγ, hγinj, hκ, hfan, -⟩ :=
    hB.exists_chart hxaL.1 hxaL.2.1
  have hF : AnalyticAt ℂ (fun t => h (A.H (γ t)) - c) 0 :=
    (hfan 0 (mem_ball_self hrγ)).sub analyticAt_const
  have hnotev : ¬ ∀ᶠ t in 𝓝 (0 : ℂ), h (A.H (γ t)) - c = 0 := by
    intro hev
    obtain ⟨r₂, hr₂, hr₂b⟩ := Metric.eventually_nhds_iff_ball.mp hev
    have hsub : γ '' ball (0 : ℂ) (min rγ r₂) ⊆ fibre A R s h c := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨-, hγN, hγs⟩ := hγ t (ball_subset_ball (min_le_left _ _) ht)
      exact ⟨hNB hγN, hγs, sub_eq_zero.mp (hr₂b t (ball_subset_ball (min_le_right _ _) ht))⟩
    have hinf : (γ '' ball (0 : ℂ) (min rγ r₂)).Infinite :=
      Set.Infinite.image (hγinj.mono (ball_subset_ball (min_le_left _ _)))
        (infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds 0 (lt_min hrγ hr₂)))
    exact hinf ((hB.finite_fibre hcoord hcρ).subset hsub)
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (A.H (γ t)) - c ≠ 0 :=
    hF.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnotev
  have hγc : ContinuousAt (fun t => h (A.H (γ t))) 0 := (hfan 0 (mem_ball_self hrγ)).continuousAt
  have hγ0c : h (A.H (γ 0)) = c := by rw [hγ0]; exact hxac
  have htQ : ∀ᶠ t in 𝓝 (0 : ℂ), h (A.H (γ t)) ∈ Q :=
    hγc.preimage_mem_nhds (by rw [hγ0c]; exact hcQ)
  have htend' : Tendsto (fun t => h (A.H (γ t))) (𝓝[≠] (0 : ℂ)) (𝓝[≠] c) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := hγc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
      rwa [hγ0c] at this
    · filter_upwards [hne] with t ht
      exact sub_ne_zero.mp ht
  have htV : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (A.H (γ t)) ∉ V := htend'.eventually hVc
  obtain ⟨τ, hτ, hτb⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp
    ((htQ.filter_mono nhdsWithin_le_nhds).and (htV.and hne)))
  set τ' := min τ rγ with hτ'
  have hτ'pos : 0 < τ' := lt_min hτ hrγ
  set Pset : Set (Source 2) := γ '' (ball (0 : ℂ) τ' \ {0}) with hPset
  have hPE : ∀ z ∈ Pset, z ∈ ball (0 : Source 2) R ∧ A.H z 0 = s ∧ h (A.H z) ∈ Q \ V := by
    rintro _ ⟨t, ⟨ht, ht0⟩, rfl⟩
    have htr : t ∈ ball (0 : ℂ) rγ := ball_subset_ball (min_le_right _ _) ht
    obtain ⟨-, hγN, hγs⟩ := hγ t htr
    obtain ⟨hQ, hV, -⟩ := hτb t (ball_subset_ball (min_le_left _ _) ht) ht0
    exact ⟨hNB hγN, hγs, hQ, hV⟩
  have hPc : IsPreconnected Pset := by
    refine (isPreconnected_ball_diff_countable hτ'pos (countable_singleton 0)).image _ ?_
    intro t ht
    exact (hγ t (ball_subset_ball (min_le_right _ _) ht.1)).1.continuousAt.continuousWithinAt
  -- the approximating points lie in `Pset` for large `n`
  have hNx : N ∩ (fun z => κ (z - xa)) ⁻¹' ball 0 τ' ∈ 𝓝 xa := by
    refine inter_mem (hNo.mem_nhds hxN) ?_
    apply ContinuousAt.preimage_mem_nhds (by fun_prop)
    simpa using ball_mem_nhds (0 : ℂ) hτ'pos
  have hinP : ∀ z ∈ N ∩ (fun z => κ (z - xa)) ⁻¹' ball 0 τ', A.H z 0 = s → h (A.H z) ≠ c →
      z ∈ Pset := by
    rintro z ⟨hzN, hzτ⟩ hzs hzc
    obtain ⟨-, hγz⟩ := hκ z hzN hzs
    refine ⟨κ (z - xa), ⟨hzτ, fun h0 => ?_⟩, hγz⟩
    rw [mem_singleton_iff] at h0
    rw [h0, hγ0] at hγz
    rw [← hγz] at hzc
    exact hzc hxac
  obtain ⟨n, hnx, hny⟩ := ((htx.eventually hNx).and (hty.eventually hNx)).exists
  have hcnc : cs (φ n) ≠ c := hcne (φ n)
  have hxP : xs (φ n) ∈ Pset := hinP _ hnx (hxs (φ n)).2.1 (by rw [(hxs (φ n)).2.2]; exact hcnc)
  have hyP : ys (φ n) ∈ Pset := hinP _ hny (hys (φ n)).2.1 (by rw [(hys (φ n)).2.2]; exact hcnc)
  obtain ⟨z, hzP, hz1, hz2⟩ := hPc U₁ U₂ hU₁ hU₂ (fun z hz => hcover (hPE z hz))
    ⟨_, hxP, hxU (φ n)⟩ ⟨_, hyP, hyU (φ n)⟩
  obtain ⟨hzB, hzs, hzQV⟩ := hPE z hzP
  exact hdisj z hzB hzs hzQV hz1 hz2

end LevelBall

/-- A point of the closed square `[-a, a]²` has norm at most `√2 a`. -/
theorem norm_le_of_mem_baseSquare {a : ℝ} {c : ℂ} (hc : c ∈ baseSquare a) : ‖c‖ ≤ √2 * a := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc
  have ha : 0 ≤ a := by linarith
  have hre : c.re ^ 2 ≤ a ^ 2 := by nlinarith
  have him : c.im ^ 2 ≤ a ^ 2 := by nlinarith
  have hn : ‖c‖ ^ 2 ≤ (√2 * a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hn

/-- Lower bound for a double product of norms. -/
theorem le_norm_prod_prod {α : Type*} (s t : Finset α) (f : α → α → ℂ) {κ : ℝ} (hκ : 0 ≤ κ)
    (h : ∀ x ∈ s, ∀ y ∈ t, κ ≤ ‖f x y‖) :
    κ ^ (s.card * t.card) ≤ ‖∏ x ∈ s, ∏ y ∈ t, f x y‖ := by
  rw [norm_prod]
  simp_rw [norm_prod]
  calc κ ^ (s.card * t.card) = ∏ _x ∈ s, ∏ _y ∈ t, κ := by
        rw [Finset.prod_const, Finset.prod_const, ← pow_mul, mul_comm]
    _ ≤ ∏ x ∈ s, ∏ y ∈ t, ‖f x y‖ := by
        refine Finset.prod_le_prod (fun x _ => Finset.prod_nonneg fun y _ => hκ)
          fun x hx => Finset.prod_le_prod (fun y _ => hκ) fun y hy => h x hx y hy

/-- Strict upper bound for a double product of norms. -/
theorem norm_prod_prod_lt {α : Type*} (s t : Finset α) (hs : s.Nonempty) (ht : t.Nonempty)
    (f : α → α → ℂ) {κ : ℝ} (h : ∀ x ∈ s, ∀ y ∈ t, 0 < ‖f x y‖ ∧ ‖f x y‖ < κ) :
    ‖∏ x ∈ s, ∏ y ∈ t, f x y‖ < κ ^ (s.card * t.card) := by
  rw [norm_prod]
  simp_rw [norm_prod]
  calc ∏ x ∈ s, ∏ y ∈ t, ‖f x y‖ < ∏ _x ∈ s, ∏ _y ∈ t, κ := by
        refine Finset.prod_lt_prod_of_nonempty
          (fun x hx => Finset.prod_pos fun y hy => (h x hx y hy).1)
          (fun x hx => Finset.prod_lt_prod_of_nonempty (fun y hy => (h x hx y hy).1)
            (fun y hy => (h x hx y hy).2) ht) hs
    _ = κ ^ (s.card * t.card) := by
        rw [Finset.prod_const, Finset.prod_const, ← pow_mul, mul_comm]

/-- The squared-norm boundary of the closed square. -/
theorem squareNorm_eq_of_mem_frontier {a : ℝ} {c : ℂ}
    (hc : c ∈ frontier (Ioo (-a) a ×ℂ Ioo (-a) a)) : squareNorm c = a := by
  have hcl : c ∈ closure (Ioo (-a) a ×ℂ Ioo (-a) a) := frontier_subset_closure hc
  have hnint : c ∉ interior (Ioo (-a) a ×ℂ Ioo (-a) a) := hc.2
  rw [Complex.interior_reProdIm, interior_Ioo, Complex.mem_reProdIm] at hnint
  rw [Complex.closure_reProdIm, Complex.mem_reProdIm] at hcl
  by_cases ha : -a < a
  · rw [closure_Ioo ha.ne] at hcl
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcl
    simp only [mem_Ioo, not_and_or, not_lt] at hnint
    simp only [squareNorm]
    apply le_antisymm (max_le (abs_le.mpr ⟨h1, h2⟩) (abs_le.mpr ⟨h3, h4⟩))
    rcases hnint with (h | h) | (h | h)
    · exact le_max_of_le_left (by rw [abs_of_nonpos (by linarith)]; linarith)
    · exact le_max_of_le_left (by rw [abs_of_nonneg (by linarith)]; linarith)
    · exact le_max_of_le_right (by rw [abs_of_nonpos (by linarith)]; linarith)
    · exact le_max_of_le_right (by rw [abs_of_nonneg (by linarith)]; linarith)
  · rw [Ioo_eq_empty ha, closure_empty] at hcl
    exact absurd hcl.1 (notMem_empty _)

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}

theorem baseSquare_subset_ball (P : LevelProjectionSetup A L) :
    baseSquare P.square ⊆ ball (0 : ℂ) P.radius := by
  intro c hc
  have h1 := norm_le_of_mem_baseSquare hc
  have h2 := P.square_le
  have hsq : √2 * (√2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h3 : √2 * P.square ≤ P.outerRadius := by
    calc √2 * P.square ≤ √2 * (P.outerRadius * (√2 / 2)) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
      _ = P.outerRadius := by rw [mul_comm P.outerRadius, ← mul_assoc, hsq, one_mul]
  exact mem_ball_zero_iff.mpr (h1.trans_lt (h3.trans_lt P.outerRadius_lt))

/-- **The field (D).** The part of the level over the square minus the critical values is
preconnected, under the separation of the roots over the boundary of the square and the
smallness of the roots over one regular value inside it. -/
theorem connectedHolds_of (P : LevelProjectionSetup A L)
    (hB : LevelBall A L.radius L.parameter P.baseCoord P.radius)
    (hcrit : ∀ c ∈ ball (0 : ℂ) P.radius, c ∉ P.critical → ∀ x ∈ P.levelFibre c,
      Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x))
    {κ : ℝ} (hκ : 0 < κ)
    (hsep : ∀ c, squareNorm c = P.square → ∀ x ∈ P.levelFibre c, ∀ y ∈ P.levelFibre c,
      x ≠ y → κ ≤ ‖P.fibreCoord (A.H x) - P.fibreCoord (A.H y)‖)
    {c₁ : ℂ} (hc₁ : squareNorm c₁ < P.square) (hc₁V : c₁ ∉ P.critical)
    (hsmall : ∀ x ∈ P.levelFibre c₁, ‖P.fibreCoord (A.H x)‖ < κ / 2) :
    P.ConnectedHolds := by
  classical
  set a := P.square with ha_def
  set V : Set ℂ := ↑P.critical with hV_def
  set Q := baseSquare a with hQ_def
  set ζ := P.fibreCoord with hζdef
  set φ : Source 2 → ℂ := fun x => P.baseCoord (A.H x) with hφdef
  have ha : 0 < a := P.square_pos
  intro U₁ U₂ hU₁ hU₂ hcover hne₁ hne₂
  by_contra hdisjne
  have hdisj : ∀ x, x ∈ ball (0 : Source 2) L.radius → A.H x 0 = L.parameter →
      P.baseCoord (A.H x) ∈ Q \ V → x ∈ U₁ → x ∉ U₂ :=
    fun x hx hxs hxQ h1 h2 => hdisjne ⟨x, ⟨hx, hxs, hxQ⟩, h1, h2⟩
  have hQρ : Q ⊆ closedBall (0 : ℂ) P.radius := fun c hc =>
    ball_subset_closedBall (P.baseSquare_subset_ball hc)
  have hVQ : ∀ c ∈ V, c ∈ Ioo (-a) a ×ℂ Ioo (-a) a := fun c hc =>
    Complex.mem_reProdIm.mpr (P.critical_mem c hc)
  -- the finite fibres
  let F : ℂ → Finset (Source 2) := fun c =>
    if hc : (P.levelFibre c).Finite then hc.toFinset else ∅
  have hF : ∀ c ∈ Q, ∀ x, x ∈ F c ↔ x ∈ P.levelFibre c := by
    intro c hc x
    have hfin : (P.levelFibre c).Finite := hB.finite_fibre P.coordinates (hQρ hc)
    simp only [F, dif_pos hfin, Set.Finite.mem_toFinset]
  let F₁ : ℂ → Finset (Source 2) := fun c => (F c).filter (· ∈ U₁)
  let F₂ : ℂ → Finset (Source 2) := fun c => (F c).filter (· ∈ U₂)
  let Rf : ℂ → ℂ := fun c => ∏ x ∈ F₁ c, ∏ y ∈ F₂ c, (ζ (A.H x) - ζ (A.H y))
  have hmemF₁ : ∀ c ∈ Q, ∀ x, x ∈ F₁ c ↔ x ∈ P.levelFibre c ∧ x ∈ U₁ := by
    intro c hc x
    simp only [F₁, Finset.mem_filter, hF c hc]
  have hmemF₂ : ∀ c ∈ Q, ∀ x, x ∈ F₂ c ↔ x ∈ P.levelFibre c ∧ x ∈ U₂ := by
    intro c hc x
    simp only [F₂, Finset.mem_filter, hF c hc]
  -- points of a fibre over `Q \ V` in `U₁` and in `U₂` are distinct, with distinct `ζ`
  have hfac : ∀ c ∈ Q \ V, ∀ x ∈ F₁ c, ∀ y ∈ F₂ c, ζ (A.H x) - ζ (A.H y) ≠ 0 := by
    intro c hc x hx y hy
    obtain ⟨⟨hxB, hxs, hxc⟩, hxU⟩ := (hmemF₁ c hc.1 x).mp hx
    obtain ⟨⟨hyB, hys, hyc⟩, hyU⟩ := (hmemF₂ c hc.1 y).mp hy
    intro hzero
    have hxy : x = y := by
      apply P.injOn_level ⟨hxB, hxs⟩ ⟨hyB, hys⟩
      simp only [Prod.mk.injEq]
      exact ⟨hxc.trans hyc.symm, sub_eq_zero.mp hzero⟩
    subst hxy
    exact hdisj x hxB hxs (by rw [hxc]; exact hc) hxU hyU
  have hRne : ∀ c ∈ Q \ V, Rf c ≠ 0 := by
    intro c hc
    exact Finset.prod_ne_zero_iff.mpr fun x hx =>
      Finset.prod_ne_zero_iff.mpr fun y hy => hfac c hc x hx y hy
  -- the local structure over a regular value
  have hlocal : ∀ c ∈ Q \ V, ∃ r > 0, ∃ Rl : ℂ → ℂ, DifferentiableAt ℂ Rl c ∧
      ∀ c' ∈ ball c r, c' ∈ Q \ V → Rf c' = Rl c' ∧ (F₁ c').card = (F₁ c).card ∧
        (F₂ c').card = (F₂ c).card := by
    intro c hc
    have hcball := P.baseSquare_subset_ball hc.1
    obtain ⟨Z, hZ, r, hr, G, hG0, hG⟩ :=
      hB.exists_levelLabels (hQρ hc.1) (hcrit c hcball hc.2)
    have hstab : ∀ z ∈ Z, ∀ᶠ c' in 𝓝 c, (z ∈ U₁ → G z c' ∈ U₁) ∧ (z ∈ U₂ → G z c' ∈ U₂) := by
      intro z hz
      obtain ⟨h1, h2, -⟩ := hG0 z hz
      have hcont : ContinuousAt (G z) c := h2.continuousAt (ball_mem_nhds c hr)
      refine Eventually.and ?_ ?_
      · by_cases hzU : z ∈ U₁
        · filter_upwards [hcont.preimage_mem_nhds (by rw [h1]; exact hU₁.mem_nhds hzU)]
            with c' hc' _ using hc'
        · exact Eventually.of_forall fun c' h => absurd h hzU
      · by_cases hzU : z ∈ U₂
        · filter_upwards [hcont.preimage_mem_nhds (by rw [h1]; exact hU₂.mem_nhds hzU)]
            with c' hc' _ using hc'
        · exact Eventually.of_forall fun c' h => absurd h hzU
    obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.eventually_nhds_iff_ball.mp
      ((Filter.eventually_all_finset Z).mpr hstab)
    set r' := min r r₁ with hr'def
    have hr' : 0 < r' := lt_min hr hr₁
    set Z₁ := Z.filter (· ∈ U₁) with hZ₁
    set Z₂ := Z.filter (· ∈ U₂) with hZ₂
    have hZE : ∀ z ∈ Z, z ∈ U₁ ∨ z ∈ U₂ := by
      intro z hz
      obtain ⟨hzB, hzs, hzc⟩ := (hZ z).mp hz
      exact hcover ⟨hzB, hzs, by rw [hzc]; exact hc⟩
    have himage : ∀ c' ∈ ball c r', c' ∈ Q \ V →
        F₁ c' = Z₁.image (fun z => G z c') ∧ F₂ c' = Z₂.image (fun z => G z c') := by
      intro c' hc' hc'QV
      have hc'r : c' ∈ ball c r := ball_subset_ball (min_le_left _ _) hc'
      have hc'r₁ := hr₁b c' (ball_subset_ball (min_le_right _ _) hc')
      obtain ⟨hGfib, hGsurj, -⟩ := hG c' hc'r
      constructor
      · ext x
        rw [hmemF₁ c' hc'QV.1, Finset.mem_image]
        constructor
        · rintro ⟨hx, hxU⟩
          obtain ⟨z, hz, rfl⟩ := hGsurj x hx
          refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩, rfl⟩
          rcases hZE z hz with hzU | hzU
          · exact hzU
          · exact absurd ((hc'r₁ z hz).2 hzU)
              (hdisj _ hx.1 hx.2.1 (by rw [hx.2.2]; exact hc'QV) hxU)
        · rintro ⟨z, hz, rfl⟩
          obtain ⟨hzZ, hzU⟩ := Finset.mem_filter.mp hz
          exact ⟨hGfib z hzZ, (hc'r₁ z hzZ).1 hzU⟩
      · ext x
        rw [hmemF₂ c' hc'QV.1, Finset.mem_image]
        constructor
        · rintro ⟨hx, hxU⟩
          obtain ⟨z, hz, rfl⟩ := hGsurj x hx
          refine ⟨z, Finset.mem_filter.mpr ⟨hz, ?_⟩, rfl⟩
          rcases hZE z hz with hzU | hzU
          · exact absurd hxU (hdisj _ hx.1 hx.2.1 (by rw [hx.2.2]; exact hc'QV)
              ((hc'r₁ z hz).1 hzU))
          · exact hzU
        · rintro ⟨z, hz, rfl⟩
          obtain ⟨hzZ, hzU⟩ := Finset.mem_filter.mp hz
          exact ⟨hGfib z hzZ, (hc'r₁ z hzZ).2 hzU⟩
    have hinj : ∀ c' ∈ ball c r', ∀ T ⊆ Z, Set.InjOn (fun z => G z c') ↑T := by
      intro c' hc' T hT
      exact ((hG c' (ball_subset_ball (min_le_left _ _) hc')).2.2).mono fun z hz => hT hz
    set Rl : ℂ → ℂ := fun c' => ∏ z ∈ Z₁, ∏ w ∈ Z₂, (ζ (A.H (G z c')) - ζ (A.H (G w c')))
      with hRl
    have hcount : ∀ c' ∈ ball c r', c' ∈ Q \ V →
        Rf c' = Rl c' ∧ (F₁ c').card = Z₁.card ∧ (F₂ c').card = Z₂.card := by
      intro c' hc' hc'QV
      obtain ⟨h1, h2⟩ := himage c' hc' hc'QV
      refine ⟨?_, ?_, ?_⟩
      · simp only [Rf]
        rw [h1, h2, Finset.prod_image (hinj c' hc' Z₁ (Finset.filter_subset _ _))]
        refine Finset.prod_congr rfl fun z _ => ?_
        rw [Finset.prod_image (hinj c' hc' Z₂ (Finset.filter_subset _ _))]
      · rw [h1, Finset.card_image_of_injOn (hinj c' hc' Z₁ (Finset.filter_subset _ _))]
      · rw [h2, Finset.card_image_of_injOn (hinj c' hc' Z₂ (Finset.filter_subset _ _))]
    refine ⟨r', hr', Rl, ?_, fun c' hc' hc'QV => ?_⟩
    · refine DifferentiableAt.fun_finsetProd fun z hz => ?_
      refine DifferentiableAt.fun_finsetProd fun w hw => ?_
      have hd : ∀ u ∈ Z, DifferentiableAt ℂ (fun c' => ζ (A.H (G u c'))) c := by
        intro u hu
        obtain ⟨h1, -, h3⟩ := hG0 u hu
        have hHu : AnalyticAt ℂ A.H (G u c) := by
          rw [h1]
          exact hB.analyticAt u (ball_subset_closedBall ((hZ u).mp hu).1)
        exact (ζ.differentiableAt).comp c (hHu.differentiableAt.comp c h3)
      exact (hd z (Finset.mem_filter.mp hz).1).sub (hd w (Finset.mem_filter.mp hw).1)
    · obtain ⟨e1, e2, e3⟩ := hcount c' hc' hc'QV
      obtain ⟨-, e2c, e3c⟩ := hcount c (mem_ball_self hr') hc
      exact ⟨e1, e2.trans e2c.symm, e3.trans e3c.symm⟩
  -- the counts are constant on `Q \ V`
  have hQVc : IsPreconnected (Q \ V) :=
    isPreconnected_baseSquare_diff_countable ha P.critical.finite_toSet.countable P.critical_mem
  have hn₁ : ∀ c ∈ Q \ V, ∀ c' ∈ Q \ V, (F₁ c).card = (F₁ c').card := by
    intro c hc c' hc'
    refine IsPreconnected.eq_of_eventually_eq hQVc (f := fun c => (F₁ c).card)
      (fun c hc => ?_) hc hc'
    obtain ⟨r, hr, Rl, -, hRl⟩ := hlocal c hc
    filter_upwards [inter_mem_nhdsWithin (Q \ V) (ball_mem_nhds c hr)] with c' hc'
    exact (hRl c' hc'.2 hc'.1).2.1
  have hn₂ : ∀ c ∈ Q \ V, ∀ c' ∈ Q \ V, (F₂ c).card = (F₂ c').card := by
    intro c hc c' hc'
    refine IsPreconnected.eq_of_eventually_eq hQVc (f := fun c => (F₂ c).card)
      (fun c hc => ?_) hc hc'
    obtain ⟨r, hr, Rl, -, hRl⟩ := hlocal c hc
    filter_upwards [inter_mem_nhdsWithin (Q \ V) (ball_mem_nhds c hr)] with c' hc'
    exact (hRl c' hc'.2 hc'.1).2.2
  have hc₁Q : c₁ ∈ Q := by
    have h := hc₁.le
    simp only [squareNorm, max_le_iff, abs_le] at h
    exact ⟨⟨h.1.1, h.1.2⟩, h.2.1, h.2.2⟩
  have hc₁QV : c₁ ∈ Q \ V := ⟨hc₁Q, hc₁V⟩
  have hpos₁ : (F₁ c₁).Nonempty := by
    obtain ⟨x, ⟨hxB, hxs, hxQV⟩, hxU⟩ := hne₁
    rw [← Finset.card_pos, hn₁ c₁ hc₁QV _ hxQV]
    exact Finset.card_pos.mpr ⟨x, (hmemF₁ _ hxQV.1 x).mpr ⟨⟨hxB, hxs, rfl⟩, hxU⟩⟩
  have hpos₂ : (F₂ c₁).Nonempty := by
    obtain ⟨x, ⟨hxB, hxs, hxQV⟩, hxU⟩ := hne₂
    rw [← Finset.card_pos, hn₂ c₁ hc₁QV _ hxQV]
    exact Finset.card_pos.mpr ⟨x, (hmemF₂ _ hxQV.1 x).mpr ⟨⟨hxB, hxs, rfl⟩, hxU⟩⟩
  set N := (F₁ c₁).card * (F₂ c₁).card with hNdef
  -- the open square
  set Usq : Set ℂ := Ioo (-a) a ×ℂ Ioo (-a) a with hUsq
  have hUo : IsOpen Usq := isOpen_Ioo.reProdIm isOpen_Ioo
  have hUQ : Usq ⊆ Q := fun z hz => by
    obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hz
    exact ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩
  have hclU : closure Usq = Q := by
    rw [hUsq, Complex.closure_reProdIm, closure_Ioo (by linarith : -a ≠ a)]
    ext z
    simp only [Complex.mem_reProdIm, hQ_def, baseSquare, mem_ofPred_eq]
  have hVcl : IsClosed V := P.critical.finite_toSet.isClosed
  have hVcompl : ∀ c, c ∉ V → ∀ᶠ c' in 𝓝 c, c' ∉ V := fun c hc =>
    hVcl.isOpen_compl.mem_nhds hc
  -- lower bounds near the critical values
  have hlow : ∀ c ∈ V, ∃ μ > 0, ∃ r > 0, ∀ c' ∈ ball c r, c' ≠ c → c' ∈ Q \ V →
      μ ≤ ‖Rf c'‖ := by
    intro c hcV
    have hcQ : Q ∈ 𝓝 c := mem_of_superset (hUo.mem_nhds (hVQ c hcV)) hUQ
    have hVc : ∀ᶠ c' in 𝓝[≠] c, c' ∉ V := by
      have hfin : (V \ {c}).Finite := P.critical.finite_toSet.sdiff
      have hn : (V \ {c})ᶜ ∈ 𝓝 c := hfin.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
      filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with c' h1 h2 h3
      exact h1 ⟨h3, h2⟩
    obtain ⟨m, hm, r, hr, hbd⟩ := hB.exists_lowerBound_near_critical P.coordinates hQρ hU₁ hU₂
      hcover hdisj (hQρ (hUQ (hVQ c hcV))) hcQ hVc
    refine ⟨m ^ N, pow_pos hm N, r, hr, fun c' hc' hne hc'QV => ?_⟩
    have h := le_norm_prod_prod (F₁ c') (F₂ c') (fun x y => ζ (A.H x) - ζ (A.H y)) hm.le
      (fun x hx y hy => hbd c' hc' hne hc'QV x ((hmemF₁ c' hc'QV.1 x).mp hx).1 y
        ((hmemF₂ c' hc'QV.1 y).mp hy).1 ((hmemF₁ c' hc'QV.1 x).mp hx).2
        ((hmemF₂ c' hc'QV.1 y).mp hy).2)
    rwa [hn₁ c' hc'QV c₁ hc₁QV, hn₂ c' hc'QV c₁ hc₁QV] at h
  -- the inverse of the resultant and its extension
  set G : ℂ → ℂ := fun c => (Rf c)⁻¹ with hGdef
  set Gt : ℂ → ℂ := fun c => if c ∈ V then limUnder (𝓝[≠] c) G else G c with hGtdef
  have hGt : ∀ c, c ∉ V → Gt c = G c := fun c hc => if_neg hc
  have hGteq : ∀ c, c ∉ V → Gt =ᶠ[𝓝 c] G := fun c hc => by
    filter_upwards [hVcompl c hc] with c' hc' using hGt c' hc'
  have hGdiff : ∀ c ∈ Usq, c ∉ V → DifferentiableAt ℂ G c := by
    intro c hcU hcV
    have hcQV : c ∈ Q \ V := ⟨hUQ hcU, hcV⟩
    obtain ⟨r, hr, Rl, hRl, hRlf⟩ := hlocal c hcQV
    have heq : Rf =ᶠ[𝓝 c] Rl := by
      filter_upwards [ball_mem_nhds c hr, hUo.mem_nhds hcU, hVcompl c hcV] with c' h1 h2 h3
      exact (hRlf c' h1 ⟨hUQ h2, h3⟩).1
    exact (hRl.congr_of_eventuallyEq heq).inv (hRne c hcQV)
  have hGtdiff : DifferentiableOn ℂ Gt Usq := by
    intro c hcU
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hcV : c ∈ V
    · obtain ⟨μ, hμ, r, hr, hμb⟩ := hlow c hcV
      have hnb : ∀ᶠ c' in 𝓝 c, c' ∈ Usq ∧ (c' ∈ V → c' = c) ∧ c' ∈ ball c r := by
        have hfin : (V \ {c}).Finite := P.critical.finite_toSet.sdiff
        have hn : (V \ {c})ᶜ ∈ 𝓝 c := hfin.isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
        filter_upwards [hUo.mem_nhds hcU, hn, ball_mem_nhds c hr] with c' h1 h2 h3
        refine ⟨h1, fun h => ?_, h3⟩
        by_contra hne
        exact h2 ⟨h, hne⟩
      obtain ⟨r₀, hr₀, hr₀b⟩ := Metric.eventually_nhds_iff_ball.mp hnb
      have hdiffOn : DifferentiableOn ℂ G (ball c r₀ \ {c}) := by
        intro c' hc'
        obtain ⟨h1, h2, -⟩ := hr₀b c' hc'.1
        have hc'V : c' ∉ V := fun h => hc'.2 (h2 h)
        exact (hGdiff c' h1 hc'V).differentiableWithinAt
      have hbdd : BddAbove (norm ∘ G '' (ball c r₀ \ {c})) := by
        refine ⟨μ⁻¹, ?_⟩
        rintro _ ⟨c', hc', rfl⟩
        obtain ⟨h1, h2, h3⟩ := hr₀b c' hc'.1
        have hc'V : c' ∉ V := fun h => hc'.2 (h2 h)
        have hle := hμb c' h3 hc'.2 ⟨hUQ h1, hc'V⟩
        simp only [comp_apply, hGdef, norm_inv]
        exact inv_anti₀ hμ hle
      have hd := Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hr₀)
        hdiffOn hbdd
      have heq : Gt =ᶠ[𝓝 c] update G c (limUnder (𝓝[≠] c) G) := by
        filter_upwards [ball_mem_nhds c hr₀] with c' hc'
        by_cases hcc : c' = c
        · subst hcc
          simp only [hGtdef, if_pos hcV, update_self]
        · obtain ⟨-, h2, -⟩ := hr₀b c' hc'
          have hc'V : c' ∉ V := fun h => hcc (h2 h)
          rw [hGt c' hc'V, update_of_ne hcc]
      exact (hd.differentiableAt (ball_mem_nhds c hr₀)).congr_of_eventuallyEq heq
    · exact (hGdiff c hcU hcV).congr_of_eventuallyEq (hGteq c hcV)
  have hGtcont : ContinuousOn Gt Q := by
    intro c hcQ
    by_cases hcU : c ∈ Usq
    · exact (hGtdiff.differentiableAt (hUo.mem_nhds hcU)).continuousAt.continuousWithinAt
    · have hcV : c ∉ V := fun h => hcU (hVQ c h)
      have hcQV : c ∈ Q \ V := ⟨hcQ, hcV⟩
      obtain ⟨r, hr, Rl, hRl, hRlf⟩ := hlocal c hcQV
      have hRfw : ContinuousWithinAt Rf Q c := by
        refine hRl.continuousAt.continuousWithinAt.congr_of_eventuallyEq ?_
          (hRlf c (mem_ball_self hr) hcQV).1
        filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds c hr),
          nhdsWithin_le_nhds (hVcompl c hcV), self_mem_nhdsWithin] with c' h1 h2 h3
        exact (hRlf c' h1 ⟨h3, h2⟩).1
      have hGw : ContinuousWithinAt G Q c := hRfw.inv₀ (hRne c hcQV)
      refine hGw.congr_of_eventuallyEq ?_ (hGt c hcV)
      exact nhdsWithin_le_nhds (hGteq c hcV)
  have hdc : DiffContOnCl ℂ Gt Usq := ⟨hGtdiff, by rw [hclU]; exact hGtcont⟩
  -- the bound on the boundary of the square
  have hbound : ∀ z ∈ frontier Usq, ‖Gt z‖ ≤ (κ ^ N)⁻¹ := by
    intro z hz
    have hzsq := squareNorm_eq_of_mem_frontier hz
    have hzQ : z ∈ Q := by
      rw [← hclU]
      exact frontier_subset_closure hz
    have hzV : z ∉ V := fun h => hz.2 (by rw [hUo.interior_eq]; exact hVQ z h)
    have hzQV : z ∈ Q \ V := ⟨hzQ, hzV⟩
    rw [hGt z hzV]
    have hlb : κ ^ N ≤ ‖Rf z‖ := by
      have h := le_norm_prod_prod (F₁ z) (F₂ z) (fun x y => ζ (A.H x) - ζ (A.H y)) hκ.le
        (fun x hx y hy => hsep z hzsq x ((hmemF₁ z hzQ x).mp hx).1 y ((hmemF₂ z hzQ y).mp hy).1
          (fun hxy => hfac z hzQV x hx y hy (by rw [hxy, sub_self])))
      rwa [hn₁ z hzQV c₁ hc₁QV, hn₂ z hzQV c₁ hc₁QV] at h
    simp only [hGdef, norm_inv]
    exact inv_anti₀ (pow_pos hκ N) hlb
  have hbdd : Bornology.IsBounded Usq :=
    (Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdc hbound
    (by rw [hclU]; exact hc₁Q)
  -- the roots over `c₁` are small
  have hlt : ‖Rf c₁‖ < κ ^ N := by
    refine norm_prod_prod_lt (F₁ c₁) (F₂ c₁) hpos₁ hpos₂ (fun x y => ζ (A.H x) - ζ (A.H y))
      fun x hx y hy => ⟨norm_pos_iff.mpr (hfac c₁ hc₁QV x hx y hy), ?_⟩
    have h1 := hsmall x ((hmemF₁ c₁ hc₁Q x).mp hx).1
    have h2 := hsmall y ((hmemF₂ c₁ hc₁Q y).mp hy).1
    calc ‖ζ (A.H x) - ζ (A.H y)‖ ≤ ‖ζ (A.H x)‖ + ‖ζ (A.H y)‖ := norm_sub_le _ _
      _ < κ / 2 + κ / 2 := add_lt_add h1 h2
      _ = κ := by ring
  rw [hGt c₁ hc₁V] at hmax
  simp only [hGdef, norm_inv] at hmax
  have hRpos : 0 < ‖Rf c₁‖ := norm_pos_iff.mpr (hRne c₁ hc₁QV)
  have := (inv_le_inv₀ hRpos (pow_pos hκ N)).mp hmax
  linarith

end LevelProjectionSetup

end OnLeConjecture.Analytic
