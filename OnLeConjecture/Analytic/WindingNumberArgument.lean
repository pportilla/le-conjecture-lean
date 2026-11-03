/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WindingNumber
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card

/-!
# Derivatives of continuous arguments and the local argument principle

A continuous logarithm `L` of a path `γ` is differentiable wherever `γ` is,
with derivative `γ' / γ`. If the imaginary part of `γ' / γ` is positive on the
open interval, the continuous argument `Im ∘ L` is strictly increasing. For a
closed path with strictly increasing argument, the zeros of `Re γ` on the
half-open period `[u, v)` are exactly the times at which the argument meets
`π / 2 + π ℤ`. Their number is twice the winding number.

The local argument principle states that the winding number of
`θ ↦ h (r e^{iθ})` is the vanishing order of `h` at `0`, whenever `h` is
analytic on a disc of radius larger than `r` and vanishes there at most at `0`.
The proof factors `h = z^d G` with `G` continuous and nonvanishing on the disc
and contracts the loop of `G` to a constant loop.
-/

@[expose] public noncomputable section

open Set Filter Topology Real Metric

namespace OnLeConjecture.Analytic

/-- A continuous logarithm has derivative `γ' / γ` wherever `γ` has derivative `γ'`. -/
theorem IsContinuousLogOn.hasDerivAt {γ L : ℝ → ℂ} {u v s : ℝ}
    (hL : IsContinuousLogOn γ L u v) (hs : s ∈ Ioo u v) {γ' : ℂ}
    (hγ : HasDerivAt γ γ' s) : HasDerivAt L (γ' / γ s) s := by
  have hγs : γ s ≠ 0 := by
    rw [← hL.2 s (Ioo_subset_Icc_self hs)]
    exact Complex.exp_ne_zero _
  have hquot : ContinuousAt (fun t => γ t / γ s) s := hγ.continuousAt.div_const _
  have hpos : ∀ᶠ t in 𝓝 s, 0 < (γ t / γ s).re := by
    apply hquot.eventually (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds _)
    simp [div_self hγs]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (hpos.and (isOpen_Ioo.mem_nhds hs))
  let M : ℝ → ℂ := fun t => L s + Complex.log (γ t / γ s)
  have hsub : Icc (s - δ / 2) (s + δ / 2) ⊆ ball s δ := by
    intro t ht
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hsubI : Icc (s - δ / 2) (s + δ / 2) ⊆ Icc u v :=
    fun t ht => Ioo_subset_Icc_self (hball (hsub ht)).2
  have hγcont : ContinuousOn γ (Icc u v) := by
    have : ContinuousOn (fun t => Complex.exp (L t)) (Icc u v) :=
      Complex.continuous_exp.comp_continuousOn hL.1
    exact this.congr fun t ht => (hL.2 t ht).symm
  have hslit : ∀ t ∈ Icc (s - δ / 2) (s + δ / 2), γ t / γ s ∈ Complex.slitPlane :=
    fun t ht => Complex.mem_slitPlane_iff.mpr (Or.inl (hball (hsub ht)).1)
  have hM : ContinuousOn M (Icc (s - δ / 2) (s + δ / 2)) :=
    continuousOn_const.add (ContinuousOn.clog ((hγcont.mono hsubI).div_const _) hslit)
  have hMexp : ∀ t ∈ Icc (s - δ / 2) (s + δ / 2), Complex.exp (M t) = Complex.exp (L t) := by
    intro t ht
    have hne : γ t / γ s ≠ 0 := Complex.slitPlane_ne_zero (hslit t ht)
    rw [Complex.exp_add, Complex.exp_log hne, hL.2 s (Ioo_subset_Icc_self hs),
      hL.2 t (hsubI ht)]
    field_simp
  have hsmem : s ∈ Icc (s - δ / 2) (s + δ / 2) := ⟨by linarith, by linarith⟩
  obtain ⟨n, hn⟩ := exists_int_eq_add_of_exp_eq isPreconnected_Icc hM
    (hL.1.mono hsubI) hMexp hsmem
  have hn0 : n = 0 := by
    have h := hn s hsmem
    simp only [M, div_self hγs, Complex.log_one, add_zero] at h
    have h' : (n : ℂ) * (2 * π * Complex.I) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 two_pi_I_ne_zero
  have heq : M =ᶠ[𝓝 s] L := by
    have hnhds : Icc (s - δ / 2) (s + δ / 2) ∈ 𝓝 s :=
      Icc_mem_nhds (by linarith) (by linarith)
    filter_upwards [hnhds] with t ht
    have h := hn t ht
    rw [hn0] at h
    simp only [Int.cast_zero, zero_mul, add_zero] at h
    exact h
  have hMd : HasDerivAt M (γ' / γ s) s := by
    have h := (hγ.div_const (γ s)).clog_real (hslit s hsmem)
    have h' : HasDerivAt M (γ' / γ s / (γ s / γ s)) s := h.const_add (L s)
    simpa only [div_self hγs, div_one] using h'
  exact hMd.congr_of_eventuallyEq heq.symm

/-- Positive imaginary logarithmic derivative makes the continuous argument
strictly increasing. -/
theorem IsContinuousLogOn.strictMonoOn_im {γ L : ℝ → ℂ} {u v : ℝ}
    (hL : IsContinuousLogOn γ L u v)
    (hd : ∀ s ∈ Ioo u v, ∃ γ' : ℂ, HasDerivAt γ γ' s ∧ 0 < (γ' / γ s).im) :
    StrictMonoOn (fun s => (L s).im) (Icc u v) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc u v)
    (Complex.continuous_im.comp_continuousOn hL.1)
  intro s hs
  rw [interior_Icc] at hs
  obtain ⟨γ', hγ', hpos⟩ := hd s hs
  have hLd := hL.hasDerivAt hs hγ'
  have him : HasDerivAt (fun t => (L t).im) (γ' / γ s).im s := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hLd
    simpa only [Function.comp_def, Complex.imCLM_apply] using h
  change 0 < deriv (fun t => (L t).im) s
  rw [him.deriv]
  exact hpos

/-- The real part of `γ` vanishes exactly where the cosine of the continuous
argument vanishes. -/
theorem IsContinuousLogOn.re_eq_zero_iff {γ L : ℝ → ℂ} {u v : ℝ}
    (hL : IsContinuousLogOn γ L u v) {s : ℝ} (hs : s ∈ Icc u v) :
    (γ s).re = 0 ↔ Real.cos (L s).im = 0 := by
  rw [← hL.2 s hs, Complex.exp_re]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (Real.exp_pos _).ne'
  · intro h
    rw [h, mul_zero]

/-- The zeros of `Re γ` on one half-open period of a closed path with
strictly increasing argument are finite, and their number is twice the winding
number. -/
theorem IsContinuousLogOn.ncard_re_eq_zero {γ L : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hL : IsContinuousLogOn γ L u v) (hmono : StrictMonoOn (fun s => (L s).im) (Icc u v))
    (hloop : γ u = γ v) :
    0 ≤ windingNumber γ u v ∧ ({s | s ∈ Ico u v ∧ (γ s).re = 0} : Set ℝ).Finite ∧
      ({s | s ∈ Ico u v ∧ (γ s).re = 0} : Set ℝ).ncard =
        2 * (windingNumber γ u v).toNat := by
  set W := windingNumber γ u v with hW
  have hu : u ∈ Icc u v := left_mem_Icc.mpr huv
  have hv : v ∈ Icc u v := right_mem_Icc.mpr huv
  have hdiff : L v - L u = W * (2 * π * Complex.I) := hL.sub_eq_windingNumber huv hloop
  let α : ℝ → ℝ := fun s => (L s).im
  have hαv : α v = α u + 2 * π * W := by
    have h := congrArg Complex.im hdiff
    simp only [Complex.sub_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat] at h
    simp only [α]
    linarith
  have hW0 : 0 ≤ W := by
    have hle : α u ≤ α v := hmono.monotoneOn hu hv huv
    rw [hαv] at hle
    have h2 : (0 : ℝ) ≤ 2 * π * W := by linarith
    have : (0 : ℝ) ≤ W := by
      by_contra hneg
      have : 2 * π * (W : ℝ) < 0 := mul_neg_of_pos_of_neg (by positivity) (lt_of_not_ge hneg)
      linarith
    exact_mod_cast this
  refine ⟨hW0, ?_⟩
  have hαcont : ContinuousOn α (Icc u v) := Complex.continuous_im.comp_continuousOn hL.1
  let x : ℝ := α u / π - 1 / 2
  let T : Finset ℤ := Finset.Ico ⌈x⌉ (⌈x⌉ + 2 * W)
  have hlevel : ∀ s ∈ Icc u v, (γ s).re = 0 ↔ ∃ k : ℤ, α s = (2 * k + 1) * π / 2 := by
    intro s hs
    rw [hL.re_eq_zero_iff hs, Real.cos_eq_zero_iff]
  have hfloor : ∀ k : ℤ, ⌊((2 * k + 1) * π / 2) / π⌋ = k := by
    intro k
    rw [show ((2 * k + 1) * π / 2) / π = (k : ℝ) + 1 / 2 by field_simp; try ring]
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  have hmaps : MapsTo (fun s => ⌊α s / π⌋) {s | s ∈ Ico u v ∧ (γ s).re = 0} (T : Set ℤ) := by
      rintro s ⟨hs, hzero⟩
      obtain ⟨k, hk⟩ := (hlevel s (Ico_subset_Icc_self hs)).mp hzero
      simp only [T, Finset.coe_Ico, mem_Ico]
      rw [hk, hfloor]
      have hlo : α u ≤ α s := hmono.monotoneOn hu (Ico_subset_Icc_self hs) hs.1
      have hhi : α s < α v := hmono (Ico_subset_Icc_self hs) hv hs.2
      rw [hk] at hlo hhi
      rw [hαv] at hhi
      constructor
      · rw [Int.ceil_le]
        simp only [x]
        rw [div_sub' (by positivity), div_le_iff₀ Real.pi_pos]
        nlinarith [Real.pi_pos]
      · have : k - 2 * W < ⌈x⌉ := by
          rw [Int.lt_ceil]
          push_cast
          simp only [x]
          rw [lt_sub_iff_add_lt, lt_div_iff₀ Real.pi_pos]
          nlinarith [Real.pi_pos]
        linarith
  have hinj : InjOn (fun s => ⌊α s / π⌋) {s | s ∈ Ico u v ∧ (γ s).re = 0} := by
      rintro s ⟨hs, hzs⟩ t ⟨ht, hzt⟩ hst
      obtain ⟨k, hk⟩ := (hlevel s (Ico_subset_Icc_self hs)).mp hzs
      obtain ⟨l, hl⟩ := (hlevel t (Ico_subset_Icc_self ht)).mp hzt
      simp only [hk, hl, hfloor] at hst
      subst hst
      exact hmono.injOn (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) (hk.trans hl.symm)
  refine ⟨Set.Finite.of_injOn hmaps hinj T.finite_toSet, ?_⟩
  have hcard : ({s | s ∈ Ico u v ∧ (γ s).re = 0} : Set ℝ).ncard = (T : Set ℤ).ncard := by
    apply Set.ncard_congr (fun s _ => ⌊α s / π⌋) (fun s hs => hmaps hs)
      (fun s t hs ht h => hinj hs ht h)
    · intro k hk
      simp only [T, Finset.coe_Ico, mem_Ico] at hk
      have hk1 : α u ≤ (2 * k + 1) * π / 2 := by
        have h := Int.ceil_le.mp hk.1
        simp only [x] at h
        rw [div_sub' (by positivity), div_le_iff₀ Real.pi_pos] at h
        nlinarith [Real.pi_pos]
      have hk2 : (2 * k + 1) * π / 2 < α v := by
        have h : k - 2 * W < ⌈x⌉ := by linarith [hk.2]
        rw [Int.lt_ceil] at h
        push_cast at h
        simp only [x] at h
        rw [lt_sub_iff_add_lt, lt_div_iff₀ Real.pi_pos] at h
        rw [hαv]
        nlinarith [Real.pi_pos]
      obtain ⟨s, hs, hαs⟩ := isPreconnected_Icc.intermediate_value hu hv hαcont
        ⟨hk1, hk2.le⟩
      have hsv : s ≠ v := by
        rintro rfl
        exact (ne_of_lt hk2) hαs.symm
      refine ⟨s, ⟨⟨hs.1, lt_of_le_of_ne hs.2 hsv⟩, (hlevel s hs).mpr ⟨k, hαs⟩⟩, ?_⟩
      simp only [hαs, hfloor]
  rw [hcard, Set.ncard_coe_finset, Int.card_Ico]
  omega

/-! ### The local argument principle -/

/-- The circle of radius `r` traversed by `θ ↦ r e^{iθ}`. -/
def circlePath (r : ℝ) (θ : ℝ) : ℂ := r * Complex.exp (θ * Complex.I)

theorem continuous_circlePath (r : ℝ) : Continuous (circlePath r) := by
  unfold circlePath
  fun_prop

theorem norm_circlePath {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖circlePath r θ‖ = r := by
  simp [circlePath, Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr]

theorem circlePath_add_two_pi (r θ : ℝ) : circlePath r (θ + 2 * π) = circlePath r θ := by
  simp only [circlePath]
  congr 1
  rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = θ * Complex.I + 2 * π * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem windingNumber_circlePath {r : ℝ} (hr : 0 < r) (u : ℝ) :
    windingNumber (circlePath r) u (u + 2 * π) = 1 := by
  have hu : u ≤ u + 2 * π := by linarith [Real.pi_pos]
  have h := windingNumber_const_mul hu
    (γ := fun θ : ℝ => Complex.exp (θ * Complex.I)) (by fun_prop)
    (fun _ _ => Complex.exp_ne_zero _) (by
      rw [show ((u + 2 * π : ℝ) : ℂ) * Complex.I = u * Complex.I + 2 * π * Complex.I by
        push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one])
    (c := (r : ℂ)) (by exact_mod_cast hr.ne')
  rw [windingNumber_exp_mul_I] at h
  exact h

/-- A continuous function without zeros on a disc gives circles of winding number zero. -/
theorem windingNumber_comp_circlePath_eq_zero {G : ℂ → ℂ} {R r : ℝ}
    (hG : ContinuousOn G (ball 0 R)) (hG0 : ∀ z ∈ ball (0 : ℂ) R, G z ≠ 0)
    (hr : 0 ≤ r) (hrR : r < R) (u : ℝ) :
    windingNumber (fun θ => G (circlePath r θ)) u (u + 2 * π) = 0 := by
  have hu : u ≤ u + 2 * π := by linarith [Real.pi_pos]
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ θ : ℝ, (τ : ℂ) * circlePath r θ ∈ ball (0 : ℂ) R := by
    intro τ hτ θ
    rw [mem_ball, dist_zero_right, norm_mul, norm_circlePath hr, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hτ.1]
    nlinarith [hτ.2]
  let H : ℝ → ℝ → ℂ := fun τ θ => G ((τ : ℂ) * circlePath r θ)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc u (u + 2 * π)) := by
    refine hG.comp (Continuous.continuousOn ?_) (fun p hp => hmem p.1 hp.1 p.2)
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      ((continuous_circlePath r).comp continuous_snd)
  have hH := windingNumber_eq_of_homotopy hu hcont (fun τ hτ θ _ => hG0 _ (hmem τ hτ θ))
    (fun τ _ => by
      change G ((τ : ℂ) * circlePath r u) = G ((τ : ℂ) * circlePath r (u + 2 * π))
      rw [circlePath_add_two_pi])
  have h0 : H 0 = fun _ => G 0 := by
    funext θ
    simp [H]
  have h1 : H 1 = fun θ => G (circlePath r θ) := by
    funext θ
    simp [H]
  rw [h0, h1, windingNumber_const (hG0 0 (mem_ball_self (lt_of_le_of_lt hr hrR))) hu] at hH
  exact hH.symm

/-- The local argument principle on a fixed circle: if `h` is analytic on the
disc of radius `R` and vanishes there at most at the origin, then every circle of
radius `r < R` has winding number equal to the vanishing order of `h` at `0`. -/
theorem windingNumber_circlePath_eq_analyticOrderNatAt {h : ℂ → ℂ} {R : ℝ}
    (hh : AnalyticOnNhd ℂ h (ball 0 R)) (hne : ∀ z ∈ ball (0 : ℂ) R, z ≠ 0 → h z ≠ 0)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) (u : ℝ) :
    windingNumber (fun θ => h (circlePath r θ)) u (u + 2 * π) = analyticOrderNatAt h 0 := by
  classical
  have hR : 0 < R := hr.trans hrR
  have h0 : AnalyticAt ℂ h 0 := hh 0 (mem_ball_self hR)
  have hnz : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), h z = 0 := by
    intro hev
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp (hev.and (ball_mem_nhds 0 hR))
    have hzpos : 0 < min ε R / 2 := by positivity
    let z : ℂ := ((min ε R / 2 : ℝ) : ℂ)
    have hzd : dist z 0 < ε := by
      simp only [z, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
      linarith [min_le_left ε R]
    obtain ⟨hz, hzR⟩ := hεb hzd
    exact hne z hzR (by simp only [z, ne_eq, Complex.ofReal_eq_zero]; exact hzpos.ne') hz
  have htop : analyticOrderAt h 0 ≠ ⊤ := fun ht => hnz (analyticOrderAt_eq_top.mp ht)
  set d := analyticOrderNatAt h 0 with hd
  have hdcast : analyticOrderAt h 0 = d := (Nat.cast_analyticOrderNatAt htop).symm
  obtain ⟨g, hg, hg0, hfac⟩ := h0.analyticOrderAt_eq_natCast.mp hdcast
  let G : ℂ → ℂ := fun z => if z = 0 then g 0 else h z / z ^ d
  have hGg : G =ᶠ[𝓝 0] g := by
    filter_upwards [hfac] with z hz
    by_cases hz0 : z = 0
    · simp [G, hz0]
    · simp only [G, hz0, if_false, hz, sub_zero, smul_eq_mul]
      field_simp
  have hGcont : ContinuousOn G (ball 0 R) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    by_cases hz0 : z = 0
    · subst hz0
      exact hg.continuousAt.congr hGg.symm
    · have hloc : (fun w => h w / w ^ d) =ᶠ[𝓝 z] G := by
        filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
        simp [G, hw]
      exact ((hh z hz).continuousAt.div (continuousAt_id.pow d) (pow_ne_zero _ hz0)).congr hloc
  have hGne : ∀ z ∈ ball (0 : ℂ) R, G z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [G, hz0, hg0]
    · simp only [G, hz0, if_false]
      exact div_ne_zero (hne z hz hz0) (pow_ne_zero _ hz0)
  have hfacG : ∀ z ∈ ball (0 : ℂ) R, h z = z ^ d * G z := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      have h00 := hfac.self_of_nhds
      simp only [sub_zero, smul_eq_mul] at h00
      simp [G, h00]
    · simp only [G, hz0, if_false]
      field_simp
  have hu : u ≤ u + 2 * π := by linarith [Real.pi_pos]
  have hcirc : ∀ θ, circlePath r θ ∈ ball (0 : ℂ) R := by
    intro θ
    rw [mem_ball, dist_zero_right, norm_circlePath hr.le]
    exact hrR
  have hcirc_ne : ∀ θ, circlePath r θ ≠ 0 := by
    intro θ hzero
    have := norm_circlePath hr.le θ
    rw [hzero, norm_zero] at this
    exact hr.ne this
  set c := circlePath r with hc
  have hccont : Continuous c := continuous_circlePath r
  have hcloop : c u = c (u + 2 * π) := (circlePath_add_two_pi r u).symm
  have hGc : ContinuousOn (fun θ => G (c θ)) (Icc u (u + 2 * π)) :=
    hGcont.comp hccont.continuousOn (fun θ _ => hcirc θ)
  have hGcne : ∀ θ ∈ Icc u (u + 2 * π), G (c θ) ≠ 0 := fun θ _ => hGne _ (hcirc θ)
  have hcpow : ContinuousOn (c ^ d) (Icc u (u + 2 * π)) := (hccont.pow d).continuousOn
  have hcpowne : ∀ θ ∈ Icc u (u + 2 * π), (c ^ d) θ ≠ 0 :=
    fun θ _ => pow_ne_zero _ (hcirc_ne θ)
  have hprod : ContinuousOn (c ^ d * fun θ => G (c θ)) (Icc u (u + 2 * π)) := hcpow.mul hGc
  have hprodne : ∀ θ ∈ Icc u (u + 2 * π), (c ^ d * fun θ => G (c θ)) θ ≠ 0 :=
    fun θ hθ => mul_ne_zero (hcpowne θ hθ) (hGcne θ hθ)
  rw [windingNumber_congr hu hprod hprodne (fun θ _ => by
      simp only [Pi.mul_apply, Pi.pow_apply]
      exact (hfacG _ (hcirc θ)).symm),
    windingNumber_mul hu hcpow hcpowne (by simp only [Pi.pow_apply, hcloop]) hGc hGcne
      (by simp only [hcloop]),
    windingNumber_pow hu hccont.continuousOn (fun θ _ => hcirc_ne θ) hcloop,
    windingNumber_circlePath hr, windingNumber_comp_circlePath_eq_zero hGcont hGne hr.le hrR]
  simp

/-- The local argument principle for small circles: for an analytic germ which
is not identically zero, every sufficiently small circle has winding number
equal to its vanishing order. -/
theorem exists_radius_windingNumber_circlePath_eq {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hnz : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), h z = 0) :
    ∃ R : ℝ, 0 < R ∧ AnalyticOnNhd ℂ h (ball 0 R) ∧
      (∀ z ∈ ball (0 : ℂ) R, z ≠ 0 → h z ≠ 0) ∧
      ∀ r : ℝ, 0 < r → r < R → ∀ u : ℝ,
        windingNumber (fun θ => h (circlePath r θ)) u (u + 2 * π) = analyticOrderNatAt h 0 := by
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → h z ≠ 0 := by
    have h' := hh.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnz
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using h'
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp (hh.eventually_analyticAt.and hne)
  have han : AnalyticOnNhd ℂ h (ball 0 R) := fun z hz => (hball hz).1
  have hz : ∀ z ∈ ball (0 : ℂ) R, z ≠ 0 → h z ≠ 0 := fun z hz => (hball hz).2
  exact ⟨R, hR, han, hz, fun r hr hrR u =>
    windingNumber_circlePath_eq_analyticOrderNatAt han hz hr hrR u⟩

end OnLeConjecture.Analytic
