/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneBranchBraidCrossingFinite
public import OnLeConjecture.Analytic.WindingNumberArgument

/-!
# Positive crossings for finitely many analytic sheets

Let `U₀, …, U_{S-1}` be holomorphic on a disc about `0`, with pairwise distinct
germs at `0`, and let `c ≠ 0` be a fibre rotation such that `Re (c (U_k 0 - U_l 0)) ≠ 0`
whenever `U_k 0 ≠ U_l 0`. The strands
`K_k(θ) = c U_k(r e^{iθ/q})` are studied on every sufficiently small source circle.

This module proves Theorem `J14:thm:multisheet` of the written proof
(`docs/route-n/written-proofs-J05-J06-J07-J21-J10-J15-J14.tex`), the multi-sheet
positivity record M1153 of the dependency audit. On every source circle of radius
`r < r₀`:

* the strands are pairwise distinct at every angle;
* a pair with equal constant terms has strictly positive angular logarithmic
  derivative, hence a continuous argument that is strictly increasing;
* a pair with distinct constant terms never has equal real parts;
* every projected crossing is transverse with positive crossing determinant;
* every compact angle interval contains finitely many crossing events.

Pairs with equal constant terms are treated by the logarithmic derivative estimate
`eventually_re_mul_deriv_div_pos`, which is the analytic difference estimate
`J14:lem:log`. Pairs with distinct constant terms are treated by continuity and the
hypothesis on `c`. No positivity of a logarithmic derivative is asserted for pairs of
order zero. No closing condition on the strands is assumed here.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace OnLeConjecture.Analytic

/-- The strands of finitely many sheets `U k` on the source circle of radius `r`,
with ramification `q` and fibre rotation `c`: `θ ↦ c U_k(r e^{iθ/q})`. -/
def multiSheetStrands {S : ℕ} (c : ℂ) (U : Fin S → ℂ → ℂ) (q : ℕ) (r : ℝ) :
    Fin S → ℝ → ℂ :=
  fun k θ => c * U k (planeBranchAngularParameter q r θ)

theorem multiSheetStrands_sub {S : ℕ} (c : ℂ) (U : Fin S → ℂ → ℂ) (q : ℕ) (r : ℝ)
    (k l : Fin S) :
    (fun θ => multiSheetStrands c U q r k θ - multiSheetStrands c U q r l θ) =
      fun θ => (fun z => c * (U k z - U l z)) (planeBranchAngularParameter q r θ) := by
  funext θ
  simp only [multiSheetStrands]
  ring

/-- The pairwise estimates of Theorem `J14:thm:multisheet` hold on a common punctured
neighborhood of `0`. -/
theorem eventually_multiSheet_pair_estimates
    {S : ℕ} {U : Fin S → ℂ → ℂ} (hU : ∀ k, AnalyticAt ℂ (U k) 0)
    (hdistinct : ∀ k l, k ≠ l → ¬ (U k =ᶠ[𝓝 0] U l)) {c : ℂ}
    (hproj : ∀ k l, U k 0 ≠ U l 0 → (c * (U k 0 - U l 0)).re ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → ∀ k l, k ≠ l →
      U k z ≠ U l z ∧
      (U k 0 = U l 0 →
        0 < (z * deriv (fun x => U k x - U l x) z / (U k z - U l z)).re) ∧
      (U k 0 ≠ U l 0 → (c * (U k z - U l z)).re ≠ 0) := by
  have hpair : ∀ k l : Fin S, ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 → k ≠ l →
      U k z ≠ U l z ∧
      (U k 0 = U l 0 →
        0 < (z * deriv (fun x => U k x - U l x) z / (U k z - U l z)).re) ∧
      (U k 0 ≠ U l 0 → (c * (U k z - U l z)).re ≠ 0) := by
    intro k l
    by_cases hkl : k = l
    · exact Filter.Eventually.of_forall fun _ _ h => (h hkl).elim
    have hD : AnalyticAt ℂ (fun x => U k x - U l x) 0 := (hU k).sub (hU l)
    have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), (fun x => U k x - U l x) z = 0 := by
      intro h
      apply hdistinct k l hkl
      filter_upwards [h] with z hz
      exact sub_eq_zero.mp hz
    by_cases h0 : U k 0 = U l 0
    · have hpos := eventually_re_mul_deriv_div_pos hD (by simp [h0]) hne
      have hpos' : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
          0 < (z * deriv (fun x => U k x - U l x) z / (U k z - U l z)).re := by
        simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hpos
      filter_upwards [hpos'] with z hz hz0 _
      have hp := hz hz0
      refine ⟨?_, fun _ => hp, fun h => (h h0).elim⟩
      intro heq
      rw [heq, sub_self, div_zero, Complex.zero_re] at hp
      exact lt_irrefl _ hp
    · have hc : ContinuousAt (fun z => (c * (U k z - U l z)).re) 0 :=
        Complex.continuous_re.continuousAt.comp
          (continuousAt_const.mul ((hU k).continuousAt.sub (hU l).continuousAt))
      filter_upwards [hc.eventually_ne (hproj k l h0)] with z hz _ _
      refine ⟨?_, fun h => (h0 h).elim, fun _ => hz⟩
      intro heq
      apply hz
      simp [heq]
  have hall := Filter.eventually_all.mpr fun k => Filter.eventually_all.mpr (hpair k)
  filter_upwards [hall] with z hz hz0 k l hkl
  exact hz k l hz0 hkl

/-- The strands are differentiable when the source circle lies in the disc of
analyticity. -/
theorem multiSheetStrands_hasDerivAt {S : ℕ} {c : ℂ} {U : Fin S → ℂ → ℂ} {R : ℝ}
    (hU : ∀ k, AnalyticOnNhd ℂ (U k) (ball 0 R)) (q : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (k : Fin S) (θ : ℝ) :
    HasDerivAt (multiSheetStrands c U q r k)
      (c * (deriv (U k) (planeBranchAngularParameter q r θ) *
        (Complex.I / (q : ℂ) * planeBranchAngularParameter q r θ))) θ := by
  have hz : planeBranchAngularParameter q r θ ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right, planeBranchAngularParameter_norm,
      abs_of_nonneg hr] using hrR
  have hd := (hU k _ hz).differentiableAt.hasDerivAt
  exact (hd.comp θ (planeBranchAngularParameter_hasDerivAt q r θ)).const_mul c

theorem multiSheetStrands_differentiable {S : ℕ} {c : ℂ} {U : Fin S → ℂ → ℂ} {R : ℝ}
    (hU : ∀ k, AnalyticOnNhd ℂ (U k) (ball 0 R)) (q : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (k : Fin S) : Differentiable ℝ (multiSheetStrands c U q r k) :=
  fun θ => (multiSheetStrands_hasDerivAt hU q hr hrR k θ).differentiableAt

theorem multiSheetStrands_continuous {S : ℕ} {c : ℂ} {U : Fin S → ℂ → ℂ} {R : ℝ}
    (hU : ∀ k, AnalyticOnNhd ℂ (U k) (ball 0 R)) (q : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hrR : r < R) (k : Fin S) : Continuous (multiSheetStrands c U q r k) :=
  (multiSheetStrands_differentiable hU q hr hrR k).continuous

/-- A nonvanishing differentiable path with positive angular logarithmic derivative has
a continuous argument that is strictly increasing on every compact interval. -/
theorem exists_strictMono_continuous_arg {γ : ℝ → ℂ} (hγ : Differentiable ℝ γ)
    (hne : ∀ θ, γ θ ≠ 0) (hpos : ∀ θ, 0 < (deriv γ θ / γ θ).im) (u v : ℝ) :
    ∃ L : ℝ → ℂ, IsContinuousLogOn γ L u v ∧
      StrictMonoOn (fun s => (L s).im) (Icc u v) := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ.continuous.continuousOn (fun s _ => hne s)
  exact ⟨L, hL, hL.strictMonoOn_im fun s _ => ⟨deriv γ s, (hγ s).hasDerivAt, hpos s⟩⟩

/-- **Multi-sheet positivity** (Theorem `J14:thm:multisheet`, record M1153).
For holomorphic sheets with pairwise distinct germs and a fibre rotation `c`
separating the distinct constant terms in real part, every sufficiently small
source circle gives pairwise distinct strands whose projected crossings are all
positive and transverse. Pairs with equal constant terms have strictly increasing
argument of their difference, pairs with distinct constant terms never cross, and
every compact angle interval contains finitely many crossing events. -/
theorem exists_radius_multiSheet_positive_crossings
    {S q : ℕ} (hq : 0 < q) {U : Fin S → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hU : ∀ k, AnalyticOnNhd ℂ (U k) (ball 0 R))
    (hdistinct : ∀ k l, k ≠ l → ¬ (U k =ᶠ[𝓝 0] U l))
    {c : ℂ} (hc : c ≠ 0)
    (hproj : ∀ k l, U k 0 ≠ U l 0 → (c * (U k 0 - U l 0)).re ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ R ∧
      (∀ z ∈ ball (0 : ℂ) r₀, z ≠ 0 → ∀ k l, k ≠ l → U k z ≠ U l z) ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
        (∀ k, Differentiable ℝ (multiSheetStrands c U q r k)) ∧
        (∀ θ, Function.Injective fun k => multiSheetStrands c U q r k θ) ∧
        (∀ k l, k ≠ l → U k 0 = U l 0 → ∀ θ,
          0 < (deriv (fun t => multiSheetStrands c U q r k t -
              multiSheetStrands c U q r l t) θ /
            (multiSheetStrands c U q r k θ - multiSheetStrands c U q r l θ)).im) ∧
        (∀ k l, k ≠ l → U k 0 = U l 0 → ∀ u v : ℝ, ∃ L : ℝ → ℂ,
          IsContinuousLogOn (fun t => multiSheetStrands c U q r k t -
            multiSheetStrands c U q r l t) L u v ∧
          StrictMonoOn (fun s => (L s).im) (Icc u v)) ∧
        (∀ k l, U k 0 ≠ U l 0 → ∀ θ,
          (multiSheetStrands c U q r k θ).re ≠ (multiSheetStrands c U q r l θ).re) ∧
        (∀ θ k l, k ≠ l →
          (multiSheetStrands c U q r k θ).re = (multiSheetStrands c U q r l θ).re →
          0 < -deriv (fun t => (multiSheetStrands c U q r k t -
              multiSheetStrands c U q r l t).re) θ *
            (multiSheetStrands c U q r k θ - multiSheetStrands c U q r l θ).im) ∧
        ∀ u v : ℝ, {θ | θ ∈ Icc u v ∧ ∃ k l, k ≠ l ∧
          (multiSheetStrands c U q r k θ).re = (multiSheetStrands c U q r l θ).re}.Finite := by
  have hU0 : ∀ k, AnalyticAt ℂ (U k) 0 := fun k => hU k 0 (mem_ball_self hR)
  obtain ⟨ρ, hρ, hρspec⟩ := Metric.eventually_nhds_iff.mp
    (eventually_multiSheet_pair_estimates hU0 hdistinct hproj)
  refine ⟨min R ρ, lt_min hR hρ, min_le_left _ _, ?_, ?_⟩
  · intro z hz hz0 k l hkl
    exact (hρspec (ball_subset_ball (min_le_right _ _) hz) hz0 k l hkl).1
  intro r hr hrr
  set K := multiSheetStrands c U q r with hKdef
  have hrR : r < R := lt_of_lt_of_le hrr (min_le_left _ _)
  have hparam (θ : ℝ) : dist (planeBranchAngularParameter q r θ) 0 < ρ := by
    rw [dist_zero_right, planeBranchAngularParameter_norm, abs_of_pos hr]
    exact lt_of_lt_of_le hrr (min_le_right _ _)
  have hparam0 (θ : ℝ) : planeBranchAngularParameter q r θ ≠ 0 := by
    apply norm_pos_iff.mp
    rw [planeBranchAngularParameter_norm, abs_of_pos hr]
    exact hr
  have hest (θ : ℝ) := hρspec (hparam θ) (hparam0 θ)
  have hdiff : ∀ k, Differentiable ℝ (K k) :=
    multiSheetStrands_differentiable hU q hr.le hrR
  have hsub := multiSheetStrands_sub c U q r
  have hne (k l : Fin S) (hkl : k ≠ l) (θ : ℝ) : K k θ - K l θ ≠ 0 := by
    have h := (hest θ k l hkl).1
    have heq : K k θ - K l θ =
        c * (U k (planeBranchAngularParameter q r θ) -
          U l (planeBranchAngularParameter q r θ)) := by
      simp only [hKdef, multiSheetStrands]
      ring
    rw [heq]
    exact mul_ne_zero hc (sub_ne_zero.mpr h)
  have hrot (k l : Fin S) (hkl : k ≠ l) (h0 : U k 0 = U l 0) (θ : ℝ) :
      0 < (deriv (fun t => K k t - K l t) θ / (K k θ - K l θ)).im := by
    have hz : planeBranchAngularParameter q r θ ∈ ball (0 : ℂ) R := by
      simpa only [mem_ball, dist_zero_right, planeBranchAngularParameter_norm,
        abs_of_pos hr] using hrR
    have hdU : DifferentiableAt ℂ (fun z => U k z - U l z)
        (planeBranchAngularParameter q r θ) :=
      ((hU k _ hz).sub (hU l _ hz)).differentiableAt
    have hd : DifferentiableAt ℂ (fun z => c * (U k z - U l z))
        (planeBranchAngularParameter q r θ) := hdU.const_mul c
    have hfun : (fun t => K k t - K l t) =
        fun t => (fun z => c * (U k z - U l z)) (planeBranchAngularParameter q r t) :=
      hsub k l
    have hval : K k θ - K l θ = (fun z => c * (U k z - U l z))
        (planeBranchAngularParameter q r θ) := congrFun hfun θ
    rw [hfun, hval, im_logDeriv_comp_planeBranchAngularParameter q r θ hd]
    have hderiv : deriv (fun z => c * (U k z - U l z)) (planeBranchAngularParameter q r θ) =
        c * deriv (fun z => U k z - U l z) (planeBranchAngularParameter q r θ) :=
      deriv_const_mul c hdU
    rw [hderiv]
    have hcancel : planeBranchAngularParameter q r θ *
          (c * deriv (fun z => U k z - U l z) (planeBranchAngularParameter q r θ)) /
          (c * (U k (planeBranchAngularParameter q r θ) -
            U l (planeBranchAngularParameter q r θ))) =
        planeBranchAngularParameter q r θ *
          deriv (fun z => U k z - U l z) (planeBranchAngularParameter q r θ) /
          (U k (planeBranchAngularParameter q r θ) -
            U l (planeBranchAngularParameter q r θ)) := by
      have hdiffne : U k (planeBranchAngularParameter q r θ) -
          U l (planeBranchAngularParameter q r θ) ≠ 0 :=
        sub_ne_zero.mpr (hest θ k l hkl).1
      field_simp
    rw [hcancel]
    exact div_pos ((hest θ k l hkl).2.1 h0) (by exact_mod_cast hq)
  have hsep (k l : Fin S) (h0 : U k 0 ≠ U l 0) (θ : ℝ) : (K k θ).re ≠ (K l θ).re := by
    have hkl : k ≠ l := fun h => h0 (h ▸ rfl)
    have h := (hest θ k l hkl).2.2 h0
    intro heq
    apply h
    have : c * (U k (planeBranchAngularParameter q r θ) -
        U l (planeBranchAngularParameter q r θ)) = K k θ - K l θ := by
      simp only [hKdef, multiSheetStrands]
      ring
    rw [this, Complex.sub_re, heq, sub_self]
  have hcross (θ : ℝ) (k l : Fin S) (hkl : k ≠ l) (heq : (K k θ).re = (K l θ).re) :
      0 < -deriv (fun t => (K k t - K l t).re) θ * (K k θ - K l θ).im := by
    have h0 : U k 0 = U l 0 := by
      by_contra h0
      exact hsep k l h0 θ heq
    have hdθ : DifferentiableAt ℝ (fun t => K k t - K l t) θ :=
      ((hdiff k) θ).sub ((hdiff l) θ)
    rw [deriv_re_eq_re_deriv hdθ]
    exact crossing_determinant_pos_of_im_div_pos (hne k l hkl θ) (hrot k l hkl h0 θ)
      (by rw [Complex.sub_re, heq, sub_self])
  refine ⟨hdiff, ?_, hrot, ?_, hsep, hcross, ?_⟩
  · intro θ k l heq
    by_contra hkl
    exact hne k l hkl θ (sub_eq_zero.mpr heq)
  · intro k l hkl h0 u v
    exact exists_strictMono_continuous_arg ((hdiff k).sub (hdiff l)) (hne k l hkl)
      (hrot k l hkl h0) u v
  · intro u v
    let P := {p : Fin S × Fin S // p.1 ≠ p.2}
    have hfin : ∀ p : P, {θ | θ ∈ Icc u v ∧ (K p.1.1 θ - K p.1.2 θ).re = 0}.Finite := by
      intro p
      apply finite_regular_zeros_Icc (f := fun t => (K p.1.1 t - K p.1.2 t).re)
        (Complex.continuous_re.comp ((hdiff p.1.1).continuous.sub (hdiff p.1.2).continuous))
      intro θ _ hz
      change (K p.1.1 θ - K p.1.2 θ).re = 0 at hz
      have heq : (K p.1.1 θ).re = (K p.1.2 θ).re := by
        rw [Complex.sub_re] at hz
        linarith
      have h := hcross θ p.1.1 p.1.2 p.2 heq
      intro hd
      change deriv (fun t => (K p.1.1 t - K p.1.2 t).re) θ = 0 at hd
      rw [hd, neg_zero, zero_mul] at h
      exact lt_irrefl _ h
    apply (Set.finite_iUnion hfin).subset
    rintro θ ⟨hθ, k, l, hkl, heq⟩
    exact Set.mem_iUnion.mpr ⟨⟨(k, l), hkl⟩, hθ, by rw [Complex.sub_re, heq, sub_self]⟩

end OnLeConjecture.Analytic
