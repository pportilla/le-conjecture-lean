/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidPositivity
public import OnLeConjecture.Analytic.MultiSheetBraidCrossingCount

/-!
# Strict-transform sheets, root sheets, and their closed braids

`MultiSheetData S` records `S` holomorphic sheets `U_k` on a disc of radius `R`, with
pairwise distinct germs at `0`, a ramification index `q ≥ 1`, and a permutation `τ` of the
labels such that `U_k(e^{2πi/q} t) = U_{τ k}(t)`. In job J14 these are the
strict-transform sheets `U_{jl}(t) = h_j(ω^l t^{q/a_j}) / t^q` of a transverse reduced
germ (Lemma `J14:lem:common`), and `τ` is the monodromy of the root covering.

Over the base circle `ξ = r^q e^{iθ}` the strict-transform braid is
`θ ↦ c U_k(r e^{iθ/q})` (`MultiSheetData.strict`) and the root braid is
`θ ↦ c (r e^{iθ/q})^q U_k(r e^{iθ/q})` (`MultiSheetData.root`). Both are closed braids over
every base period `[b, b + 2π]` with monodromy `τ`, for all sufficiently small `r`.

This module proves that both braids are isotopic through closed braids at all small radii
and all base angles, that the strict-transform braid is represented by its positive event
word, and that the signed crossing count of the root braid, in the sense of the J15
structure `SheetCrossingData`, is `S (S - 1)` plus the length of that event word.
-/

@[expose] public noncomputable section

open Set Filter Metric Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Finitely many holomorphic sheets with pairwise distinct germs, closed under the
rotation `t ↦ e^{2πi/q} t` of the source parameter up to the relabelling `τ`. -/
structure MultiSheetData (S : ℕ) where
  /-- The ramification index of the common source parameter. -/
  q : ℕ
  /-- The sheets. -/
  U : Fin S → ℂ → ℂ
  /-- The radius of the disc of analyticity. -/
  R : ℝ
  /-- The monodromy permutation of the labels. -/
  τ : Equiv.Perm (Fin S)
  q_pos : 0 < q
  R_pos : 0 < R
  analytic : ∀ k, AnalyticOnNhd ℂ (U k) (ball 0 R)
  distinct : ∀ k l, k ≠ l → ¬ (U k =ᶠ[𝓝 0] U l)
  monodromy : ∀ k, ∀ t ∈ ball (0 : ℂ) R,
    U k (Complex.exp (2 * π * Complex.I / q) * t) = U (τ k) t

namespace MultiSheetData

variable {S : ℕ} (D : MultiSheetData S)

/-- The root sheets `t ↦ t^q U_k(t)`. -/
def rootSheet : Fin S → ℂ → ℂ := fun k t => t ^ D.q * D.U k t

/-- The strict-transform braid read through `c` on the source circle of radius `r`. -/
def strict (c : ℂ) (r : ℝ) : Fin S → ℝ → ℂ := multiSheetStrands c D.U D.q r

/-- The root braid read through `c` on the source circle of radius `r`. -/
def root (c : ℂ) (r : ℝ) : Fin S → ℝ → ℂ := multiSheetStrands c D.rootSheet D.q r

theorem rootSheet_analytic (k : Fin S) : AnalyticOnNhd ℂ (D.rootSheet k) (ball 0 D.R) :=
  fun t ht => (analyticAt_id.pow D.q).mul (D.analytic k t ht)

theorem rootSheet_distinct (k l : Fin S) (hkl : k ≠ l) :
    ¬ (D.rootSheet k =ᶠ[𝓝 0] D.rootSheet l) := by
  intro h
  have hd : AnalyticAt ℂ (fun t => D.U k t - D.U l t) 0 :=
    (D.analytic k 0 (mem_ball_self D.R_pos)).sub (D.analytic l 0 (mem_ball_self D.R_pos))
  rcases hd.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · exact D.distinct k l hkl (h0.mono fun t ht => sub_eq_zero.mp ht)
  · obtain ⟨t, ht, ht0⟩ := (hne.and self_mem_nhdsWithin).and
      ((h.filter_mono nhdsWithin_le_nhds)) |>.exists
    have heq : t ^ D.q * D.U k t = t ^ D.q * D.U l t := ht0
    have htne : t ≠ 0 := ht.2
    exact ht.1 (sub_eq_zero.mpr (mul_left_cancel₀ (pow_ne_zero _ htne) heq))

theorem exp_two_pi_div_pow : Complex.exp (2 * π * Complex.I / D.q) ^ D.q = 1 := by
  rw [← Complex.exp_nat_mul]
  have hq : (D.q : ℂ) ≠ 0 := by exact_mod_cast D.q_pos.ne'
  rw [show (D.q : ℂ) * (2 * π * Complex.I / D.q) = 2 * π * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

theorem rootSheet_monodromy (k : Fin S) {t : ℂ} (ht : t ∈ ball (0 : ℂ) D.R) :
    D.rootSheet k (Complex.exp (2 * π * Complex.I / D.q) * t) = D.rootSheet (D.τ k) t := by
  simp only [rootSheet, mul_pow, D.exp_two_pi_div_pow, one_mul, D.monodromy k t ht]

theorem parameter_mem_ball {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.R) (θ : ℝ) :
    planeBranchAngularParameter D.q r θ ∈ ball (0 : ℂ) D.R := by
  simpa only [mem_ball, dist_zero_right, planeBranchAngularParameter_norm, abs_of_nonneg hr]
    using hrR

theorem strict_add_two_pi (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.R) (k : Fin S) (θ : ℝ) :
    D.strict c r k (θ + 2 * π) = D.strict c r (D.τ k) θ := by
  simp only [strict, multiSheetStrands, planeBranchAngularParameter_add_two_pi,
    D.monodromy k _ (D.parameter_mem_ball hr hrR θ)]

theorem root_add_two_pi (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hrR : r < D.R) (k : Fin S) (θ : ℝ) :
    D.root c r k (θ + 2 * π) = D.root c r (D.τ k) θ := by
  simp only [root, multiSheetStrands, planeBranchAngularParameter_add_two_pi,
    D.rootSheet_monodromy k (D.parameter_mem_ball hr hrR θ)]

/-- The root braid is the strict-transform braid multiplied by the base point
`ξ = r^q e^{iθ}`. -/
theorem root_eq (c : ℂ) (r : ℝ) (k : Fin S) (θ : ℝ) :
    D.root c r k θ = circlePath (r ^ D.q) θ * D.strict c r k θ := by
  simp only [root, strict, multiSheetStrands, rootSheet,
    planeBranchAngularParameter_pow D.q_pos, circlePath]
  push_cast
  ring

/-- The strands built from analytic sheets with a common monodromy, pairwise distinct on
a punctured disc, are closed braids over every base period. -/
theorem isClosedStrandBraid_of_sheets {V : Fin S → ℂ → ℂ}
    (hV : ∀ k, AnalyticOnNhd ℂ (V k) (ball 0 D.R))
    (hmono : ∀ k, ∀ t ∈ ball (0 : ℂ) D.R,
      V k (Complex.exp (2 * π * Complex.I / D.q) * t) = V (D.τ k) t)
    {r₀ : ℝ} (hr₀R : r₀ ≤ D.R)
    (hsep : ∀ z ∈ ball (0 : ℂ) r₀, z ≠ 0 → ∀ k l, k ≠ l → V k z ≠ V l z)
    {c : ℂ} (hc : c ≠ 0) {r : ℝ} (hr : 0 < r) (hrr : r < r₀) (b : ℝ) :
    IsClosedStrandBraid (multiSheetStrands c V D.q r) b (b + 2 * π) D.τ where
  lt := by linarith [Real.pi_pos]
  continuousOn k :=
    (multiSheetStrands_continuous hV D.q hr.le (lt_of_lt_of_le hrr hr₀R) k).continuousOn
  injective t _ k l hkl := by
    by_contra hne
    have hz : planeBranchAngularParameter D.q r t ∈ ball (0 : ℂ) r₀ := by
      simpa only [mem_ball, dist_zero_right, planeBranchAngularParameter_norm,
        abs_of_pos hr] using hrr
    have hz0 : planeBranchAngularParameter D.q r t ≠ 0 := by
      apply norm_pos_iff.mp
      rw [planeBranchAngularParameter_norm, abs_of_pos hr]
      exact hr
    exact hsep _ hz hz0 k l hne (mul_left_cancel₀ hc hkl)
  closing k := by
    simp only [multiSheetStrands, planeBranchAngularParameter_add_two_pi,
      hmono k _ (D.parameter_mem_ball hr.le (lt_of_lt_of_le hrr hr₀R) b)]

/-- Interpolation of the radius is an isotopy through closed braids. -/
theorem multiSheetStrands_radius_isotopic {V : Fin S → ℂ → ℂ}
    (hV : ∀ k, AnalyticOnNhd ℂ (V k) (ball 0 D.R))
    (hmono : ∀ k, ∀ t ∈ ball (0 : ℂ) D.R,
      V k (Complex.exp (2 * π * Complex.I / D.q) * t) = V (D.τ k) t)
    {r₀ : ℝ} (hr₀R : r₀ ≤ D.R)
    (hsep : ∀ z ∈ ball (0 : ℂ) r₀, z ≠ 0 → ∀ k l, k ≠ l → V k z ≠ V l z)
    {c : ℂ} (hc : c ≠ 0) {r r' : ℝ} (hr : 0 < r) (hrr : r < r₀) (hr' : 0 < r') (hrr' : r' < r₀)
    (b : ℝ) :
    ClosedStrandBraidIsotopic (multiSheetStrands c V D.q r) (multiSheetStrands c V D.q r')
      b (b + 2 * π) D.τ := by
  let ρ : ℝ → ℝ := fun s => (1 - s) * r + s * r'
  have hρ : ∀ s ∈ Icc (0 : ℝ) 1, 0 < ρ s ∧ ρ s < r₀ := by
    intro s hs
    simp only [ρ]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (min_le_left r r')),
        mul_nonneg hs.1 (sub_nonneg.2 (min_le_right r r')), lt_min hr hr']
    · nlinarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (le_max_left r r')),
        mul_nonneg hs.1 (sub_nonneg.2 (le_max_right r r')), max_lt hrr hrr']
  refine ⟨fun s => multiSheetStrands c V D.q (ρ s), ⟨by linarith [Real.pi_pos], fun k => ?_,
    fun s hs t ht => ?_, fun s hs k => ?_⟩, fun k t _ => by simp [ρ], fun k t _ => by simp [ρ]⟩
  · -- Joint continuity on the product.
    have hpar : Continuous fun p : ℝ × ℝ => planeBranchAngularParameter D.q (ρ p.1) p.2 := by
      unfold planeBranchAngularParameter
      fun_prop
    have hmaps : MapsTo (fun p : ℝ × ℝ => planeBranchAngularParameter D.q (ρ p.1) p.2)
        (Icc 0 1 ×ˢ Icc b (b + 2 * π)) (ball 0 D.R) := fun p hp =>
      D.parameter_mem_ball (hρ p.1 hp.1).1.le (lt_of_lt_of_le (hρ p.1 hp.1).2 hr₀R) p.2
    exact continuousOn_const.mul ((hV k).continuousOn.comp hpar.continuousOn hmaps)
  · exact (D.isClosedStrandBraid_of_sheets hV hmono hr₀R hsep hc (hρ s hs).1 (hρ s hs).2
      b).injective t ht
  · exact (D.isClosedStrandBraid_of_sheets hV hmono hr₀R hsep hc (hρ s hs).1 (hρ s hs).2
      b).closing k

end MultiSheetData

/-! ### Changing the base angle of a periodic closed braid -/

/-- Periodic labelled strands with monodromy: a closed braid over every period. -/
structure IsPeriodicStrandBraid {S : ℕ} (K : Fin S → ℝ → ℂ) (τ : Equiv.Perm (Fin S)) :
    Prop where
  continuous : ∀ k, Continuous (K k)
  injective : ∀ t, Function.Injective fun k => K k t
  periodic : ∀ k t, K k (t + 2 * π) = K (τ k) t

namespace IsPeriodicStrandBraid

variable {S : ℕ} {K : Fin S → ℝ → ℂ} {τ : Equiv.Perm (Fin S)}

theorem isClosedStrandBraid (h : IsPeriodicStrandBraid K τ) (b : ℝ) :
    IsClosedStrandBraid K b (b + 2 * π) τ :=
  ⟨by linarith [Real.pi_pos], fun k => (h.continuous k).continuousOn,
    fun t _ => h.injective t, fun k => h.periodic k b⟩

/-- Translating a periodic closed braid in the parameter is an isotopy over a fixed
period. -/
theorem isotopic_shift (h : IsPeriodicStrandBraid K τ) (b c : ℝ) :
    ClosedStrandBraidIsotopic K (fun k t => K k (t + c)) b (b + 2 * π) τ := by
  refine ⟨fun s k t => K k (t + s * c), ⟨by linarith [Real.pi_pos], fun k => ?_,
    fun s _ t _ => h.injective _, fun s _ k => ?_⟩, fun k t _ => by simp,
    fun k t _ => by simp⟩
  · exact ((h.continuous k).comp (by fun_prop)).continuousOn
  · rw [show b + 2 * π + s * c = (b + s * c) + 2 * π by ring]
    exact h.periodic k _

/-- Representation by a word does not depend on the base angle. -/
theorem isRepresented_base (h : IsPeriodicStrandBraid K τ) {W : PositiveAdjacentWord S}
    {b : ℝ} (hW : IsRepresentedByPositiveWord K b (b + 2 * π) W) (b' : ℝ) :
    IsRepresentedByPositiveWord K b' (b' + 2 * π) W := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hshift := hW.comp_affine (u' := b') (v' := b' + 2 * π) (by linarith)
  have heq : (fun k t => K k (b + (t - b') / (b' + 2 * π - b') * (b + 2 * π - b))) =
      fun k t => K k (t + (b - b')) := by
    funext k t
    congr 1
    field_simp
    ring
  rw [heq] at hshift
  exact hshift.of_isotopic (h.isotopic_shift b' (b - b'))

/-- The winding number of the strand discriminant does not depend on the base angle. -/
theorem windingNumber_base (h : IsPeriodicStrandBraid K τ) (b b' : ℝ) :
    windingNumber (strandDiscriminant K) b' (b' + 2 * π) =
      windingNumber (strandDiscriminant K) b (b + 2 * π) := by
  rw [(h.isotopic_shift b' (b - b')).windingNumber_strandDiscriminant_eq]
  have hcl := h.isClosedStrandBraid b
  have harg := argChange_comp_add_const hcl.lt.le hcl.strandDiscriminant_continuousOn
    hcl.strandDiscriminant_ne_zero (b - b')
  unfold windingNumber
  congr 2
  rw [show b - (b - b') = b' by ring, show b + 2 * π - (b - b') = b' + 2 * π by ring] at harg
  rw [← harg]
  rfl

end IsPeriodicStrandBraid

namespace MultiSheetData

variable {S : ℕ} (D : MultiSheetData S)

/-- For finitely many nonzero complex numbers there is a direction `1 + i s` whose real
projection vanishes on none of them. -/
theorem exists_separating_projection (F : Finset ℂ) (hF : ∀ d ∈ F, d ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ d ∈ F, (c * d).re ≠ 0 := by
  classical
  let bad : Finset ℝ := (F.filter fun d => d.im ≠ 0).image fun d => d.re / d.im
  obtain ⟨s, -, hs⟩ := (Set.infinite_univ (α := ℝ)).exists_notMem_finset bad
  refine ⟨1 + s * Complex.I, fun h => by simpa using congrArg Complex.re h, fun d hd => ?_⟩
  have hre : ((1 + s * Complex.I) * d).re = d.re - s * d.im := by
    simp [Complex.mul_re]
  rw [hre]
  intro h0
  by_cases him : d.im = 0
  · apply hF d hd
    apply Complex.ext
    · simpa [him] using h0
    · exact him
  · apply hs
    refine Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, him⟩, ?_⟩
    field_simp
    linarith

/-- A fibre rotation separating all distinct constant terms of the sheets. -/
theorem exists_projection : ∃ c : ℂ, c ≠ 0 ∧
    ∀ k l, D.U k 0 ≠ D.U l 0 → (c * (D.U k 0 - D.U l 0)).re ≠ 0 := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_separating_projection
    ((Finset.univ.filter fun p : Fin S × Fin S => D.U p.1 0 ≠ D.U p.2 0).image
      fun p => D.U p.1 0 - D.U p.2 0) (by
        intro d hd
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
        exact sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
  exact ⟨c, hc, fun k l hkl => hF _ (Finset.mem_image.mpr
    ⟨(k, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkl⟩, rfl⟩)⟩

end MultiSheetData

end OnLeConjecture.Analytic
