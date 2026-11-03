/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WindingNumberArgument
public import Mathlib.Data.Sign.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Signed crossings of a continuous argument

Let `g : [s, t] → ℝ` be continuous. If `g` takes no integer value on `[s, t]`,
then `⌊g s⌋ = ⌊g t⌋`, by the intermediate value theorem. If `g` meets the
integers at finitely many interior times, each with a nonzero derivative, then
`⌊g t⌋ - ⌊g s⌋` is the sum of the signs of those derivatives.

Applied to `g = α / π - 1 / 2`, where `α` is a continuous argument of a nonzero
path `γ`, the integer values of `g` are exactly the zeros of `Re γ`. At such a
zero the derivative of `α` has the sign of `-Im γ · Re γ'`, which is the positive
crossing convention of the native braid modules. Hence the signed number of
zeros of `Re γ` is `⌊α t / π - 1 / 2⌋ - ⌊α s / π - 1 / 2⌋`.
-/

@[expose] public noncomputable section

open Set Filter Topology Real

namespace OnLeConjecture.Analytic

/-- The integer sign of a real number: `1` for positive, `-1` for negative,
and `0` for zero. -/
def realSignInt (x : ℝ) : ℤ := ((SignType.sign x : SignType) : ℤ)

theorem realSignInt_of_pos {x : ℝ} (hx : 0 < x) : realSignInt x = 1 := by
  simp [realSignInt, sign_pos hx]

theorem realSignInt_of_neg {x : ℝ} (hx : x < 0) : realSignInt x = -1 := by
  simp [realSignInt, sign_neg hx]

theorem realSignInt_div_pos {x y : ℝ} (hy : 0 < y) : realSignInt (x / y) = realSignInt x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [realSignInt_of_neg (div_neg_of_neg_of_pos hx hy), realSignInt_of_neg hx]
  · simp [hx]
  · rw [realSignInt_of_pos (div_pos hx hy), realSignInt_of_pos hx]

/-- A continuous function without integer values has constant integer part. -/
theorem floor_eq_floor_of_no_int {g : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hg : ContinuousOn g (Icc s t)) (hno : ∀ θ ∈ Icc s t, ∀ k : ℤ, g θ ≠ k) :
    ⌊g s⌋ = ⌊g t⌋ := by
  have hs : s ∈ Icc s t := left_mem_Icc.mpr hst
  have ht : t ∈ Icc s t := right_mem_Icc.mpr hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : g s ≤ ((⌊g s⌋ + 1 : ℤ) : ℝ) := by
      push_cast
      exact (Int.lt_floor_add_one _).le
    have h2 : (((⌊g s⌋ + 1 : ℤ)) : ℝ) ≤ g t := by
      have : ⌊g s⌋ + 1 ≤ ⌊g t⌋ := hlt
      exact (Int.cast_le.mpr this).trans (Int.floor_le _)
    obtain ⟨θ, hθ, hgθ⟩ := isPreconnected_Icc.intermediate_value hs ht hg ⟨h1, h2⟩
    exact hno θ hθ _ hgθ
  · have h1 : g t ≤ ((⌊g t⌋ + 1 : ℤ) : ℝ) := by
      push_cast
      exact (Int.lt_floor_add_one _).le
    have h2 : (((⌊g t⌋ + 1 : ℤ)) : ℝ) ≤ g s := by
      have : ⌊g t⌋ + 1 ≤ ⌊g s⌋ := hlt
      exact (Int.cast_le.mpr this).trans (Int.floor_le _)
    obtain ⟨θ, hθ, hgθ⟩ := isPreconnected_Icc.intermediate_value ht hs hg ⟨h1, h2⟩
    exact hno θ hθ _ hgθ

/-- One transverse integer crossing changes the integer part by the sign of the
derivative. -/
theorem floor_sub_floor_of_single_crossing {g : ℝ → ℝ} {s t θ₀ g' : ℝ}
    (hg : ContinuousOn g (Icc s t)) (hs : s < θ₀) (ht : θ₀ < t)
    (hint : ∃ k : ℤ, g θ₀ = k)
    (honly : ∀ θ ∈ Icc s t, θ ≠ θ₀ → ∀ k : ℤ, g θ ≠ k)
    (hd : HasDerivAt g g' θ₀) (hg' : g' ≠ 0) :
    ⌊g t⌋ - ⌊g s⌋ = realSignInt g' := by
  obtain ⟨k, hk⟩ := hint
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hnear : ∀ᶠ x in 𝓝 θ₀, |g x - k| < 1 := by
    have hc : ContinuousAt (fun x => g x - k) θ₀ := hd.continuousAt.sub continuousAt_const
    have h0 : g θ₀ - (k : ℝ) = 0 := by rw [hk]; ring
    have := hc.tendsto
    rw [h0] at this
    exact this.eventually (isOpen_lt continuous_abs continuous_const |>.mem_nhds (by simp))
  -- The sign of the slope near `θ₀`.
  have hsl : ∀ᶠ x in 𝓝[≠] θ₀, 0 < g' * slope g θ₀ x := by
    have ht' : Tendsto (fun x => g' * slope g θ₀ x) (𝓝[≠] θ₀) (𝓝 (g' * g')) :=
      hslope.const_mul g'
    exact ht'.eventually (Ioi_mem_nhds (mul_self_pos.mpr hg'))
  have hall : ∀ᶠ x in 𝓝 θ₀, x ≠ θ₀ → 0 < g' * slope g θ₀ x ∧ |g x - k| < 1 := by
    have h' : ∀ᶠ x in 𝓝 θ₀, x ≠ θ₀ → 0 < g' * slope g θ₀ x := by
      simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hsl
    filter_upwards [h', hnear] with x hx hx' hne
    exact ⟨hx hne, hx'⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hall
  set η := min δ (min (θ₀ - s) (t - θ₀)) / 2 with hη
  have hηpos : 0 < η := by
    have : 0 < min δ (min (θ₀ - s) (t - θ₀)) := lt_min hδ (lt_min (by linarith) (by linarith))
    positivity
  have hηδ : η < δ := by
    have : min δ (min (θ₀ - s) (t - θ₀)) ≤ δ := min_le_left _ _
    linarith
  have hηs : η < θ₀ - s := by
    have : min δ (min (θ₀ - s) (t - θ₀)) ≤ θ₀ - s := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hηt : η < t - θ₀ := by
    have : min δ (min (θ₀ - s) (t - θ₀)) ≤ t - θ₀ := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  set x₁ := θ₀ - η with hx₁
  set x₂ := θ₀ + η with hx₂
  have hd₁ : dist x₁ θ₀ < δ := by
    rw [Real.dist_eq, show x₁ - θ₀ = -η by ring, abs_neg, abs_of_pos hηpos]
    exact hηδ
  have hd₂ : dist x₂ θ₀ < δ := by
    rw [Real.dist_eq, show x₂ - θ₀ = η by ring, abs_of_pos hηpos]
    exact hηδ
  obtain ⟨hs₁, hn₁⟩ := hball hd₁ (by linarith)
  obtain ⟨hs₂, hn₂⟩ := hball hd₂ (by linarith)
  rw [slope_def_field, hk, show x₁ - θ₀ = -η by ring] at hs₁
  rw [slope_def_field, hk, show x₂ - θ₀ = η by ring] at hs₂
  have hleft : ⌊g s⌋ = ⌊g x₁⌋ := by
    apply floor_eq_floor_of_no_int (by linarith) (hg.mono (Icc_subset_Icc le_rfl (by linarith)))
    intro θ hθ
    exact honly θ ⟨hθ.1, by linarith [hθ.2]⟩ (by linarith [hθ.2])
  have hright : ⌊g x₂⌋ = ⌊g t⌋ := by
    apply floor_eq_floor_of_no_int (by linarith) (hg.mono (Icc_subset_Icc (by linarith) le_rfl))
    intro θ hθ
    exact honly θ ⟨by linarith [hθ.1], hθ.2⟩ (by linarith [hθ.1])
  rw [hleft, ← hright]
  rw [abs_lt] at hn₁ hn₂
  have hη0 : η ≠ 0 := hηpos.ne'
  have e₁ : 0 < g' * (k - g x₁) := by
    have h := hs₁
    rw [show g' * ((g x₁ - k) / -η) = (g' * (k - g x₁)) / η by field_simp; ring] at h
    exact (div_pos_iff_of_pos_right hηpos).mp h
  have e₂ : 0 < g' * (g x₂ - k) := by
    have h := hs₂
    rw [show g' * ((g x₂ - k) / η) = (g' * (g x₂ - k)) / η by ring] at h
    exact (div_pos_iff_of_pos_right hηpos).mp h
  rcases lt_or_gt_of_ne hg' with hneg | hpos
  · -- Negative derivative: the function decreases through `k`.
    have hlt₁ : (k : ℝ) < g x₁ := by nlinarith
    have hgt₂ : g x₂ < k := by nlinarith
    have hf₁ : ⌊g x₁⌋ = k := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    have hf₂ : ⌊g x₂⌋ = k - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hf₁, hf₂, realSignInt_of_neg hneg]
    ring
  · -- Positive derivative: the function increases through `k`.
    have hlt₁ : g x₁ < k := by nlinarith
    have hgt₂ : (k : ℝ) < g x₂ := by nlinarith
    have hf₁ : ⌊g x₁⌋ = k - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    have hf₂ : ⌊g x₂⌋ = k := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    rw [hf₁, hf₂, realSignInt_of_pos hpos]
    ring

/-- Finitely many transverse integer crossings change the integer part by
the sum of the signs of the derivatives. -/
theorem floor_sub_floor_eq_sum_sign {g g' : ℝ → ℝ} (Z : Finset ℝ) :
    ∀ {s t : ℝ}, s ≤ t → ContinuousOn g (Icc s t) →
      (∀ θ ∈ Icc s t, (∃ k : ℤ, g θ = k) ↔ θ ∈ Z) → (∀ θ ∈ Z, θ ∈ Ioo s t) →
      (∀ θ ∈ Z, HasDerivAt g (g' θ) θ ∧ g' θ ≠ 0) →
      ⌊g t⌋ - ⌊g s⌋ = ∑ θ ∈ Z, realSignInt (g' θ) := by
  induction Z using Finset.strongInduction with
  | H Z ih =>
    intro s t hst hg hiff hin hder
    by_cases hZ : Z.Nonempty
    · set θ₀ := Z.min' hZ with hθ₀def
      have hθ₀Z : θ₀ ∈ Z := Z.min'_mem hZ
      have hθ₀in := hin θ₀ hθ₀Z
      have hsθ₀ : s < θ₀ := hθ₀in.1
      set Z' := Z.erase θ₀ with hZ'
      -- The next crossing, or the right endpoint.
      obtain ⟨n, hθ₀n, hnt, hge⟩ : ∃ n : ℝ, θ₀ < n ∧ n ≤ t ∧ ∀ θ ∈ Z', n ≤ θ := by
        by_cases hZ'ne : Z'.Nonempty
        · refine ⟨Z'.min' hZ'ne, ?_, ?_, fun θ hθ => Z'.min'_le θ hθ⟩
          · have hmem := Z'.min'_mem hZ'ne
            have hne : Z'.min' hZ'ne ≠ θ₀ := (Finset.mem_erase.mp hmem).1
            exact lt_of_le_of_ne (Z.min'_le _ (Finset.mem_erase.mp hmem).2) hne.symm
          · exact (hin _ (Finset.mem_erase.mp (Z'.min'_mem hZ'ne)).2).2.le
        · refine ⟨t, hθ₀in.2, le_rfl, fun θ hθ => (hZ'ne ⟨θ, hθ⟩).elim⟩
      set m := (θ₀ + n) / 2 with hm
      have hθ₀m : θ₀ < m := by linarith
      have hmn : m < n := by linarith
      have hmt : m ≤ t := by linarith
      -- The crossing at `θ₀` between `s` and `m`.
      have h1 : ⌊g m⌋ - ⌊g s⌋ = realSignInt (g' θ₀) := by
        apply floor_sub_floor_of_single_crossing (hg.mono (Icc_subset_Icc le_rfl hmt))
          hθ₀in.1 hθ₀m ((hiff θ₀ (Ioo_subset_Icc_self hθ₀in)).mpr hθ₀Z) _
          (hder θ₀ hθ₀Z).1 (hder θ₀ hθ₀Z).2
        intro θ hθ hne k hk
        have hθZ : θ ∈ Z := (hiff θ ⟨hθ.1, hθ.2.trans hmt⟩).mp ⟨k, hk⟩
        have := hge θ (Finset.mem_erase.mpr ⟨hne, hθZ⟩)
        linarith [hθ.2]
      -- The remaining crossings between `m` and `t`.
      have h2 : ⌊g t⌋ - ⌊g m⌋ = ∑ θ ∈ Z', realSignInt (g' θ) := by
        apply ih Z' (Finset.erase_ssubset hθ₀Z) hmt (hg.mono (Icc_subset_Icc (by linarith) le_rfl))
        · intro θ hθ
          constructor
          · intro hk
            have hθZ := (hiff θ ⟨by linarith [hθ.1], hθ.2⟩).mp hk
            exact Finset.mem_erase.mpr ⟨by intro h; rw [h] at hθ; linarith [hθ.1], hθZ⟩
          · intro hθZ'
            exact (hiff θ ⟨by linarith [hθ.1], hθ.2⟩).mpr (Finset.mem_erase.mp hθZ').2
        · intro θ hθ
          exact ⟨lt_of_lt_of_le hmn (hge θ hθ), (hin θ (Finset.mem_erase.mp hθ).2).2⟩
        · intro θ hθ
          exact hder θ (Finset.mem_erase.mp hθ).2
      rw [← Finset.add_sum_erase Z _ hθ₀Z, ← h1, ← h2]
      ring
    · have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZ
      subst hZe
      rw [Finset.sum_empty, sub_eq_zero]
      exact (floor_eq_floor_of_no_int hst hg fun θ hθ k hk =>
        Finset.notMem_empty θ ((hiff θ hθ).mp ⟨k, hk⟩)).symm

/-- The integer values of `α / π - 1 / 2` for a continuous argument `α` are the
zeros of the real part. -/
theorem IsContinuousLogOn.exists_int_iff_re_eq_zero {γ L : ℝ → ℂ} {u v : ℝ}
    (hL : IsContinuousLogOn γ L u v) {θ : ℝ} (hθ : θ ∈ Icc u v) :
    (∃ k : ℤ, (L θ).im / π - 1 / 2 = k) ↔ (γ θ).re = 0 := by
  rw [hL.re_eq_zero_iff hθ, Real.cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (L θ).im = (k + 1 / 2) * π := by
      field_simp at hk
      linarith [hk, Real.pi_pos]
    rw [this]
    ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk]
    field_simp
    ring

/-- The signed number of zeros of `Re γ` along a continuous logarithm. The sign
of a zero is the sign of `-Im γ · Re γ'`. -/
theorem IsContinuousLogOn.floor_sub_floor_eq_sum_crossingSign {γ L : ℝ → ℂ} {u v : ℝ}
    (huv : u ≤ v) (hL : IsContinuousLogOn γ L u v) (Z : Finset ℝ)
    (hZ : ∀ θ ∈ Icc u v, (γ θ).re = 0 ↔ θ ∈ Z) (hZin : ∀ θ ∈ Z, θ ∈ Ioo u v)
    (γ' : ℝ → ℂ) (hder : ∀ θ ∈ Z, HasDerivAt γ (γ' θ) θ ∧ (γ' θ).re ≠ 0) :
    ⌊(L v).im / π - 1 / 2⌋ - ⌊(L u).im / π - 1 / 2⌋ =
      ∑ θ ∈ Z, realSignInt (-(γ θ).im * (γ' θ).re) := by
  have hγne : ∀ θ ∈ Icc u v, γ θ ≠ 0 := fun θ hθ => by
    rw [← hL.2 θ hθ]
    exact Complex.exp_ne_zero _
  have hcont : ContinuousOn (fun θ => (L θ).im / π - 1 / 2) (Icc u v) :=
    ((Complex.continuous_im.comp_continuousOn hL.1).div_const π).sub continuousOn_const
  let g' : ℝ → ℝ := fun θ => (γ' θ / γ θ).im / π
  have hsum := floor_sub_floor_eq_sum_sign (g := fun θ => (L θ).im / π - 1 / 2) (g' := g') Z huv
    hcont (fun θ hθ => (hL.exists_int_iff_re_eq_zero hθ).trans (hZ θ hθ)) hZin (by
      intro θ hθZ
      have hθ := hZin θ hθZ
      have hLd := hL.hasDerivAt hθ (hder θ hθZ).1
      have him : HasDerivAt (fun t => (L t).im) (γ' θ / γ θ).im θ := by
        have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hLd
        simpa only [Function.comp_def, Complex.imCLM_apply] using h
      refine ⟨(him.div_const π).sub_const (1 / 2), ?_⟩
      have hre : (γ θ).re = 0 := (hZ θ (Ioo_subset_Icc_self hθ)).mpr hθZ
      have hne := hγne θ (Ioo_subset_Icc_self hθ)
      have him0 : (γ θ).im ≠ 0 := by
        intro h0
        exact hne (Complex.ext hre h0)
      have hn : 0 < Complex.normSq (γ θ) := Complex.normSq_pos.mpr hne
      have hdivim : (γ' θ / γ θ).im = -((γ' θ).re * (γ θ).im) / Complex.normSq (γ θ) := by
        rw [Complex.div_im, hre]
        ring
      have : (γ' θ).re * (γ θ).im ≠ 0 := mul_ne_zero (hder θ hθZ).2 him0
      change (γ' θ / γ θ).im / π ≠ 0
      rw [hdivim]
      exact div_ne_zero (div_ne_zero (neg_ne_zero.mpr this) hn.ne') Real.pi_ne_zero)
  rw [hsum]
  refine Finset.sum_congr rfl fun θ hθZ => ?_
  have hθ := hZin θ hθZ
  have hre : (γ θ).re = 0 := (hZ θ (Ioo_subset_Icc_self hθ)).mpr hθZ
  have hne := hγne θ (Ioo_subset_Icc_self hθ)
  have hn : 0 < Complex.normSq (γ θ) := Complex.normSq_pos.mpr hne
  have hdivim : (γ' θ / γ θ).im = (-(γ θ).im * (γ' θ).re) / Complex.normSq (γ θ) := by
    rw [Complex.div_im, hre]
    ring
  change realSignInt ((γ' θ / γ θ).im / π) = _
  rw [hdivim, realSignInt_div_pos Real.pi_pos, realSignInt_div_pos hn]

end OnLeConjecture.Analytic
