/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyCoxeter

/-!
# The braid of the `d` preimages of a small circle under `t ↦ t^d`, read through a chart

Let `d ≥ 2` and let `Y` be a function on a neighbourhood of `0 ∈ ℂ` with a strict derivative
`a ≠ 0` at `0`. Over the circle `r^d e^{iθ}`, `θ ∈ [b, b + 2π]`, the `d` solutions of
`t^d = r^d e^{iθ}` are the points `smoothRootParameter d r k θ = r e^{i(θ - 2πk)/d}`. This module
proves that, for every sufficiently small `r > 0` and every base angle `b`, the closed braid
`θ ↦ Y (r e^{i(θ - 2πk)/d})` over `[b, b + 2π]` is represented through closed braids by the
Coxeter word `σ_0 σ_1 ⋯ σ_{d-2}` (`exists_radius_isRepresented_coxeter`). This is the local braid
at a smooth critical point of order `d` of the projection, in the subsection "Local factors,
without a generic-Morse projection" of Section 3 of the written proof of Statement E
(`statement-E-complete-proof.tex`), where `Y` is the inverse of a coordinate `t` with
`h - c = t^d`.

The proof has three steps.

* `rigidTurn_isotopic_cyclicShift`: the rigid turn `rigidTurnPath d` of the `d` points
  `-e^{-2πik/d}` by the angle `2π/d` during `[0, 1]` is isotopic through closed braids to the
  cyclic shift `cyclicShiftPath d` of `MultiSheetBraidCyclicShift.lean`, by the convex
  combination of the arguments: for labels `k < l` both argument differences lie in `(0, 2π)`.
  Hence the rigid turn is represented by the Coxeter word (`isRepresented_cyclicShiftPath`).
* An increasing affine change of parameter, multiplication by `a r e^{i(b/d - π)}` and a
  translation by `Y 0` carry the rigid turn to the linear model `θ ↦ Y 0 + a r e^{i(θ - 2πk)/d}`.
* The strict derivative gives `‖Y z - Y w - a (z - w)‖ ≤ ‖a‖ ‖z - w‖ / 2` on a small disc, so the
  straight-line interpolation between the linear model and `θ ↦ Y (r e^{i(θ - 2πk)/d})` is an
  isotopy through closed braids (`LevelPointSmooth.isotopic_of_norm_sub_lt`).
-/

@[expose] public noncomputable section

open Set Function Filter Metric Real
open scoped Topology

namespace OnLeConjecture.Analytic

open KnotTheory

variable {d : ℕ}

/-! ### The `d`-th roots over a circle -/

/-- The point `r e^{i(θ - 2πk)/d}`: for `k = 0, …, d - 1` these are the `d`-th roots of
`r^d e^{iθ}`. -/
def smoothRootParameter (d : ℕ) (r : ℝ) (k : Fin d) (θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((((θ - 2 * π * k.val) / d : ℝ) : ℂ) * Complex.I)

theorem smoothRootParameter_continuous (d : ℕ) (r : ℝ) (k : Fin d) :
    Continuous (smoothRootParameter d r k) := by
  unfold smoothRootParameter
  fun_prop

theorem norm_smoothRootParameter (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (k : Fin d) (θ : ℝ) :
    ‖smoothRootParameter d r k θ‖ = r := by
  rw [smoothRootParameter, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr]

theorem smoothRootParameter_pow (hd : d ≠ 0) (r : ℝ) (k : Fin d) (θ : ℝ) :
    smoothRootParameter d r k θ ^ d =
      ((r ^ d : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [smoothRootParameter, mul_pow, ← Complex.exp_nat_mul]
  have hdc : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have h : (d : ℂ) * ((((θ - 2 * π * k.val) / d : ℝ) : ℂ) * Complex.I) =
      (θ : ℂ) * Complex.I + ((-(k.val : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  push_cast
  ring

/-- The labels of the closing permutation: `k = (j + 1) mod d` for `j = (finRotate d)⁻¹ k`. -/
theorem finRotate_inv_val (k : Fin d) :
    k.val = (((finRotate d)⁻¹ k).val + 1) % d := by
  have h := finRotate_pow_apply_val 1 ((finRotate d)⁻¹ k)
  rw [pow_one, Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
  rw [Equiv.Perm.inv_def]
  exact h

/-- After one turn of the base angle the roots are relabelled by `(finRotate d)⁻¹`. -/
theorem smoothRootParameter_add_two_pi (r : ℝ) (k : Fin d) (θ : ℝ) :
    smoothRootParameter d r k (θ + 2 * π) = smoothRootParameter d r ((finRotate d)⁻¹ k) θ := by
  have hd : 0 < d := Fin.pos k
  set j := (finRotate d)⁻¹ k with hj
  have hdiv := Nat.div_add_mod (j.val + 1) d
  rw [← finRotate_inv_val k] at hdiv
  set q := (j.val + 1) / d
  have hdr : (d : ℝ) ≠ 0 := by positivity
  have hreal : (θ + 2 * π - 2 * π * k.val) / d = (θ - 2 * π * j.val) / d + q * (2 * π) := by
    have h1 : (d : ℝ) * q + k.val = j.val + 1 := by exact_mod_cast hdiv
    field_simp
    linear_combination (-2 * π) * h1
  unfold smoothRootParameter
  congr 1
  have h2 : (((q * (2 * π) : ℝ)) : ℂ) * Complex.I = ((q : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [hreal, Complex.ofReal_add, add_mul, Complex.exp_add, h2, Complex.exp_int_mul_two_pi_mul_I,
    mul_one]

theorem smoothRootParameter_injective (hd : 0 < d) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    Injective fun k : Fin d => smoothRootParameter d r k θ := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hmain : ∀ k l : Fin d, k.val < l.val →
      smoothRootParameter d r k θ ≠ smoothRootParameter d r l θ := by
    intro k l hkl he
    have hkl' : (k.val : ℝ) < l.val := by exact_mod_cast hkl
    have hl : (l.val : ℝ) < d := by exact_mod_cast l.isLt
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have he' := mul_left_cancel₀ hr' he
    have heq : (θ - 2 * π * k.val) / d - (θ - 2 * π * l.val) / d =
        2 * π * (l.val - k.val) / d := by ring
    refine exp_mul_I_ne_of_sub_mem ?_ ?_ he'
    · rw [heq]
      exact div_pos (mul_pos (by positivity) (by linarith)) hdr
    · rw [heq, div_lt_iff₀ hdr]
      nlinarith [pi_pos]
  intro k l hkl
  by_contra hne
  rcases lt_or_gt_of_ne (fun h : k.val = l.val => hne (Fin.ext h)) with h | h
  · exact hmain k l h hkl
  · exact hmain l k h hkl.symm

/-- Every `d`-th root of `r^d e^{iθ}` is one of the points `smoothRootParameter d r k θ`. -/
theorem exists_eq_smoothRootParameter (hd : 0 < d) {r : ℝ} (hr : 0 < r) {θ : ℝ} {z : ℂ}
    (hz : z ^ d = ((r ^ d : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :
    ∃ k : Fin d, z = smoothRootParameter d r k θ := by
  have : NeZero d := ⟨hd.ne'⟩
  set z₀ := smoothRootParameter d r ⟨0, hd⟩ θ with hz₀def
  have hz₀ : z₀ ≠ 0 := by
    intro h
    have := norm_smoothRootParameter d hr.le ⟨0, hd⟩ θ
    rw [← hz₀def, h, norm_zero] at this
    exact hr.ne this
  have hz₀d : z₀ ^ d = ((r ^ d : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
    smoothRootParameter_pow hd.ne' r _ θ
  have hpow : (z / z₀) ^ d = 1 := by
    rw [div_pow, hz, ← hz₀d]
    exact div_self (pow_ne_zero d hz₀)
  set ω := Complex.exp (-(2 * π * Complex.I / d)) with hωdef
  have hω : IsPrimitiveRoot ω d := by
    rw [hωdef, Complex.exp_neg]
    exact (Complex.isPrimitiveRoot_exp d hd.ne').inv
  obtain ⟨m, hm, hωm⟩ := hω.eq_pow_of_pow_eq_one hpow
  refine ⟨⟨m, hm⟩, ?_⟩
  have hrep : smoothRootParameter d r ⟨m, hm⟩ θ = z₀ * ω ^ m := by
    rw [hz₀def, hωdef, smoothRootParameter, smoothRootParameter, ← Complex.exp_nat_mul,
      mul_assoc (r : ℂ), ← Complex.exp_add]
    congr 2
    have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast [Fin.val_mk]
    field_simp
    ring
  rw [hrep, hωm, mul_div_cancel₀ _ hz₀]

/-! ### The rigid turn and the cyclic shift -/

/-- The rigid turn of the points `-e^{-2πik/d}` by the angle `2π/d` during `[0, 1]`. -/
def rigidTurnPath (d : ℕ) (k : Fin d) (t : ℝ) : ℂ :=
  Complex.exp (((π + 2 * π * (t - k.val) / d : ℝ) : ℂ) * Complex.I)

/-- The convex combination of the arguments of the rigid turn and of the cyclic shift. -/
def rigidTurnAngleFamily (d : ℕ) (s : ℝ) (k : Fin d) (t : ℝ) : ℂ :=
  Complex.exp ((((1 - s) * (π + 2 * π * (t - k.val) / d) +
    s * cyclicShiftAngle d (t - k.val) : ℝ) : ℂ) * Complex.I)

theorem rigidTurnAngleFamily_injective (hd : 2 ≤ d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Injective fun k : Fin d => rigidTurnAngleFamily d s k t := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hmain : ∀ k l : Fin d, k.val < l.val →
      rigidTurnAngleFamily d s k t ≠ rigidTurnAngleFamily d s l t := by
    intro k l hkl
    have hkl' : (k.val : ℝ) < l.val := by exact_mod_cast hkl
    have hl : (l.val : ℝ) + 1 ≤ d := by exact_mod_cast l.isLt
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    set d₁ := 2 * π * (l.val - k.val) / d with hd₁def
    set d₂ := cyclicShiftAngle d (t - k.val) - cyclicShiftAngle d (t - l.val) with hd₂def
    have hd₁ : 0 < d₁ := div_pos (mul_pos (by positivity) (by linarith)) hd0
    have hd₁' : d₁ < 2 * π := by
      rw [hd₁def, div_lt_iff₀ hd0]
      nlinarith [pi_pos]
    have hd₂ : 0 < d₂ := by
      have := cyclicShiftAngle_strictMono hd (show t - l.val < t - k.val by linarith)
      linarith
    have hd₂' : d₂ < 2 * π := cyclicShiftAngle_sub_lt hd (by linarith)
    have he : (1 - s) * (π + 2 * π * (t - k.val) / d) + s * cyclicShiftAngle d (t - k.val) -
        ((1 - s) * (π + 2 * π * (t - l.val) / d) + s * cyclicShiftAngle d (t - l.val)) =
        (1 - s) * d₁ + s * d₂ := by
      simp only [hd₁def, hd₂def]
      ring
    have hm₁ := mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (min_le_left d₁ d₂))
    have hm₂ := mul_nonneg hs.1 (sub_nonneg.2 (min_le_right d₁ d₂))
    have hM₁ := mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (le_max_left d₁ d₂))
    have hM₂ := mul_nonneg hs.1 (sub_nonneg.2 (le_max_right d₁ d₂))
    have hmin : 0 < min d₁ d₂ := lt_min hd₁ hd₂
    have hmax : max d₁ d₂ < 2 * π := max_lt hd₁' hd₂'
    apply exp_mul_I_ne_of_sub_mem
    · rw [he]
      nlinarith
    · rw [he]
      nlinarith
  intro k l hkl
  by_contra hne
  rcases lt_or_gt_of_ne (fun h : k.val = l.val => hne (Fin.ext h)) with h | h
  · exact hmain k l h hkl
  · exact hmain l k h hkl.symm

theorem rigidTurnAngleFamily_closing (hd : 2 ≤ d) (s : ℝ) (k : Fin d) :
    rigidTurnAngleFamily d s k 1 = rigidTurnAngleFamily d s ((finRotate d)⁻¹ k) 0 := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  set j := (finRotate d)⁻¹ k with hj
  have hk := finRotate_inv_val k
  rw [← hj] at hk
  unfold rigidTurnAngleFamily
  rcases Nat.lt_or_ge (j.val + 1) d with h | h
  · -- `k = j + 1`: the arguments agree.
    rw [Nat.mod_eq_of_lt h] at hk
    have hkr : (k.val : ℝ) = j.val + 1 := by exact_mod_cast hk
    congr 3
    rw [hkr]
    ring_nf
  · -- `j = d - 1` and `k = 0`: the arguments differ by `2π`.
    have hjd : j.val + 1 = d := by have := j.isLt; omega
    rw [hjd, Nat.mod_self] at hk
    have hkr : (k.val : ℝ) = 0 := by exact_mod_cast hk
    have hjr : (j.val : ℝ) = d - 1 := by
      have : ((j.val + 1 : ℕ) : ℝ) = d := by exact_mod_cast hjd
      push_cast at this
      linarith
    have hφ := cyclicShiftAngle_add hd (p := 1 - (d : ℝ)) ⟨le_rfl, by linarith⟩
    rw [show 1 - (d : ℝ) + d = 1 by ring] at hφ
    have harg : (1 - s) * (π + 2 * π * (1 - k.val) / d) + s * cyclicShiftAngle d (1 - k.val) =
        ((1 - s) * (π + 2 * π * (0 - j.val) / d) + s * cyclicShiftAngle d (0 - j.val)) +
          2 * π := by
      rw [hkr, hjr, sub_zero, show (0 : ℝ) - (d - 1) = 1 - d by ring, hφ]
      field_simp
      ring
    rw [harg]
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- **The rigid turn is isotopic to the cyclic shift.** -/
theorem rigidTurn_isotopic_cyclicShift (hd : 2 ≤ d) :
    ClosedStrandBraidIsotopic (rigidTurnPath d) (cyclicShiftPath d) 0 1 (finRotate d)⁻¹ := by
  refine ⟨rigidTurnAngleFamily d, IsClosedStrandBraidIsotopy.of_continuous zero_lt_one
    (fun k => ?_) (fun s hs t _ => rigidTurnAngleFamily_injective hd hs t)
    (fun s _ k => rigidTurnAngleFamily_closing hd s k), fun k t _ => ?_, fun k t _ => ?_⟩
  · unfold rigidTurnAngleFamily
    have := cyclicShiftAngle_continuous d
    fun_prop
  · simp [rigidTurnAngleFamily, rigidTurnPath]
  · simp [rigidTurnAngleFamily, cyclicShiftPath]

/-- **The rigid turn is represented by the Coxeter word.** -/
theorem isRepresented_rigidTurnPath (hd : 2 ≤ d) :
    IsRepresentedByPositiveWord (rigidTurnPath d) 0 1 (coxeterWord d) :=
  (isRepresented_cyclicShiftPath hd).of_isotopic (rigidTurn_isotopic_cyclicShift hd)

/-! ### Elementary operations on represented closed braids -/

namespace LevelPointSmooth

variable {S : ℕ} {K K' K₀ K₁ : Fin S → ℝ → ℂ} {u v : ℝ} {τ : Equiv.Perm (Fin S)}
  {W : PositiveAdjacentWord S}

/-- Representation only depends on the strands over the parameter interval. -/
theorem isRepresented_congr (h : IsRepresentedByPositiveWord K u v W)
    (he : ∀ k, ∀ t ∈ Icc u v, K' k t = K k t) : IsRepresentedByPositiveWord K' u v W := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.congr (fun k t ht => he (p k) t ht) (fun _ _ _ => rfl)⟩

/-- Representation is invariant under relabelling of the strands. -/
theorem isRepresented_relabel (h : IsRepresentedByPositiveWord K u v W)
    (σ : Equiv.Perm (Fin S)) : IsRepresentedByPositiveWord (fun k t => K (σ k) t) u v W := by
  obtain ⟨p, hp⟩ := h
  exact ⟨σ⁻¹ * p, hp.congr (fun k t _ => by simp) (fun _ _ _ => rfl)⟩

/-- Representation is invariant under translation by a constant. -/
theorem isRepresented_const_add (hK : IsClosedStrandBraid K u v τ)
    (h : IsRepresentedByPositiveWord K u v W) (c : ℂ) :
    IsRepresentedByPositiveWord (fun k t => c + K k t) u v W := by
  refine h.of_isotopic (τ := τ) ⟨fun s k t => (1 - s) * c + K k t,
    ⟨hK.lt, fun k => ?_, fun s _ t ht k l hkl => hK.injective t ht (add_left_cancel hkl),
      fun s _ k => by simp only [hK.closing k]⟩, fun k t _ => by simp, fun k t _ => by simp⟩
  have hs : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) := by fun_prop
  exact ((continuousOn_const.sub hs.continuousOn).mul continuousOn_const).add
    ((hK.continuousOn k).comp continuous_snd.continuousOn (fun p hp => hp.2))

/-- **Straight-line interpolation under a small perturbation.** If the pairwise differences of
`K₁` differ from those of the closed braid `K₀` by less than their norm, the straight-line
interpolation is an isotopy through closed braids. -/
theorem isotopic_of_norm_sub_lt (h₀ : IsClosedStrandBraid K₀ u v τ)
    (hc : ∀ k, ContinuousOn (K₁ k) (Icc u v)) (hclose : ∀ k, K₁ k v = K₁ (τ k) u)
    (hlt : ∀ t ∈ Icc u v, ∀ k l, k ≠ l →
      ‖(K₁ k t - K₁ l t) - (K₀ k t - K₀ l t)‖ < ‖K₀ k t - K₀ l t‖) :
    ClosedStrandBraidIsotopic K₀ K₁ u v τ := by
  refine ⟨fun s k t => (1 - s) * K₀ k t + s * K₁ k t, ⟨h₀.lt, fun k => ?_, ?_, ?_⟩,
    fun k t _ => by simp, fun k t _ => by simp⟩
  · have h0 := (h₀.continuousOn k).comp continuous_snd.continuousOn
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v) => hp.2)
    have h1 := (hc k).comp continuous_snd.continuousOn
      (fun p (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v) => hp.2)
    have hs : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) := by fun_prop
    exact ((continuousOn_const.sub hs.continuousOn).mul h0).add (hs.continuousOn.mul h1)
  · intro s hs t ht k l hkl
    by_contra hne
    have hlt' := hlt t ht k l hne
    have hkl' : (1 - (s : ℂ)) * K₀ k t + s * K₁ k t = (1 - s) * K₀ l t + s * K₁ l t := hkl
    have heq : K₀ k t - K₀ l t = -((s : ℂ) * ((K₁ k t - K₁ l t) - (K₀ k t - K₀ l t))) := by
      linear_combination hkl'
    have hle : ‖K₀ k t - K₀ l t‖ ≤ ‖(K₁ k t - K₁ l t) - (K₀ k t - K₀ l t)‖ :=
      calc ‖K₀ k t - K₀ l t‖ = ‖-((s : ℂ) * ((K₁ k t - K₁ l t) - (K₀ k t - K₀ l t)))‖ :=
            congrArg norm heq
        _ = s * ‖(K₁ k t - K₁ l t) - (K₀ k t - K₀ l t)‖ := by
            rw [norm_neg, norm_mul, Complex.norm_of_nonneg hs.1]
        _ ≤ ‖(K₁ k t - K₁ l t) - (K₀ k t - K₀ l t)‖ :=
            mul_le_of_le_one_left (norm_nonneg _) hs.2
    linarith
  · intro s _ k
    simp only [h₀.closing k, hclose k]

/-- The strict derivative bounds the deviation from the linear part on a small disc. -/
theorem exists_ball_norm_sub_sub_le {Y : ℂ → ℂ} {a : ℂ} (hY : HasStrictDerivAt Y a 0) {c : ℝ}
    (hc : 0 < c) : ∃ ρ > 0, ∀ z ∈ ball (0 : ℂ) ρ, ∀ w ∈ ball (0 : ℂ) ρ,
      ‖Y z - Y w - a * (z - w)‖ ≤ c * ‖z - w‖ := by
  have h1 : HasStrictFDerivAt Y (ContinuousLinearMap.toSpanSingleton ℂ a) 0 :=
    hY.hasStrictFDerivAt
  have h := (hasStrictFDerivAt_iff_isLittleO.mp h1).def hc
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  refine ⟨ρ, hρ, fun z hz w hw => ?_⟩
  have hp : (z, w) ∈ ball ((0 : ℂ), (0 : ℂ)) ρ := by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (by simpa using hz) (by simpa using hw)
  have := hball (z, w) hp
  simpa [mul_comm] using this

end LevelPointSmooth

open LevelPointSmooth

/-! ### The braid of the `d` branches -/

/-- The linear model `θ ↦ a r e^{i(θ - 2πk)/d}` is a closed braid over every base period. -/
theorem isClosedStrandBraid_smul_smoothRootParameter (hd : 0 < d) {a : ℂ} (ha : a ≠ 0) {r : ℝ}
    (hr : 0 < r) (b : ℝ) :
    IsClosedStrandBraid (fun k θ => a * smoothRootParameter d r k θ) b (b + 2 * π)
      (finRotate d)⁻¹ where
  lt := by linarith [pi_pos]
  continuousOn k := (continuous_const.mul (smoothRootParameter_continuous d r k)).continuousOn
  injective θ _ k l hkl := smoothRootParameter_injective hd hr θ (mul_left_cancel₀ ha hkl)
  closing k := by simp only [smoothRootParameter_add_two_pi]

/-- **The linear model is represented by the Coxeter word.** -/
theorem isRepresented_smul_smoothRootParameter (hd : 2 ≤ d) {a : ℂ} (ha : a ≠ 0) {r : ℝ}
    (hr : 0 < r) (b : ℝ) :
    IsRepresentedByPositiveWord (fun k θ => a * smoothRootParameter d r k θ) b (b + 2 * π)
      (coxeterWord d) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hbb : b < b + 2 * π := by linarith
  have hdr : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  set φ : ℝ → ℝ := fun θ => (θ - b) / (2 * π) with hφdef
  have hφc : Continuous φ := by fun_prop
  have hφm : MapsTo φ (Icc b (b + 2 * π)) (Icc 0 1) := fun θ hθ =>
    ⟨div_nonneg (by linarith [hθ.1]) h2π.le, (div_le_one h2π).mpr (by linarith [hθ.2])⟩
  have hφb : φ b = 0 := by simp [hφdef]
  have hφe : φ (b + 2 * π) = 1 := by
    simp only [hφdef, add_sub_cancel_left]
    exact div_self h2π.ne'
  have hT : IsClosedStrandBraid (rigidTurnPath d) 0 1 (finRotate d)⁻¹ :=
    (rigidTurn_isotopic_cyclicShift hd).left
  have hTb : IsClosedStrandBraid (fun k θ => rigidTurnPath d k (φ θ)) b (b + 2 * π)
      (finRotate d)⁻¹ := hT.comp_time hbb hφc.continuousOn hφm hφb hφe
  have hRb : IsRepresentedByPositiveWord (fun k θ => rigidTurnPath d k (φ θ)) b (b + 2 * π)
      (coxeterWord d) := by
    refine isRepresented_congr ((isRepresented_rigidTurnPath hd).comp_affine hbb)
      fun k θ _ => ?_
    change rigidTurnPath d k ((θ - b) / (2 * π)) =
      rigidTurnPath d k (0 + (θ - b) / (b + 2 * π - b) * (1 - 0))
    rw [add_sub_cancel_left, sub_zero, mul_one, zero_add]
  set c₁ : ℂ := a * r * Complex.exp ((((b / d - π) : ℝ) : ℂ) * Complex.I) with hc₁def
  have hc₁ : c₁ ≠ 0 := mul_ne_zero (mul_ne_zero ha (by exact_mod_cast hr.ne'))
    (Complex.exp_ne_zero _)
  refine isRepresented_congr (hRb.const_mul hTb hc₁) fun k θ _ => ?_
  rw [hc₁def, smoothRootParameter, rigidTurnPath]
  rw [show a * (r * Complex.exp ((((θ - 2 * π * k.val) / d : ℝ) : ℂ) * Complex.I)) =
      a * r * Complex.exp ((((θ - 2 * π * k.val) / d : ℝ) : ℂ) * Complex.I) by ring,
    mul_assoc (a * r), ← Complex.exp_add]
  congr 2
  simp only [hφdef]
  push_cast
  field_simp
  ring

/-- **The braid of the `d` branches is the Coxeter braid.** Let `Y` have the strict derivative
`a ≠ 0` at `0`. For every sufficiently small `r > 0` and every base angle `b`, the closed braid
`θ ↦ Y (r e^{i(θ - 2πk)/d})` over `[b, b + 2π]` is represented through closed braids by the
Coxeter word. -/
theorem exists_radius_isRepresented_coxeter (hd : 2 ≤ d) {Y : ℂ → ℂ} {a : ℂ} (ha : a ≠ 0)
    (hY : HasStrictDerivAt Y a 0) :
    ∃ ρ > 0, ∀ r : ℝ, 0 < r → r < ρ → ∀ b : ℝ,
      IsClosedStrandBraid (fun k θ => Y (smoothRootParameter d r k θ)) b (b + 2 * π)
        (finRotate d)⁻¹ ∧
      IsRepresentedByPositiveWord (fun k θ => Y (smoothRootParameter d r k θ)) b (b + 2 * π)
        (coxeterWord d) := by
  have hd0 : 0 < d := by omega
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  obtain ⟨ρ, hρ, hest⟩ := exists_ball_norm_sub_sub_le hY (half_pos hna)
  refine ⟨ρ, hρ, fun r hr hrρ b => ?_⟩
  set z := smoothRootParameter d r with hzdef
  have hzball : ∀ k θ, z k θ ∈ ball (0 : ℂ) ρ := fun k θ => by
    rw [mem_ball, dist_zero_right, hzdef, norm_smoothRootParameter d hr.le]
    exact hrρ
  -- `Y` is Lipschitz, hence continuous, on the disc.
  have hlip : ∀ z₁ ∈ ball (0 : ℂ) ρ, ∀ z₂ ∈ ball (0 : ℂ) ρ,
      dist (Y z₁) (Y z₂) ≤ (3 / 2 * ‖a‖) * dist z₁ z₂ := by
    intro z₁ h₁ z₂ h₂
    have h := hest z₁ h₁ z₂ h₂
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖Y z₁ - Y z₂‖ = ‖(Y z₁ - Y z₂ - a * (z₁ - z₂)) + a * (z₁ - z₂)‖ := by ring_nf
      _ ≤ ‖Y z₁ - Y z₂ - a * (z₁ - z₂)‖ + ‖a * (z₁ - z₂)‖ := norm_add_le _ _
      _ ≤ ‖a‖ / 2 * ‖z₁ - z₂‖ + ‖a‖ * ‖z₁ - z₂‖ := by rw [norm_mul]; linarith
      _ = 3 / 2 * ‖a‖ * ‖z₁ - z₂‖ := by ring
  have hYc : ContinuousOn Y (ball (0 : ℂ) ρ) := (LipschitzOnWith.of_dist_le' hlip).continuousOn
  have hEc : ∀ k, ContinuousOn (fun θ => Y (z k θ)) (Icc b (b + 2 * π)) := fun k =>
    hYc.comp (smoothRootParameter_continuous d r k).continuousOn fun θ _ => hzball k θ
  have hEclose : ∀ k, Y (z k (b + 2 * π)) = Y (z ((finRotate d)⁻¹ k) b) := fun k => by
    rw [hzdef, smoothRootParameter_add_two_pi]
  -- The linear model `Y 0 + a z`.
  have hM := isClosedStrandBraid_smul_smoothRootParameter hd0 ha hr b
  have hM' : IsClosedStrandBraid (fun k θ => Y 0 + a * z k θ) b (b + 2 * π) (finRotate d)⁻¹ :=
    ⟨hM.lt, fun k => continuousOn_const.add (hM.continuousOn k),
      fun θ hθ k l hkl => hM.injective θ hθ (add_left_cancel hkl),
      fun k => by rw [hzdef, smoothRootParameter_add_two_pi]⟩
  have hMrep := isRepresented_const_add hM (isRepresented_smul_smoothRootParameter hd ha hr b)
    (Y 0)
  -- The straight-line isotopy.
  have hiso : ClosedStrandBraidIsotopic (fun k θ => Y 0 + a * z k θ) (fun k θ => Y (z k θ))
      b (b + 2 * π) (finRotate d)⁻¹ := by
    refine isotopic_of_norm_sub_lt hM' hEc hEclose fun θ _ k l hkl => ?_
    have hzkl : z k θ - z l θ ≠ 0 :=
      sub_ne_zero.mpr fun h => hkl (smoothRootParameter_injective hd0 hr θ h)
    have hpos : 0 < ‖z k θ - z l θ‖ := norm_pos_iff.mpr hzkl
    have h1 := hest (z k θ) (hzball k θ) (z l θ) (hzball l θ)
    have e1 : (Y (z k θ) - Y (z l θ)) - (Y 0 + a * z k θ - (Y 0 + a * z l θ)) =
        Y (z k θ) - Y (z l θ) - a * (z k θ - z l θ) := by ring
    have e2 : Y 0 + a * z k θ - (Y 0 + a * z l θ) = a * (z k θ - z l θ) := by ring
    rw [e1, e2, norm_mul]
    nlinarith
  exact ⟨hiso.right, hMrep.of_isotopic hiso.symm⟩

end OnLeConjecture.Analytic
