/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Algebra.Order.Round

/-!
# Continuous logarithms, argument changes, and winding numbers

A continuous map `γ : [u, v] → ℂ ∖ {0}` has a continuous logarithm, obtained
by lifting the path through Mathlib's covering map `Complex.isCoveringMap_exp`.
Two continuous logarithms on a preconnected set differ by one fixed integer
multiple of `2πi`. Consequently the imaginary part of the total change of a
continuous logarithm, `argChange γ u v`, does not depend on the chosen
logarithm. For a closed path it is `2π` times an integer, the winding number
`windingNumber γ u v`.

The argument change is additive under pointwise products and under
concatenation of intervals, and it is invariant under nonzero constant factors
and monotone reparametrizations. The winding number is invariant under
continuous homotopies through nonvanishing closed paths. The proof of
homotopy invariance uses Mathlib's homotopy lifting `IsCoveringMap.liftHomotopy`.
-/

@[expose] public noncomputable section

open Set Filter Topology Real

namespace OnLeConjecture.Analytic

/-- `L` is a continuous logarithm of `γ` on the closed interval `[u, v]`. -/
def IsContinuousLogOn (γ L : ℝ → ℂ) (u v : ℝ) : Prop :=
  ContinuousOn L (Icc u v) ∧ ∀ s ∈ Icc u v, Complex.exp (L s) = γ s

theorem two_pi_I_ne_zero : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
  simp [Real.pi_ne_zero]

/-- Two continuous functions with equal exponentials on a preconnected set
differ by one fixed integer multiple of `2πi`. -/
theorem exists_int_eq_add_of_exp_eq {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {L₁ L₂ : X → ℂ} (h₁ : ContinuousOn L₁ S)
    (h₂ : ContinuousOn L₂ S) (he : ∀ s ∈ S, Complex.exp (L₁ s) = Complex.exp (L₂ s))
    {s₀ : X} (hs₀ : s₀ ∈ S) :
    ∃ n : ℤ, ∀ s ∈ S, L₁ s = L₂ s + n * (2 * π * Complex.I) := by
  let g : X → ℝ := fun s => ((L₁ s - L₂ s) / (2 * π * Complex.I)).re
  have hg : ContinuousOn g S :=
    Complex.continuous_re.comp_continuousOn ((h₁.sub h₂).div_const _)
  have hgint : ∀ s ∈ S, ∃ n : ℤ, g s = n ∧ L₁ s = L₂ s + n * (2 * π * Complex.I) := by
    intro s hs
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (he s hs)
    refine ⟨n, ?_, hn⟩
    simp only [g, hn, add_sub_cancel_left, mul_div_assoc, div_self two_pi_I_ne_zero, mul_one,
      Complex.intCast_re]
  obtain ⟨n₀, hn₀, -⟩ := hgint s₀ hs₀
  refine ⟨n₀, fun s hs => ?_⟩
  obtain ⟨n, hn, hL⟩ := hgint s hs
  suffices n = n₀ by rw [hL, this]
  by_contra hne
  have hhalf : ∀ t ∈ S, g t ≠ (min n n₀ : ℤ) + 1 / 2 := by
    intro t ht hgt
    obtain ⟨m, hm, -⟩ := hgint t ht
    rw [hm] at hgt
    have h2 : (2 * m : ℤ) = 2 * (min n n₀ : ℤ) + 1 := by
      have : (2 : ℝ) * m = 2 * (min n n₀ : ℤ) + 1 := by linarith
      exact_mod_cast this
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hmem : ((min n n₀ : ℤ) : ℝ) + 1 / 2 ∈ Icc (g s) (g s₀) := by
      rw [hn, hn₀, min_eq_left hlt.le]
      have : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨t, ht, hgt⟩ := hS.intermediate_value hs hs₀ hg hmem
    exact hhalf t ht hgt
  · have hmem : ((min n n₀ : ℤ) : ℝ) + 1 / 2 ∈ Icc (g s₀) (g s) := by
      rw [hn, hn₀, min_eq_right hlt.le]
      have : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨t, ht, hgt⟩ := hS.intermediate_value hs₀ hs hg hmem
    exact hhalf t ht hgt

/-- Two continuous logarithms of one function on `[u, v]` differ by a fixed
integer multiple of `2πi`. -/
theorem IsContinuousLogOn.exists_int_eq_add {γ L₁ L₂ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (h₁ : IsContinuousLogOn γ L₁ u v) (h₂ : IsContinuousLogOn γ L₂ u v) :
    ∃ n : ℤ, ∀ s ∈ Icc u v, L₁ s = L₂ s + n * (2 * π * Complex.I) :=
  exists_int_eq_add_of_exp_eq isPreconnected_Icc h₁.1 h₂.1
    (fun s hs => (h₁.2 s hs).trans (h₂.2 s hs).symm) (left_mem_Icc.mpr huv)

/-- The affine parametrization of `[u, v]` by the unit interval. -/
def intervalAffine (u v : ℝ) (t : ℝ) : ℝ := u + t * (v - u)

theorem intervalAffine_mem {u v : ℝ} (huv : u ≤ v) (t : unitInterval) :
    intervalAffine u v t ∈ Icc u v := by
  have h0 := t.2.1
  have h1 := t.2.2
  constructor
  · simp only [intervalAffine]
    nlinarith
  · simp only [intervalAffine]
    nlinarith

/-- The inverse affine map from `[u, v]` to the unit interval. -/
def intervalUnit (u v : ℝ) (s : ℝ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((s - u) / (v - u))

theorem continuous_intervalUnit (u v : ℝ) :
    Continuous (intervalUnit u v) :=
  continuous_projIcc.comp ((continuous_id.sub continuous_const).div_const _)

theorem intervalAffine_intervalUnit {u v : ℝ} (huv : u < v) {s : ℝ} (hs : s ∈ Icc u v) :
    intervalAffine u v (intervalUnit u v s) = s := by
  have hvu : 0 < v - u := sub_pos.mpr huv
  have hmem : (s - u) / (v - u) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hs.1) hvu.le
    · rw [div_le_one hvu]
      linarith [hs.2]
  simp only [intervalUnit, intervalAffine, Set.projIcc_of_mem _ hmem]
  field_simp
  ring

theorem intervalUnit_left (u v : ℝ) : intervalUnit u v u = 0 := by
  apply Subtype.ext
  simp [intervalUnit, Set.projIcc]

theorem intervalUnit_right {u v : ℝ} (huv : u < v) : intervalUnit u v v = 1 := by
  apply Subtype.ext
  have hvu : (v - u) ≠ 0 := (sub_pos.mpr huv).ne'
  simp [intervalUnit, Set.projIcc, div_self hvu]

/-- The covering projection `exp : ℂ → ℂ ∖ {0}` in subtype form. -/
def expToNonzero (z : ℂ) : {w : ℂ // w ≠ 0} := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

theorem isCoveringMap_expToNonzero : IsCoveringMap expToNonzero :=
  Complex.isCoveringMap_exp

/-- Every continuous nonvanishing function on `[u, v]` has a continuous
logarithm there, defined and continuous on all of `ℝ`. -/
theorem exists_continuous_log {γ : ℝ → ℂ} {u v : ℝ} (hγ : ContinuousOn γ (Icc u v))
    (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧ ∀ s ∈ Icc u v, Complex.exp (L s) = γ s := by
  rcases lt_or_ge u v with huv | hvu
  · have hφ : ∀ t : unitInterval, intervalAffine u v t ∈ Icc u v :=
      intervalAffine_mem huv.le
    have hcont : Continuous fun t : unitInterval => γ (intervalAffine u v t) :=
      hγ.comp_continuous (by unfold intervalAffine; fun_prop) hφ
    let η : C(unitInterval, {w : ℂ // w ≠ 0}) :=
      ⟨fun t => ⟨γ (intervalAffine u v t), h0 _ (hφ t)⟩, hcont.subtype_mk _⟩
    have hu : u ∈ Icc u v := left_mem_Icc.mpr huv.le
    have hη0 : η 0 = expToNonzero (Complex.log (γ u)) := by
      apply Subtype.ext
      simp [η, expToNonzero, intervalAffine, Complex.exp_log (h0 u hu)]
    let Λ := isCoveringMap_expToNonzero.liftPath η (Complex.log (γ u)) hη0
    have hΛ := isCoveringMap_expToNonzero.liftPath_lifts η (Complex.log (γ u)) hη0
    refine ⟨fun s => Λ (intervalUnit u v s),
      Λ.continuous.comp (continuous_intervalUnit u v), ?_⟩
    intro s hs
    have h := congrArg Subtype.val (congrFun hΛ (intervalUnit u v s))
    simp only [Function.comp_apply, expToNonzero] at h
    rw [h]
    change γ (intervalAffine u v (intervalUnit u v s)) = γ s
    rw [intervalAffine_intervalUnit huv hs]
  · refine ⟨fun _ => Complex.log (γ u), continuous_const, ?_⟩
    intro s hs
    have hsu : s = u := le_antisymm (hs.2.trans hvu) hs.1
    subst hsu
    exact Complex.exp_log (h0 _ hs)

theorem exists_isContinuousLogOn {γ : ℝ → ℂ} {u v : ℝ} (hγ : ContinuousOn γ (Icc u v))
    (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) : ∃ L : ℝ → ℂ, IsContinuousLogOn γ L u v := by
  obtain ⟨L, hL, he⟩ := exists_continuous_log hγ h0
  exact ⟨L, hL.continuousOn, he⟩

/-- The change of a continuous argument of `γ` along `[u, v]`. It is zero by
convention when `γ` has no continuous logarithm on `[u, v]`. -/
def argChange (γ : ℝ → ℂ) (u v : ℝ) : ℝ := by
  classical
  exact if h : ∃ L : ℝ → ℂ, IsContinuousLogOn γ L u v then
    (h.choose v - h.choose u).im else 0

/-- Every continuous logarithm computes the argument change. -/
theorem IsContinuousLogOn.argChange_eq {γ L : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hL : IsContinuousLogOn γ L u v) : argChange γ u v = (L v - L u).im := by
  have hex : ∃ L : ℝ → ℂ, IsContinuousLogOn γ L u v := ⟨L, hL⟩
  rw [argChange, dif_pos hex]
  obtain ⟨n, hn⟩ := hex.choose_spec.exists_int_eq_add huv hL
  rw [hn v (right_mem_Icc.mpr huv), hn u (left_mem_Icc.mpr huv)]
  ring_nf

/-- The winding number of `γ` along `[u, v]`, the nearest integer to the
argument change divided by `2π`. It is the exact quotient for closed paths. -/
def windingNumber (γ : ℝ → ℂ) (u v : ℝ) : ℤ := round (argChange γ u v / (2 * π))

/-- For a closed path, the total change of a continuous logarithm is the
winding number times `2πi`. -/
theorem IsContinuousLogOn.sub_eq_windingNumber {γ L : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hL : IsContinuousLogOn γ L u v) (hloop : γ u = γ v) :
    L v - L u = windingNumber γ u v * (2 * π * Complex.I) := by
  have he : Complex.exp (L v) = Complex.exp (L u) := by
    rw [hL.2 v (right_mem_Icc.mpr huv), hL.2 u (left_mem_Icc.mpr huv), hloop]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have harg : argChange γ u v = 2 * π * n := by
    rw [hL.argChange_eq huv, hn]
    simp only [add_sub_cancel_left, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hw : windingNumber γ u v = n := by
    rw [windingNumber, harg, mul_div_cancel_left₀ _ (by positivity : (2 * π) ≠ 0), round_intCast]
  rw [hw, hn]
  ring

/-- For a closed nonvanishing path the argument change is `2π` times the winding number. -/
theorem argChange_eq_two_pi_mul_windingNumber {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) (hloop : γ u = γ v) :
    argChange γ u v = 2 * π * windingNumber γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [hL.argChange_eq huv, hL.sub_eq_windingNumber huv hloop]
  simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- A winding number is determined by any continuous logarithm. -/
theorem IsContinuousLogOn.windingNumber_eq {γ L : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hL : IsContinuousLogOn γ L u v) (hloop : γ u = γ v) {n : ℤ}
    (hn : L v - L u = n * (2 * π * Complex.I)) : windingNumber γ u v = n := by
  have h := (hL.sub_eq_windingNumber huv hloop).symm.trans hn
  have h' := mul_right_cancel₀ two_pi_I_ne_zero h
  exact_mod_cast h'

/-! ### Algebraic properties of the argument change -/

theorem IsContinuousLogOn.mul {γ₁ γ₂ L₁ L₂ : ℝ → ℂ} {u v : ℝ}
    (h₁ : IsContinuousLogOn γ₁ L₁ u v) (h₂ : IsContinuousLogOn γ₂ L₂ u v) :
    IsContinuousLogOn (γ₁ * γ₂) (L₁ + L₂) u v :=
  ⟨h₁.1.add h₂.1, fun s hs => by
    simp only [Pi.add_apply, Pi.mul_apply, Complex.exp_add, h₁.2 s hs, h₂.2 s hs]⟩

theorem IsContinuousLogOn.inv {γ L : ℝ → ℂ} {u v : ℝ} (h : IsContinuousLogOn γ L u v) :
    IsContinuousLogOn γ⁻¹ (-L) u v :=
  ⟨h.1.neg, fun s hs => by simp only [Pi.neg_apply, Pi.inv_apply, Complex.exp_neg, h.2 s hs]⟩

theorem IsContinuousLogOn.pow {γ L : ℝ → ℂ} {u v : ℝ} (h : IsContinuousLogOn γ L u v)
    (n : ℕ) : IsContinuousLogOn (γ ^ n) (fun s => (n : ℂ) * L s) u v :=
  ⟨continuousOn_const.mul h.1, fun s hs => by
    simp only [Pi.pow_apply, ← h.2 s hs, ← Complex.exp_nat_mul]⟩

theorem IsContinuousLogOn.const_mul {γ L : ℝ → ℂ} {u v : ℝ} (h : IsContinuousLogOn γ L u v)
    {c : ℂ} (hc : c ≠ 0) :
    IsContinuousLogOn (fun s => c * γ s) (fun s => Complex.log c + L s) u v :=
  ⟨continuousOn_const.add h.1, fun s hs => by
    simp only [Complex.exp_add, Complex.exp_log hc, h.2 s hs]⟩

theorem IsContinuousLogOn.mono {γ L : ℝ → ℂ} {u v u' v' : ℝ} (h : IsContinuousLogOn γ L u v)
    (hu : u ≤ u') (hv : v' ≤ v) : IsContinuousLogOn γ L u' v' :=
  ⟨h.1.mono (Icc_subset_Icc hu hv), fun s hs => h.2 s ⟨hu.trans hs.1, hs.2.trans hv⟩⟩

theorem IsContinuousLogOn.congr {γ γ' L : ℝ → ℂ} {u v : ℝ} (h : IsContinuousLogOn γ L u v)
    (heq : ∀ s ∈ Icc u v, γ s = γ' s) : IsContinuousLogOn γ' L u v :=
  ⟨h.1, fun s hs => (h.2 s hs).trans (heq s hs)⟩

/-- A continuous logarithm composed with a reparametrization. -/
theorem IsContinuousLogOn.comp {γ L : ℝ → ℂ} {u v : ℝ} (h : IsContinuousLogOn γ L u v)
    {φ : ℝ → ℝ} {u' v' : ℝ} (hφ : ContinuousOn φ (Icc u' v'))
    (hmaps : MapsTo φ (Icc u' v') (Icc u v)) :
    IsContinuousLogOn (γ ∘ φ) (L ∘ φ) u' v' :=
  ⟨h.1.comp hφ hmaps, fun s hs => h.2 (φ s) (hmaps hs)⟩

/-- `exp ∘ f` has continuous logarithm `f`. -/
theorem isContinuousLogOn_exp {f : ℝ → ℂ} {u v : ℝ} (hf : ContinuousOn f (Icc u v)) :
    IsContinuousLogOn (fun s => Complex.exp (f s)) f u v :=
  ⟨hf, fun _ _ => rfl⟩

theorem argChange_mul {γ₁ γ₂ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ₁ : ContinuousOn γ₁ (Icc u v)) (h₁ : ∀ s ∈ Icc u v, γ₁ s ≠ 0)
    (hγ₂ : ContinuousOn γ₂ (Icc u v)) (h₂ : ∀ s ∈ Icc u v, γ₂ s ≠ 0) :
    argChange (γ₁ * γ₂) u v = argChange γ₁ u v + argChange γ₂ u v := by
  obtain ⟨L₁, hL₁⟩ := exists_isContinuousLogOn hγ₁ h₁
  obtain ⟨L₂, hL₂⟩ := exists_isContinuousLogOn hγ₂ h₂
  rw [(hL₁.mul hL₂).argChange_eq huv, hL₁.argChange_eq huv, hL₂.argChange_eq huv]
  simp only [Pi.add_apply, Complex.sub_im, Complex.add_im]
  ring

theorem argChange_inv {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) :
    argChange γ⁻¹ u v = -argChange γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [hL.inv.argChange_eq huv, hL.argChange_eq huv]
  simp only [Pi.neg_apply, Complex.sub_im, Complex.neg_im]
  ring

theorem argChange_pow {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) (n : ℕ) :
    argChange (γ ^ n) u v = n * argChange γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [(hL.pow n).argChange_eq huv, hL.argChange_eq huv]
  simp only [← mul_sub, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
    add_zero]

theorem argChange_const_mul {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    argChange (fun s => c * γ s) u v = argChange γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [(hL.const_mul hc).argChange_eq huv, hL.argChange_eq huv]
  ring_nf

theorem argChange_congr {γ γ' : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0)
    (heq : ∀ s ∈ Icc u v, γ s = γ' s) : argChange γ' u v = argChange γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [(hL.congr heq).argChange_eq huv, hL.argChange_eq huv]

theorem argChange_exp {f : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v) (hf : ContinuousOn f (Icc u v)) :
    argChange (fun s => Complex.exp (f s)) u v = (f v - f u).im :=
  (isContinuousLogOn_exp hf).argChange_eq huv

/-- Additivity of the argument change under concatenation of intervals. -/
theorem argChange_add_argChange {γ : ℝ → ℂ} {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w)
    (hγ : ContinuousOn γ (Icc u w)) (h0 : ∀ s ∈ Icc u w, γ s ≠ 0) :
    argChange γ u v + argChange γ v w = argChange γ u w := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [(hL.mono le_rfl hvw).argChange_eq huv, (hL.mono huv le_rfl).argChange_eq hvw,
    hL.argChange_eq (huv.trans hvw)]
  simp only [Complex.sub_im]
  ring

/-- Reparametrization by a continuous map carrying `[u', v']` into `[u, v]`
and its endpoints to `u` and `v`. -/
theorem argChange_comp {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0)
    {φ : ℝ → ℝ} {u' v' : ℝ} (huv' : u' ≤ v') (hφ : ContinuousOn φ (Icc u' v'))
    (hmaps : MapsTo φ (Icc u' v') (Icc u v)) (hu : φ u' = u) (hv : φ v' = v) :
    argChange (γ ∘ φ) u' v' = argChange γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  rw [(hL.comp hφ hmaps).argChange_eq huv', hL.argChange_eq huv]
  simp only [Function.comp_apply, hu, hv]

/-- Translation of the parameter. -/
theorem argChange_comp_add_const {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) (c : ℝ) :
    argChange (fun s => γ (s + c)) (u - c) (v - c) = argChange γ u v := by
  apply argChange_comp huv hγ h0 (by linarith) (by fun_prop)
  · intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · ring
  · ring

theorem argChange_finset_prod {ι : Type*} (s : Finset ι) {γ : ι → ℝ → ℂ} {u v : ℝ}
    (huv : u ≤ v) (hγ : ∀ i ∈ s, ContinuousOn (γ i) (Icc u v))
    (h0 : ∀ i ∈ s, ∀ t ∈ Icc u v, γ i t ≠ 0) :
    argChange (fun t => ∏ i ∈ s, γ i t) u v = ∑ i ∈ s, argChange (γ i) u v := by
  classical
  choose L hL using fun i (hi : i ∈ s) => exists_isContinuousLogOn (hγ i hi) (h0 i hi)
  have hprod : IsContinuousLogOn (fun t => ∏ i ∈ s, γ i t)
      (fun t => ∑ i ∈ s.attach, L i.1 i.2 t) u v := by
    refine ⟨continuousOn_finsetSum _ fun i _ => (hL i.1 i.2).1, fun t ht => ?_⟩
    rw [Complex.exp_sum]
    change ∏ x ∈ s.attach, Complex.exp (L x.1 x.2 t) = ∏ i ∈ s, γ i t
    rw [← Finset.prod_attach s (fun i => γ i t)]
    exact Finset.prod_congr rfl fun i _ => (hL i.1 i.2).2 t ht
  rw [hprod.argChange_eq huv, ← Finset.sum_attach s (fun i => argChange (γ i) u v)]
  rw [← Finset.sum_sub_distrib, Complex.im_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [(hL i.1 i.2).argChange_eq huv, Complex.sub_im]

/-! ### Winding numbers of closed paths -/

theorem windingNumber_mul {γ₁ γ₂ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ₁ : ContinuousOn γ₁ (Icc u v)) (h₁ : ∀ s ∈ Icc u v, γ₁ s ≠ 0) (hl₁ : γ₁ u = γ₁ v)
    (hγ₂ : ContinuousOn γ₂ (Icc u v)) (h₂ : ∀ s ∈ Icc u v, γ₂ s ≠ 0) (hl₂ : γ₂ u = γ₂ v) :
    windingNumber (γ₁ * γ₂) u v = windingNumber γ₁ u v + windingNumber γ₂ u v := by
  obtain ⟨L₁, hL₁⟩ := exists_isContinuousLogOn hγ₁ h₁
  obtain ⟨L₂, hL₂⟩ := exists_isContinuousLogOn hγ₂ h₂
  apply (hL₁.mul hL₂).windingNumber_eq huv (by simp only [Pi.mul_apply, hl₁, hl₂])
  simp only [Pi.add_apply]
  rw [show L₁ v + L₂ v - (L₁ u + L₂ u) = (L₁ v - L₁ u) + (L₂ v - L₂ u) by ring,
    hL₁.sub_eq_windingNumber huv hl₁, hL₂.sub_eq_windingNumber huv hl₂]
  push_cast
  ring

theorem windingNumber_pow {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) (hl : γ u = γ v) (n : ℕ) :
    windingNumber (γ ^ n) u v = n * windingNumber γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  apply (hL.pow n).windingNumber_eq huv (by simp only [Pi.pow_apply, hl])
  rw [← mul_sub, hL.sub_eq_windingNumber huv hl]
  push_cast
  ring

theorem windingNumber_const_mul {γ : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0) (hl : γ u = γ v)
    {c : ℂ} (hc : c ≠ 0) :
    windingNumber (fun s => c * γ s) u v = windingNumber γ u v := by
  obtain ⟨L, hL⟩ := exists_isContinuousLogOn hγ h0
  apply (hL.const_mul hc).windingNumber_eq huv (by simp only [hl])
  rw [show Complex.log c + L v - (Complex.log c + L u) = L v - L u by ring,
    hL.sub_eq_windingNumber huv hl]

theorem windingNumber_congr {γ γ' : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hγ : ContinuousOn γ (Icc u v)) (h0 : ∀ s ∈ Icc u v, γ s ≠ 0)
    (heq : ∀ s ∈ Icc u v, γ s = γ' s) : windingNumber γ' u v = windingNumber γ u v := by
  rw [windingNumber, windingNumber, argChange_congr huv hγ h0 heq]

theorem windingNumber_finset_prod {ι : Type*} (s : Finset ι) {γ : ι → ℝ → ℂ} {u v : ℝ}
    (huv : u ≤ v) (hγ : ∀ i ∈ s, ContinuousOn (γ i) (Icc u v))
    (h0 : ∀ i ∈ s, ∀ t ∈ Icc u v, γ i t ≠ 0) (hl : ∀ i ∈ s, γ i u = γ i v) :
    windingNumber (fun t => ∏ i ∈ s, γ i t) u v = ∑ i ∈ s, windingNumber (γ i) u v := by
  have hprod := argChange_finset_prod s huv hγ h0
  have hcont : ContinuousOn (fun t => ∏ i ∈ s, γ i t) (Icc u v) :=
    continuousOn_finsetProd _ hγ
  have hne : ∀ t ∈ Icc u v, ∏ i ∈ s, γ i t ≠ 0 :=
    fun t ht => Finset.prod_ne_zero_iff.mpr fun i hi => h0 i hi t ht
  rw [argChange_eq_two_pi_mul_windingNumber huv hcont hne
    (Finset.prod_congr rfl fun i hi => hl i hi)] at hprod
  rw [Finset.sum_congr rfl fun i hi =>
    argChange_eq_two_pi_mul_windingNumber huv (hγ i hi) (h0 i hi) (hl i hi),
    ← Finset.mul_sum] at hprod
  have h := mul_left_cancel₀ (by positivity : (2 * π) ≠ 0) hprod
  exact_mod_cast h

/-- A path `exp ∘ f` closes with winding number `n` when `f` increases by `2πin`. -/
theorem windingNumber_exp {f : ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hf : ContinuousOn f (Icc u v)) {n : ℤ} (hn : f v - f u = n * (2 * π * Complex.I)) :
    windingNumber (fun s => Complex.exp (f s)) u v = n := by
  have hloop : Complex.exp (f u) = Complex.exp (f v) := by
    rw [show f v = f u + n * (2 * π * Complex.I) by rw [← hn]; ring, Complex.exp_add,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  exact (isContinuousLogOn_exp hf).windingNumber_eq huv hloop hn

/-- The standard circle `θ ↦ exp(iθ)` winds once over `[u, u + 2π]`. -/
theorem windingNumber_exp_mul_I (u : ℝ) :
    windingNumber (fun θ : ℝ => Complex.exp (θ * Complex.I)) u (u + 2 * π) = 1 := by
  apply windingNumber_exp (by linarith [Real.pi_pos]) (by fun_prop)
  push_cast
  ring

/-- A constant nonzero path has winding number zero. -/
theorem windingNumber_const {c : ℂ} (hc : c ≠ 0) {u v : ℝ} (huv : u ≤ v) :
    windingNumber (fun _ => c) u v = 0 := by
  have hL : IsContinuousLogOn (fun _ => c) (fun _ => Complex.log c) u v :=
    ⟨continuousOn_const, fun _ _ => Complex.exp_log hc⟩
  exact hL.windingNumber_eq huv rfl (by simp)

/-! ### Homotopy invariance -/

/-- The winding number is constant along a continuous homotopy through closed
nonvanishing paths, parametrized by `τ ∈ [0, 1]`. -/
theorem windingNumber_eq_of_homotopy {H : ℝ → ℝ → ℂ} {u v : ℝ} (huv : u ≤ v)
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc 0 1 ×ˢ Icc u v))
    (h0 : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc u v, H τ s ≠ 0)
    (hloop : ∀ τ ∈ Icc (0 : ℝ) 1, H τ u = H τ v) :
    windingNumber (H 0) u v = windingNumber (H 1) u v := by
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst heq
    have h00 := h0 0 (left_mem_Icc.mpr zero_le_one) u (left_mem_Icc.mpr le_rfl)
    have h10 := h0 1 (right_mem_Icc.mpr zero_le_one) u (left_mem_Icc.mpr le_rfl)
    have hc0 : windingNumber (H 0) u u = 0 := by
      rw [windingNumber_congr le_rfl continuousOn_const (fun _ _ => h00)
        (fun s hs => by rw [show s = u from le_antisymm hs.2 hs.1])]
      exact windingNumber_const h00 le_rfl
    have hc1 : windingNumber (H 1) u u = 0 := by
      rw [windingNumber_congr le_rfl continuousOn_const (fun _ _ => h10)
        (fun s hs => by rw [show s = u from le_antisymm hs.2 hs.1])]
      exact windingNumber_const h10 le_rfl
    rw [hc0, hc1]
  have hmemτ : ∀ τ : unitInterval, (τ : ℝ) ∈ Icc (0 : ℝ) 1 := fun τ => τ.2
  have hmems : ∀ t : unitInterval, intervalAffine u v t ∈ Icc u v := intervalAffine_mem huv
  -- The homotopy on the unit square: first coordinate along the path, second the homotopy.
  have hcont : Continuous fun q : unitInterval × unitInterval =>
      H (q.2 : ℝ) (intervalAffine u v q.1) := by
    have hm : ∀ q : unitInterval × unitInterval,
        ((q.2 : ℝ), intervalAffine u v q.1) ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v :=
      fun q => ⟨hmemτ q.2, hmems q.1⟩
    exact hH.comp_continuous (by unfold intervalAffine; fun_prop) hm
  let Hc : C(unitInterval × unitInterval, {w : ℂ // w ≠ 0}) :=
    ⟨fun q => ⟨H (q.2 : ℝ) (intervalAffine u v q.1), h0 _ (hmemτ q.2) _ (hmems q.1)⟩,
      hcont.subtype_mk _⟩
  -- Lift the left edge `τ ↦ H τ u`.
  have hu : u ∈ Icc u v := left_mem_Icc.mpr huv
  have hedge : Continuous fun τ : unitInterval => H (τ : ℝ) u := by
    have hm : ∀ τ : unitInterval, ((τ : ℝ), u) ∈ Icc (0 : ℝ) 1 ×ˢ Icc u v :=
      fun τ => ⟨hmemτ τ, hu⟩
    exact hH.comp_continuous (by fun_prop) hm
  let η : C(unitInterval, {w : ℂ // w ≠ 0}) :=
    ⟨fun τ => ⟨H (τ : ℝ) u, h0 _ (hmemτ τ) _ hu⟩, hedge.subtype_mk _⟩
  have hη0 : η 0 = expToNonzero (Complex.log (H 0 u)) := by
    apply Subtype.ext
    simp [η, expToNonzero, Complex.exp_log (h0 0 (left_mem_Icc.mpr zero_le_one) u hu)]
  let f₀ := isCoveringMap_expToNonzero.liftPath η (Complex.log (H 0 u)) hη0
  have hf₀ := isCoveringMap_expToNonzero.liftPath_lifts η (Complex.log (H 0 u)) hη0
  have hH0 : ∀ τ, Hc (0, τ) = expToNonzero (f₀ τ) := by
    intro τ
    have h := congrFun hf₀ τ
    simp only [Function.comp_apply] at h
    rw [h]
    apply Subtype.ext
    simp [Hc, η, intervalAffine]
  let Λ := isCoveringMap_expToNonzero.liftHomotopy Hc f₀ hH0
  have hΛ := isCoveringMap_expToNonzero.liftHomotopy_lifts Hc f₀ hH0
  have hΛexp : ∀ q, Complex.exp (Λ q) = H (q.2 : ℝ) (intervalAffine u v q.1) := by
    intro q
    exact congrArg Subtype.val (congrFun hΛ q)
  -- The total change along each closed path in the family.
  let D : ℝ → ℂ := fun τ =>
    Λ (1, Set.projIcc 0 1 zero_le_one τ) - Λ (0, Set.projIcc 0 1 zero_le_one τ)
  have hDcont : Continuous D := by
    apply Continuous.sub <;> exact Λ.continuous.comp (by fun_prop)
  have hDexp : ∀ τ ∈ Icc (0 : ℝ) 1, Complex.exp (D τ) = Complex.exp 0 := by
    intro τ hτ
    rw [Complex.exp_sub, hΛexp, hΛexp, Complex.exp_zero]
    simp only [Set.projIcc_of_mem _ hτ]
    simp only [intervalAffine, Set.Icc.coe_one, one_mul, Set.Icc.coe_zero, zero_mul, add_zero,
      add_sub_cancel]
    rw [hloop τ hτ, div_self (h0 τ hτ v (right_mem_Icc.mpr huv))]
  obtain ⟨n, hn⟩ := exists_int_eq_add_of_exp_eq isPreconnected_Icc hDcont.continuousOn
    continuousOn_const hDexp (left_mem_Icc.mpr zero_le_one)
  -- Each path has the logarithm `s ↦ Λ (s, τ)`.
  have hlog : ∀ τ ∈ Icc (0 : ℝ) 1, windingNumber (H τ) u v = n := by
    intro τ hτ
    let L : ℝ → ℂ := fun s => Λ (intervalUnit u v s, Set.projIcc 0 1 zero_le_one τ)
    have hL : IsContinuousLogOn (H τ) L u v := by
      refine ⟨(Λ.continuous.comp (by
        exact (continuous_intervalUnit u v).prodMk continuous_const)).continuousOn, ?_⟩
      intro s hs
      rw [hΛexp]
      simp only [Set.projIcc_of_mem _ hτ, intervalAffine_intervalUnit hlt hs]
    apply hL.windingNumber_eq huv (hloop τ hτ)
    have h := hn τ hτ
    simp only [D, zero_add] at h
    simp only [L, intervalUnit_left, intervalUnit_right hlt]
    exact h
  rw [hlog 0 (left_mem_Icc.mpr zero_le_one), hlog 1 (right_mem_Icc.mpr zero_le_one)]

end OnLeConjecture.Analytic
