/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidCyclicShift
public import OnLeConjecture.Analytic.MultiSheetBraidSheets

/-!
# The full twist: a rigid turn of a closed braid is the prefix `fullTwistWord`

Let `W` be a positive word on `S` strands, and let `C_W` be its canonical closed braid over
`[0, 1]` (`positiveWordModel W 0 1`). This module proves Lemmas `J14:lem:rotation` and
`J14:lem:product` of the written proof in the following form: the closed braid
`t ↦ e^{2πit} C_W(t)`, in which the whole configuration turns once counterclockwise while
the word `W` is performed, is isotopic through closed braids to the canonical closed braid of
`fullTwistWord S ++ W`.

The isotopy is a composite of five isotopies, each of explicit form:

1. separation of the turn from the word (`J14:lem:product`): the turn is performed first,
   at the real configuration `k ↦ k`, and the word afterwards;
2. transport of the base configuration of the turn from the real configuration to the
   semicircle configuration `Q`, along the straight segment between them;
3. replacement of the rigid turn of `Q` by the cyclic shift, by convex combination of
   the arguments (the argument differences stay in `(0, 2π)`);
4. straight-line interpolation from the cyclic shift to the canonical path of
   `fullTwistWord S` (`cyclicShift_separation`), with the transport segments shrunk to
   constants;
5. a monotone reparametrization identifying the result with the canonical closed braid of
   `fullTwistWord S ++ W` (concatenation formula).

As a consequence, multiplying a closed braid represented by `W` by the base circle
`θ ↦ ρ e^{iθ}` gives a closed braid represented by `fullTwistWord S ++ W`.
-/

@[expose] public noncomputable section

open Set Filter Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-! ### Concatenation of four strand families -/

/-- The concatenation of four strand families on the quarters of `[0, 1]`, each family
parametrized by `[0, 1]`. -/
def quarterPath {S : ℕ} (F₁ F₂ F₃ F₄ : Fin S → ℝ → ℂ) : Fin S → ℝ → ℂ := fun k t =>
  if t ≤ 1 / 4 then F₁ k (4 * t) else if t ≤ 1 / 2 then F₂ k (4 * t - 1)
  else if t ≤ 3 / 4 then F₃ k (4 * t - 2) else F₄ k (4 * t - 3)

theorem quarterPath_of_le_quarter {S : ℕ} (F₁ F₂ F₃ F₄ : Fin S → ℝ → ℂ) (k : Fin S) {t : ℝ}
    (ht : t ≤ 1 / 4) : quarterPath F₁ F₂ F₃ F₄ k t = F₁ k (4 * t) := by
  unfold quarterPath
  rw [if_pos ht]

theorem quarterPath_of_mem_second {S : ℕ} (F₁ F₂ F₃ F₄ : Fin S → ℝ → ℂ) (k : Fin S) {t : ℝ}
    (ht₁ : 1 / 4 < t) (ht₂ : t ≤ 1 / 2) : quarterPath F₁ F₂ F₃ F₄ k t = F₂ k (4 * t - 1) := by
  unfold quarterPath
  rw [if_neg (not_le.mpr ht₁), if_pos ht₂]

theorem quarterPath_of_mem_third {S : ℕ} (F₁ F₂ F₃ F₄ : Fin S → ℝ → ℂ) (k : Fin S) {t : ℝ}
    (ht₁ : 1 / 2 < t) (ht₂ : t ≤ 3 / 4) : quarterPath F₁ F₂ F₃ F₄ k t = F₃ k (4 * t - 2) := by
  unfold quarterPath
  rw [if_neg (not_le.mpr (show (1 : ℝ) / 4 < t by linarith)), if_neg (not_le.mpr ht₁),
    if_pos ht₂]

theorem quarterPath_of_gt {S : ℕ} (F₁ F₂ F₃ F₄ : Fin S → ℝ → ℂ) (k : Fin S) {t : ℝ}
    (ht : 3 / 4 < t) : quarterPath F₁ F₂ F₃ F₄ k t = F₄ k (4 * t - 3) := by
  unfold quarterPath
  rw [if_neg (not_le.mpr (show (1 : ℝ) / 4 < t by linarith)),
    if_neg (not_le.mpr (show (1 : ℝ) / 2 < t by linarith)), if_neg (not_le.mpr ht)]

/-- Four families of strand families, jointly continuous, matching at the seams, injective
on `[0, 1]²` and closing up with the monodromy `τ`, give an isotopy through closed braids. -/
theorem quarterFamily_isotopy {S : ℕ} {τ : Equiv.Perm (Fin S)}
    (G₁ G₂ G₃ G₄ : ℝ → Fin S → ℝ → ℂ)
    (hc₁ : ∀ k, Continuous fun p : ℝ × ℝ => G₁ p.1 k p.2)
    (hc₂ : ∀ k, Continuous fun p : ℝ × ℝ => G₂ p.1 k p.2)
    (hc₃ : ∀ k, Continuous fun p : ℝ × ℝ => G₃ p.1 k p.2)
    (hc₄ : ∀ k, Continuous fun p : ℝ × ℝ => G₄ p.1 k p.2)
    (h₁₂ : ∀ s k, G₁ s k 1 = G₂ s k 0) (h₂₃ : ∀ s k, G₂ s k 1 = G₃ s k 0)
    (h₃₄ : ∀ s k, G₃ s k 1 = G₄ s k 0)
    (hi₁ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => G₁ s k l)
    (hi₂ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => G₂ s k l)
    (hi₃ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => G₃ s k l)
    (hi₄ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => G₄ s k l)
    (hclose : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, G₄ s k 1 = G₁ s (τ k) 0) :
    IsClosedStrandBraidIsotopy (fun s => quarterPath (G₁ s) (G₂ s) (G₃ s) (G₄ s)) 0 1 τ := by
  refine IsClosedStrandBraidIsotopy.of_continuous zero_lt_one (fun k => ?_) ?_ ?_
  · have c₁ : Continuous fun p : ℝ × ℝ => G₁ p.1 k (4 * p.2) :=
      (hc₁ k).comp (f := fun p : ℝ × ℝ => (p.1, 4 * p.2)) (by fun_prop)
    have c₂ : Continuous fun p : ℝ × ℝ => G₂ p.1 k (4 * p.2 - 1) :=
      (hc₂ k).comp (f := fun p : ℝ × ℝ => (p.1, 4 * p.2 - 1)) (by fun_prop)
    have c₃ : Continuous fun p : ℝ × ℝ => G₃ p.1 k (4 * p.2 - 2) :=
      (hc₃ k).comp (f := fun p : ℝ × ℝ => (p.1, 4 * p.2 - 2)) (by fun_prop)
    have c₄ : Continuous fun p : ℝ × ℝ => G₄ p.1 k (4 * p.2 - 3) :=
      (hc₄ k).comp (f := fun p : ℝ × ℝ => (p.1, 4 * p.2 - 3)) (by fun_prop)
    have hin₃ : Continuous fun p : ℝ × ℝ =>
        if p.2 ≤ 3 / 4 then G₃ p.1 k (4 * p.2 - 2) else G₄ p.1 k (4 * p.2 - 3) := by
      refine Continuous.if_le c₃ c₄ continuous_snd continuous_const fun p hp => ?_
      rw [hp]
      norm_num
      exact h₃₄ p.1 k
    have hin₂ : Continuous fun p : ℝ × ℝ =>
        if p.2 ≤ 1 / 2 then G₂ p.1 k (4 * p.2 - 1) else
          if p.2 ≤ 3 / 4 then G₃ p.1 k (4 * p.2 - 2) else G₄ p.1 k (4 * p.2 - 3) := by
      refine Continuous.if_le c₂ hin₃ continuous_snd continuous_const fun p hp => ?_
      rw [hp, if_pos (by norm_num)]
      norm_num
      exact h₂₃ p.1 k
    refine Continuous.if_le c₁ hin₂ continuous_snd continuous_const fun p hp => ?_
    rw [hp, if_pos (by norm_num)]
    norm_num
    exact h₁₂ p.1 k
  · intro s hs t ht
    by_cases h1 : t ≤ 1 / 4
    · simp_rw [quarterPath_of_le_quarter _ _ _ _ _ h1]
      exact hi₁ s hs _ ⟨by linarith [ht.1], by linarith⟩
    by_cases h2 : t ≤ 1 / 2
    · simp_rw [quarterPath_of_mem_second _ _ _ _ _ (not_le.mp h1) h2]
      exact hi₂ s hs _ ⟨by linarith [not_le.mp h1], by linarith⟩
    by_cases h3 : t ≤ 3 / 4
    · simp_rw [quarterPath_of_mem_third _ _ _ _ _ (not_le.mp h2) h3]
      exact hi₃ s hs _ ⟨by linarith [not_le.mp h2], by linarith⟩
    · simp_rw [quarterPath_of_gt _ _ _ _ _ (not_le.mp h3)]
      exact hi₄ s hs _ ⟨by linarith [not_le.mp h3], by linarith [ht.2]⟩
  · intro s hs k
    rw [quarterPath_of_gt _ _ _ _ _ (by norm_num : (3 : ℝ) / 4 < 1),
      quarterPath_of_le_quarter _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
    exact hclose s hs k

/-- Four strand families matching at the seams give a closed braid over `[0, 1]`. -/
theorem quarterPath_isClosedStrandBraid {S : ℕ} {τ : Equiv.Perm (Fin S)}
    (F₁ F₂ F₃ F₄ : Fin S → ℝ → ℂ)
    (hc₁ : ∀ k, Continuous (F₁ k)) (hc₂ : ∀ k, Continuous (F₂ k))
    (hc₃ : ∀ k, Continuous (F₃ k)) (hc₄ : ∀ k, Continuous (F₄ k))
    (h₁₂ : ∀ k, F₁ k 1 = F₂ k 0) (h₂₃ : ∀ k, F₂ k 1 = F₃ k 0) (h₃₄ : ∀ k, F₃ k 1 = F₄ k 0)
    (hi₁ : ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => F₁ k l)
    (hi₂ : ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => F₂ k l)
    (hi₃ : ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => F₃ k l)
    (hi₄ : ∀ l ∈ Icc (0 : ℝ) 1, Function.Injective fun k => F₄ k l)
    (hclose : ∀ k, F₄ k 1 = F₁ (τ k) 0) :
    IsClosedStrandBraid (quarterPath F₁ F₂ F₃ F₄) 0 1 τ :=
  (quarterFamily_isotopy (τ := τ) (fun _ => F₁) (fun _ => F₂) (fun _ => F₃) (fun _ => F₄)
    (fun k => (hc₁ k).comp continuous_snd) (fun k => (hc₂ k).comp continuous_snd)
    (fun k => (hc₃ k).comp continuous_snd) (fun k => (hc₄ k).comp continuous_snd)
    (fun _ => h₁₂) (fun _ => h₂₃) (fun _ => h₃₄) (fun _ _ => hi₁) (fun _ _ => hi₂)
    (fun _ _ => hi₃) (fun _ _ => hi₄) (fun _ _ => hclose)).slice
    (left_mem_Icc.mpr zero_le_one)

/-! ### The configurations and strand families of the construction -/

/-- The real configuration `k ↦ k`. -/
def rankConfig (S : ℕ) (k : Fin S) : ℂ := (k.val : ℂ)

/-- The straight segment from the real configuration (`s = 0`) to the semicircle
configuration of the cyclic shift (`s = 1`). -/
def semicircleSegment (S : ℕ) (s : ℝ) (k : Fin S) : ℂ :=
  (1 - s) * (k.val : ℂ) + s * cyclicShiftPath S k 0

/-- The canonical closed braid of `W`, parametrized by `[0, 1]`. -/
def wordStrands {S : ℕ} (W : PositiveAdjacentWord S) (k : Fin S) (l : ℝ) : ℂ :=
  positiveGridWord W k (l * ((W.length : ℝ) + 1))

/-- The convex combination of the arguments of the rigid turn of the semicircle
configuration and of the cyclic shift. -/
def angleFamily (S : ℕ) (s : ℝ) (k : Fin S) (l : ℝ) : ℂ :=
  Complex.exp ((((1 - s) * (cyclicShiftAngle S (-(k.val : ℝ)) + 2 * π * l) +
    s * cyclicShiftAngle S ((S : ℝ) * l - k.val) : ℝ) : ℂ) * Complex.I)

theorem wordStrands_continuous {S : ℕ} (W : PositiveAdjacentWord S) (k : Fin S) :
    Continuous (wordStrands W k) :=
  (positiveGridWord_contDiff W k).continuous.comp (by fun_prop)

theorem wordStrands_zero {S : ℕ} (W : PositiveAdjacentWord S) (k : Fin S) :
    wordStrands W k 0 = rankConfig S k := by
  simp [wordStrands, rankConfig, positiveGridWord_of_nonpos W k le_rfl]

theorem wordStrands_one {S : ℕ} (W : PositiveAdjacentWord S) (k : Fin S) :
    wordStrands W k 1 = rankConfig S ((PositiveAdjacentWord.permutation W)⁻¹ k) := by
  rw [wordStrands, one_mul, positiveGridWord_of_length_le W k (by linarith)]
  rfl

theorem wordStrands_injective {S : ℕ} (W : PositiveAdjacentWord S) (l : ℝ) :
    Function.Injective fun k => wordStrands W k l :=
  positiveGridWord_injective W _

theorem positiveWordModel_zero_one {S : ℕ} (W : PositiveAdjacentWord S) (k : Fin S) (t : ℝ) :
    positiveWordModel W 0 1 k t = wordStrands W k t := by
  simp [positiveWordModel, positiveWordModelTime, wordStrands]

theorem semicircleSegment_continuous (S : ℕ) (k : Fin S) :
    Continuous fun s => semicircleSegment S s k := by
  unfold semicircleSegment
  fun_prop

theorem semicircleSegment_zero (S : ℕ) (k : Fin S) :
    semicircleSegment S 0 k = rankConfig S k := by
  simp [semicircleSegment, rankConfig]

theorem semicircleSegment_one (S : ℕ) (k : Fin S) :
    semicircleSegment S 1 k = cyclicShiftPath S k 0 := by
  simp [semicircleSegment]

/-- The real parts of the semicircle configuration increase with the label. -/
theorem cyclicShiftPath_zero_re_strictMono {S : ℕ} (hS : 2 ≤ S) :
    StrictMono fun k : Fin S => (cyclicShiftPath S k 0).re := by
  intro k l hkl
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hk : (k.val : ℝ) + 1 ≤ S := by exact_mod_cast k.isLt
  have hl : (l.val : ℝ) + 1 ≤ S := by exact_mod_cast l.isLt
  have hkl' : (k.val : ℝ) < l.val := by exact_mod_cast hkl
  simp only [cyclicShiftPath, zero_sub, exp_ofReal_mul_I_re']
  have hmk := cyclicShiftAngle_mem_of_nonpos hS
    (p := -(k.val : ℝ)) ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) k.val]⟩
  have hml := cyclicShiftAngle_mem_of_nonpos hS
    (p := -(l.val : ℝ)) ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) l.val]⟩
  exact Real.cos_lt_cos_of_nonneg_of_le_pi hml.1 hmk.2
    (cyclicShiftAngle_strictMono hS (by linarith))

/-- The real parts of every configuration on the segment increase with the label. -/
theorem semicircleSegment_re_strictMono {S : ℕ} (hS : 2 ≤ S) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : StrictMono fun k : Fin S => (semicircleSegment S s k).re := by
  intro k l hkl
  have hq := cyclicShiftPath_zero_re_strictMono hS hkl
  have hkl' : (k.val : ℝ) < l.val := by exact_mod_cast hkl
  simp only [semicircleSegment, Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.one_re, Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero, zero_mul]
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1]
    simpa using hq
  · nlinarith [hs.1]

theorem semicircleSegment_injective {S : ℕ} (hS : 2 ≤ S) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Function.Injective fun k : Fin S => semicircleSegment S s k := by
  intro k l h
  exact (semicircleSegment_re_strictMono hS hs).injective (congrArg Complex.re h)

theorem angleFamily_continuous (S : ℕ) (k : Fin S) :
    Continuous fun p : ℝ × ℝ => angleFamily S p.1 k p.2 := by
  unfold angleFamily
  have := cyclicShiftAngle_continuous S
  fun_prop

theorem angleFamily_zero_left (s : ℝ) (k : Fin S) :
    angleFamily S s k 0 = cyclicShiftPath S k 0 := by
  simp [angleFamily, cyclicShiftPath]
  ring_nf

theorem angleFamily_one_left (hS : 2 ≤ S) (s : ℝ) (k : Fin S) :
    angleFamily S s k 1 = cyclicShiftPath S k 0 := by
  have hk : (k.val : ℝ) + 1 ≤ S := by exact_mod_cast k.isLt
  have hper := cyclicShiftAngle_add hS (p := -(k.val : ℝ))
    ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) k.val]⟩
  rw [show -(k.val : ℝ) + S = (S : ℝ) * 1 - k.val by ring] at hper
  simp only [angleFamily, cyclicShiftPath, zero_sub, hper]
  rw [show ((((1 - s) * (cyclicShiftAngle S (-(k.val : ℝ)) + 2 * π * 1) +
      s * (cyclicShiftAngle S (-(k.val : ℝ)) + 2 * π) : ℝ) : ℂ) * Complex.I) =
      ((cyclicShiftAngle S (-(k.val : ℝ)) : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by
    push_cast
    ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem angleFamily_zero (S : ℕ) (k : Fin S) (l : ℝ) :
    angleFamily S 0 k l = Complex.exp (2 * π * l * Complex.I) * cyclicShiftPath S k 0 := by
  simp only [angleFamily, cyclicShiftPath, zero_sub, sub_zero, one_mul, zero_mul, add_zero]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angleFamily_one (S : ℕ) (k : Fin S) (l : ℝ) :
    angleFamily S 1 k l = cyclicShiftPath S k ((S : ℝ) * l) := by
  simp [angleFamily, cyclicShiftPath]

theorem exp_mul_I_ne_of_sub_mem {a b : ℝ} (h0 : 0 < a - b) (h2 : a - b < 2 * π) :
    Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I) := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat] at him
  have heq : a - b = 2 * π * n := by linarith
  have hpos : (0 : ℝ) < n := by
    by_contra hle
    nlinarith [pi_pos]
  have hlt : (n : ℝ) < 1 := by
    by_contra hle
    nlinarith [pi_pos]
  have h1 : (0 : ℤ) < n := by exact_mod_cast hpos
  have h2 : n < (1 : ℤ) := by exact_mod_cast hlt
  omega

theorem angleFamily_injective (hS : 2 ≤ S) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (l : ℝ) : Function.Injective fun k : Fin S => angleFamily S s k l := by
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hmain : ∀ k k' : Fin S, k.val < k'.val → angleFamily S s k l ≠ angleFamily S s k' l := by
    intro k k' hkk'
    have hkr : (k.val : ℝ) < k'.val := by exact_mod_cast hkk'
    have hk' : (k'.val : ℝ) + 1 ≤ S := by exact_mod_cast k'.isLt
    have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    have hd1 := cyclicShiftAngle_strictMono hS (show -(k'.val : ℝ) < -(k.val : ℝ) by linarith)
    have hd2 := cyclicShiftAngle_sub_lt hS (x := -(k'.val : ℝ)) (y := -(k.val : ℝ))
      (by linarith)
    have hd3 := cyclicShiftAngle_strictMono hS
      (show (S : ℝ) * l - k'.val < (S : ℝ) * l - k.val by linarith)
    have hd4 := cyclicShiftAngle_sub_lt hS (x := (S : ℝ) * l - k'.val)
      (y := (S : ℝ) * l - k.val) (by linarith)
    set d₁ := cyclicShiftAngle S (-(k.val : ℝ)) - cyclicShiftAngle S (-(k'.val : ℝ))
    set d₂ := cyclicShiftAngle S ((S : ℝ) * l - k.val) -
      cyclicShiftAngle S ((S : ℝ) * l - k'.val)
    have he : (1 - s) * (cyclicShiftAngle S (-(k.val : ℝ)) + 2 * π * l) +
        s * cyclicShiftAngle S ((S : ℝ) * l - k.val) -
        ((1 - s) * (cyclicShiftAngle S (-(k'.val : ℝ)) + 2 * π * l) +
          s * cyclicShiftAngle S ((S : ℝ) * l - k'.val)) = (1 - s) * d₁ + s * d₂ := by
      simp only [d₁, d₂]
      ring
    have hd₁ : 0 < d₁ := by simp only [d₁]; linarith
    have hd₂ : 0 < d₂ := by simp only [d₂]; linarith
    have hm₁ := mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (min_le_left d₁ d₂))
    have hm₂ := mul_nonneg hs.1 (sub_nonneg.2 (min_le_right d₁ d₂))
    have hM₁ := mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 (le_max_left d₁ d₂))
    have hM₂ := mul_nonneg hs.1 (sub_nonneg.2 (le_max_right d₁ d₂))
    have hmin : 0 < min d₁ d₂ := lt_min hd₁ hd₂
    have hmax : max d₁ d₂ < 2 * π := max_lt hd2 hd4
    apply exp_mul_I_ne_of_sub_mem
    · rw [he]
      nlinarith
    · rw [he]
      nlinarith
  intro k k' h
  by_contra hne
  rcases lt_or_gt_of_ne (fun he : k.val = k'.val => hne (Fin.ext he)) with hlt | hlt
  · exact hmain k k' hlt h
  · exact hmain k' k hlt h.symm

/-! ### The five isotopies -/

section FullTwist

variable {S : ℕ}

theorem fullTwist_append_permutation (W : PositiveAdjacentWord S) :
    PositiveAdjacentWord.permutation (fullTwistWord S ++ W) =
      PositiveAdjacentWord.permutation W := by
  rw [PositiveAdjacentWord.permutation_append_eq_mul]
  have h : PositiveAdjacentWord.permutation (fullTwistWord S) = 1 := fullTwistWord_permutation S
  rw [h, one_mul]

theorem fullTwistWord_length_real (S : ℕ) (hS : 1 ≤ S) :
    ((fullTwistWord S).length : ℝ) = (S : ℝ) * ((S : ℝ) - 1) := by
  rw [fullTwistWord, torusWord_length, Nat.cast_mul, Nat.cast_sub hS]
  simp

theorem rankConfig_injective (S : ℕ) : Function.Injective (rankConfig S) := by
  intro k l h
  unfold rankConfig at h
  exact Fin.ext (by exact_mod_cast h)

theorem rankConfig_re_strictMono (S : ℕ) : StrictMono fun k : Fin S => (rankConfig S k).re := by
  intro k l h
  simpa [rankConfig] using h

theorem cyclicShiftPath_period (hS : 2 ≤ S) (k : Fin S) :
    cyclicShiftPath S k S = cyclicShiftPath S k 0 := by
  have hk : (k.val : ℝ) + 1 ≤ S := by exact_mod_cast k.isLt
  have hper := cyclicShiftAngle_add hS (p := -(k.val : ℝ))
    ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) k.val]⟩
  rw [show -(k.val : ℝ) + S = (S : ℝ) - k.val by ring] at hper
  simp only [cyclicShiftPath, zero_sub, hper]
  push_cast
  rw [add_mul, Complex.exp_add, show (2 * (π : ℂ)) * Complex.I = 2 * π * Complex.I by ring,
    Complex.exp_two_pi_mul_I, mul_one]

/-- Two strand families whose real parts are both strictly increasing in the label are
separated in the real coordinate. -/
theorem sep_of_strictMono {f g : Fin S → ℂ} (hf : StrictMono fun k => (f k).re)
    (hg : StrictMono fun k => (g k).re) {k l : Fin S} (hkl : k ≠ l) :
    0 < (f k - f l).re * (g k - g l).re ∨ 0 < (f k - f l).im * (g k - g l).im := by
  left
  rw [Complex.sub_re, Complex.sub_re]
  rcases lt_or_gt_of_ne hkl with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hf h)) (sub_neg.mpr (hg h))
  · exact mul_pos (sub_pos.mpr (hf h)) (sub_pos.mpr (hg h))

theorem sep_self {a : ℂ} (ha : a ≠ 0) : 0 < a.re * a.re ∨ 0 < a.im * a.im := by
  by_cases h : a.re = 0
  · right
    have him : a.im ≠ 0 := fun hi => ha (Complex.ext h hi)
    exact mul_self_pos.mpr him
  · left
    exact mul_self_pos.mpr h

/-- The turned word path, with the turn performed first. -/
def turnFirstPath (W : PositiveAdjacentWord S) : Fin S → ℝ → ℂ :=
  quarterPath (fun k l => Complex.exp (2 * π * (l : ℂ) * Complex.I) * rankConfig S k)
    (fun k _ => rankConfig S k) (wordStrands W)
    (fun k _ => rankConfig S ((PositiveAdjacentWord.permutation W)⁻¹ k))

/-- Step 1: the turn and the word are performed one after the other. -/
theorem twisted_isotopic_turnFirst (W : PositiveAdjacentWord S) :
    ClosedStrandBraidIsotopic
      (fun k t => Complex.exp (2 * π * (t : ℂ) * Complex.I) * wordStrands W k t)
      (turnFirstPath W) 0 1 (PositiveAdjacentWord.permutation W)⁻¹ := by
  let α : ℝ → ℝ → ℝ := fun s t => (1 - s) * t + s * min (4 * t) 1
  let β : ℝ → ℝ → ℝ := fun s t => (1 - s) * t + s * unitClamp (4 * t - 2)
  have hβc : Continuous fun p : ℝ × ℝ => β p.1 p.2 := by
    have := unitClamp_continuous
    simp only [β]
    fun_prop
  refine ⟨fun s k t => Complex.exp (2 * π * ((α s t : ℝ) : ℂ) * Complex.I) *
    wordStrands W k (β s t), IsClosedStrandBraidIsotopy.of_continuous zero_lt_one
      (fun k => ?_) (fun s _ t _ k l hkl => ?_) (fun s _ k => ?_), fun k t _ => ?_,
      fun k t ht => ?_⟩
  · have hα : Continuous fun p : ℝ × ℝ => α p.1 p.2 := by simp only [α]; fun_prop
    exact (Complex.continuous_exp.comp (by fun_prop)).mul
      ((wordStrands_continuous W k).comp hβc)
  · exact wordStrands_injective W _ (mul_left_cancel₀ (Complex.exp_ne_zero _) hkl)
  · have h1 : α s 1 = 1 := by simp only [α]; norm_num
    have h2 : β s 1 = 1 := by
      simp only [β]
      rw [unitClamp_of_one_le (by norm_num)]
      ring
    have h3 : α s 0 = 0 := by simp only [α]; norm_num
    have h4 : β s 0 = 0 := by
      simp only [β]
      rw [unitClamp_of_nonpos (by norm_num)]
      ring
    rw [h1, h2, h3, h4, wordStrands_one, wordStrands_zero]
    simp
  · simp [α, β]
  · -- The end of the deformation is the concatenation.
    simp only [α, β, sub_self, zero_mul, one_mul, zero_add]
    by_cases h1 : t ≤ 1 / 4
    · rw [turnFirstPath, quarterPath_of_le_quarter _ _ _ _ _ h1, min_eq_left (by linarith),
        unitClamp_of_nonpos (by linarith), wordStrands_zero]
    by_cases h2 : t ≤ 1 / 2
    · rw [turnFirstPath, quarterPath_of_mem_second _ _ _ _ _ (not_le.mp h1) h2,
        min_eq_right (by linarith), unitClamp_of_nonpos (by linarith), wordStrands_zero]
      simp
    by_cases h3 : t ≤ 3 / 4
    · rw [turnFirstPath, quarterPath_of_mem_third _ _ _ _ _ (not_le.mp h2) h3,
        min_eq_right (by linarith), unitClamp_of_mem ⟨by linarith, by linarith⟩]
      simp
    · rw [turnFirstPath, quarterPath_of_gt _ _ _ _ _ (not_le.mp h3),
        min_eq_right (by linarith), unitClamp_of_one_le (by linarith [ht.2]), wordStrands_one]
      simp

/-- The semicircle-based turn followed by the transport segments and the word. -/
def semicircleTurnPath (W : PositiveAdjacentWord S) : Fin S → ℝ → ℂ :=
  quarterPath (fun k l => Complex.exp (2 * π * (l : ℂ) * Complex.I) * cyclicShiftPath S k 0)
    (fun k l => semicircleSegment S (1 - l) k) (wordStrands W)
    (fun k l => semicircleSegment S l ((PositiveAdjacentWord.permutation W)⁻¹ k))

/-- Step 2: transport of the base configuration of the turn. -/
theorem turnFirst_isotopic_semicircle (hS : 2 ≤ S) (W : PositiveAdjacentWord S) :
    ClosedStrandBraidIsotopic (turnFirstPath W) (semicircleTurnPath W) 0 1
      (PositiveAdjacentWord.permutation W)⁻¹ := by
  set τ' := (PositiveAdjacentWord.permutation W)⁻¹
  have hiso := quarterFamily_isotopy (τ := τ')
    (fun s k l => Complex.exp (2 * π * (l : ℂ) * Complex.I) * semicircleSegment S s k)
    (fun s k l => semicircleSegment S ((1 - l) * s) k)
    (fun _ => wordStrands W)
    (fun s k l => semicircleSegment S (l * s) (τ' k))
    (fun k => by unfold semicircleSegment; have := cyclicShiftPath_continuous S k; fun_prop)
    (fun k => (semicircleSegment_continuous S k).comp (by fun_prop))
    (fun k => (wordStrands_continuous W k).comp continuous_snd)
    (fun k => (semicircleSegment_continuous S (τ' k)).comp (by fun_prop))
    (fun s k => by simp)
    (fun s k => by simp [wordStrands_zero, semicircleSegment_zero])
    (fun s k => by simp [wordStrands_one, semicircleSegment_zero, τ'])
    (fun s hs l _ k k' h => semicircleSegment_injective hS hs
      (mul_left_cancel₀ (Complex.exp_ne_zero _) h))
    (fun s hs l hl => semicircleSegment_injective hS
      ⟨mul_nonneg (by linarith [hl.2]) hs.1, by nlinarith [hl.1, hl.2, hs.1, hs.2]⟩)
    (fun _ _ l _ => wordStrands_injective W l)
    (fun s hs l hl => (semicircleSegment_injective hS
      ⟨mul_nonneg hl.1 hs.1, by nlinarith [hl.1, hl.2, hs.1, hs.2]⟩).comp τ'.injective)
    (fun s _ k => by simp)
  refine ⟨_, hiso, fun k t _ => ?_, fun k t _ => ?_⟩
  · simp only [turnFirstPath, mul_zero, semicircleSegment_zero]
    rfl
  · simp only [semicircleTurnPath, mul_one, semicircleSegment_one]
    rfl

/-- The cyclic shift followed by the transport segments and the word. -/
def cyclicShiftTurnPath (W : PositiveAdjacentWord S) : Fin S → ℝ → ℂ :=
  quarterPath (fun k l => cyclicShiftPath S k ((S : ℝ) * l))
    (fun k l => semicircleSegment S (1 - l) k) (wordStrands W)
    (fun k l => semicircleSegment S l ((PositiveAdjacentWord.permutation W)⁻¹ k))

/-- Step 3: the rigid turn of the semicircle configuration is replaced by the cyclic
shift. -/
theorem semicircle_isotopic_cyclicShift (hS : 2 ≤ S) (W : PositiveAdjacentWord S) :
    ClosedStrandBraidIsotopic (semicircleTurnPath W) (cyclicShiftTurnPath W) 0 1
      (PositiveAdjacentWord.permutation W)⁻¹ := by
  set τ' := (PositiveAdjacentWord.permutation W)⁻¹
  have hiso := quarterFamily_isotopy (τ := τ')
    (fun s k l => angleFamily S s k l)
    (fun _ k l => semicircleSegment S (1 - l) k)
    (fun _ => wordStrands W)
    (fun _ k l => semicircleSegment S l (τ' k))
    (fun k => angleFamily_continuous S k)
    (fun k => (semicircleSegment_continuous S k).comp (by fun_prop))
    (fun k => (wordStrands_continuous W k).comp continuous_snd)
    (fun k => (semicircleSegment_continuous S (τ' k)).comp continuous_snd)
    (fun s k => by rw [angleFamily_one_left hS, sub_zero, semicircleSegment_one])
    (fun s k => by simp [wordStrands_zero, semicircleSegment_zero])
    (fun s k => by simp [wordStrands_one, semicircleSegment_zero, τ'])
    (fun s hs l _ => angleFamily_injective hS hs l)
    (fun _ _ l hl => semicircleSegment_injective hS ⟨by linarith [hl.2], by linarith [hl.1]⟩)
    (fun _ _ l _ => wordStrands_injective W l)
    (fun _ _ l hl => (semicircleSegment_injective hS hl).comp τ'.injective)
    (fun s _ k => by rw [semicircleSegment_one, angleFamily_zero_left])
  refine ⟨_, hiso, fun k t _ => ?_, fun k t _ => ?_⟩
  · simp only [semicircleTurnPath, angleFamily_zero]
    rfl
  · simp only [cyclicShiftTurnPath, angleFamily_one]
    rfl

/-- The canonical full twist followed by the word, with constant connecting pieces. -/
def fullTwistTurnPath (W : PositiveAdjacentWord S) : Fin S → ℝ → ℂ :=
  quarterPath (fun k l => positiveGridWord (fullTwistWord S) k ((S : ℝ) * ((S : ℝ) - 1) * l))
    (fun k _ => rankConfig S k) (wordStrands W)
    (fun k _ => rankConfig S ((PositiveAdjacentWord.permutation W)⁻¹ k))

theorem fullTwistWord_end (hS : 1 ≤ S) (k : Fin S) :
    positiveGridWord (fullTwistWord S) k ((S : ℝ) * ((S : ℝ) - 1)) = rankConfig S k := by
  rw [positiveGridWord_of_length_le _ _ (by rw [fullTwistWord_length_real S hS])]
  have h : PositiveAdjacentWord.permutation (fullTwistWord S) = 1 := fullTwistWord_permutation S
  rw [h]
  rfl

/-- Step 4: straight-line interpolation from the cyclic shift to the canonical full
twist. -/
theorem cyclicShift_isotopic_fullTwist (hS : 2 ≤ S) (W : PositiveAdjacentWord S) :
    ClosedStrandBraidIsotopic (cyclicShiftTurnPath W) (fullTwistTurnPath W) 0 1
      (PositiveAdjacentWord.permutation W)⁻¹ := by
  set τ' := (PositiveAdjacentWord.permutation W)⁻¹
  have hS1 : 1 ≤ S := by omega
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hS1r : (0 : ℝ) < (S : ℝ) - 1 := by linarith
  have h₂ : IsClosedStrandBraid (cyclicShiftTurnPath W) 0 1 τ' :=
    quarterPath_isClosedStrandBraid _ _ _ _
      (fun k => (cyclicShiftPath_continuous S k).comp (by fun_prop))
      (fun k => (semicircleSegment_continuous S k).comp (by fun_prop))
      (fun k => wordStrands_continuous W k)
      (fun k => (semicircleSegment_continuous S (τ' k)))
      (fun k => by rw [sub_zero, semicircleSegment_one, mul_one, cyclicShiftPath_period hS])
      (fun k => by simp [wordStrands_zero, semicircleSegment_zero])
      (fun k => by simp [wordStrands_one, semicircleSegment_zero])
      (fun l _ => by
        have h := angleFamily_injective hS (s := 1) ⟨zero_le_one, le_rfl⟩ l
        simpa only [angleFamily_one] using h)
      (fun l hl => semicircleSegment_injective hS ⟨by linarith [hl.2], by linarith [hl.1]⟩)
      (fun l _ => wordStrands_injective W l)
      (fun l hl => (semicircleSegment_injective hS hl).comp τ'.injective)
      (fun k => by
        rw [semicircleSegment_one, mul_zero])
  have h₃ : IsClosedStrandBraid (fullTwistTurnPath W) 0 1 τ' :=
    quarterPath_isClosedStrandBraid _ _ _ _
      (fun k => (positiveGridWord_contDiff _ k).continuous.comp (by fun_prop))
      (fun k => continuous_const) (fun k => wordStrands_continuous W k)
      (fun k => continuous_const)
      (fun k => by rw [mul_one, fullTwistWord_end hS1])
      (fun k => (wordStrands_zero W k).symm)
      (fun k => by rw [wordStrands_one])
      (fun l _ => positiveGridWord_injective _ _)
      (fun l _ => rankConfig_injective S)
      (fun l _ => wordStrands_injective W l)
      (fun l _ => (rankConfig_injective S).comp τ'.injective)
      (fun k => by
        rw [mul_zero, positiveGridWord_of_nonpos _ _ le_rfl]
        rfl)
  apply ClosedStrandBraidIsotopic.of_separation h₂ h₃
  intro t ht k l hkl
  by_cases h1 : t ≤ 1 / 4
  · simp only [cyclicShiftTurnPath, fullTwistTurnPath, quarterPath_of_le_quarter _ _ _ _ _ h1]
    have hτ : (S : ℝ) * ((S : ℝ) - 1) * (4 * t) ∈ Icc (0 : ℝ) ((S : ℝ) * ((S : ℝ) - 1)) := by
      constructor
      · have : 0 ≤ (S : ℝ) * ((S : ℝ) - 1) := by positivity
        nlinarith [ht.1]
      · have : 0 ≤ (S : ℝ) * ((S : ℝ) - 1) := by positivity
        nlinarith [ht.1]
    have h := cyclicShift_separation hS hτ hkl
    have heq : (S : ℝ) * ((S : ℝ) - 1) * (4 * t) / ((S : ℝ) - 1) = (S : ℝ) * (4 * t) := by
      field_simp
    rw [heq] at h
    exact h
  by_cases h2 : t ≤ 1 / 2
  · simp only [cyclicShiftTurnPath, fullTwistTurnPath,
      quarterPath_of_mem_second _ _ _ _ _ (not_le.mp h1) h2]
    exact sep_of_strictMono (semicircleSegment_re_strictMono hS
      ⟨by linarith, by linarith [not_le.mp h1]⟩) (rankConfig_re_strictMono S) hkl
  by_cases h3 : t ≤ 3 / 4
  · simp only [cyclicShiftTurnPath, fullTwistTurnPath,
      quarterPath_of_mem_third _ _ _ _ _ (not_le.mp h2) h3]
    exact sep_self (sub_ne_zero.mpr fun he => hkl (wordStrands_injective W _ he))
  · simp only [cyclicShiftTurnPath, fullTwistTurnPath, quarterPath_of_gt _ _ _ _ _ (not_le.mp h3)]
    exact sep_of_strictMono
      (semicircleSegment_re_strictMono hS ⟨by linarith [not_le.mp h3], by linarith [ht.2]⟩)
      (rankConfig_re_strictMono S) (τ'.injective.ne hkl)

/-- The monotone change of parameter of step 5. -/
def fullTwistTime (S : ℕ) (W : PositiveAdjacentWord S) (t : ℝ) : ℝ :=
  (S : ℝ) * ((S : ℝ) - 1) * min (4 * t) 1 + ((W.length : ℝ) + 1) * unitClamp (4 * t - 2)

/-- Step 5: the canonical full twist followed by the word is the canonical closed braid of
the concatenated word. -/
theorem fullTwistTurn_isotopic_model (hS : 2 ≤ S) (W : PositiveAdjacentWord S) :
    ClosedStrandBraidIsotopic (fullTwistTurnPath W) (positiveWordModel (fullTwistWord S ++ W) 0 1)
      0 1 (PositiveAdjacentWord.permutation W)⁻¹ := by
  have hS1 : 1 ≤ S := by omega
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hD : ((fullTwistWord S).length : ℝ) = (S : ℝ) * ((S : ℝ) - 1) :=
    fullTwistWord_length_real S hS1
  have hDpos : 0 ≤ (S : ℝ) * ((S : ℝ) - 1) := mul_nonneg (by positivity) (by linarith)
  have hL : (0 : ℝ) ≤ W.length := Nat.cast_nonneg _
  have hlen : (((fullTwistWord S ++ W).length : ℕ) : ℝ) + 1 =
      (S : ℝ) * ((S : ℝ) - 1) + ((W.length : ℝ) + 1) := by
    rw [List.length_append, Nat.cast_add, hD]
    ring
  have hcl := positiveGridWord_isClosedStrandBraid (fullTwistWord S ++ W)
  rw [fullTwist_append_permutation] at hcl
  have hψc : Continuous (fullTwistTime S W) := by
    unfold fullTwistTime
    have := unitClamp_continuous
    fun_prop
  have hψm : MapsTo (fullTwistTime S W) (Icc 0 1)
      (Icc 0 ((((fullTwistWord S ++ W).length : ℕ) : ℝ) + 1)) := by
    intro t ht
    rw [hlen]
    have hm0 : 0 ≤ min (4 * t) 1 := le_min (by linarith [ht.1]) zero_le_one
    have hm1 : min (4 * t) 1 ≤ 1 := min_le_right _ _
    have hc := unitClamp_mem (4 * t - 2)
    unfold fullTwistTime
    constructor
    · have := mul_nonneg hDpos hm0
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ (W.length : ℝ) + 1) hc.1
      linarith
    · have := mul_le_mul_of_nonneg_left hm1 hDpos
      have := mul_le_mul_of_nonneg_left hc.2 (by linarith : (0 : ℝ) ≤ (W.length : ℝ) + 1)
      linarith
  have hψ0 : fullTwistTime S W 0 = 0 := by
    simp [fullTwistTime, unitClamp_of_nonpos (show (-2 : ℝ) ≤ 0 by norm_num)]
  have hψ1 : fullTwistTime S W 1 = (((fullTwistWord S ++ W).length : ℕ) : ℝ) + 1 := by
    rw [hlen, fullTwistTime, min_eq_right (by norm_num), unitClamp_of_one_le (by norm_num)]
    ring
  have hrep := ClosedStrandBraidIsotopic.of_reparam hcl zero_lt_one hψc.continuousOn
    (positiveWordModelTime_continuous _ 0 1).continuousOn hψm
    (positiveWordModelTime_mapsTo _ zero_lt_one) hψ0 hψ1 (positiveWordModelTime_left _ 0 1)
    (positiveWordModelTime_right _ zero_lt_one)
  refine hrep.congr (fun k t ht => ?_) (fun k t _ => rfl)
  -- The concatenated path along the change of parameter.
  have hperm1 : PositiveAdjacentWord.permutation (fullTwistWord S) = 1 :=
    fullTwistWord_permutation S
  by_cases h1 : t ≤ 1 / 4
  · rw [fullTwistTurnPath, quarterPath_of_le_quarter _ _ _ _ _ h1, fullTwistTime,
      min_eq_left (by linarith), unitClamp_of_nonpos (by linarith), mul_zero, add_zero,
      positiveGridWord_append_of_le _ _ _ (by rw [hD]; nlinarith [ht.1])]
  by_cases h2 : t ≤ 1 / 2
  · rw [fullTwistTurnPath, quarterPath_of_mem_second _ _ _ _ _ (not_le.mp h1) h2, fullTwistTime,
      min_eq_right (by linarith), unitClamp_of_nonpos (by linarith), mul_zero, add_zero,
      mul_one, positiveGridWord_append_of_le _ _ _ (by rw [hD]),
      fullTwistWord_end hS1]
  by_cases h3 : t ≤ 3 / 4
  · rw [fullTwistTurnPath, quarterPath_of_mem_third _ _ _ _ _ (not_le.mp h2) h3, fullTwistTime,
      min_eq_right (by linarith), unitClamp_of_mem ⟨by linarith, by linarith⟩, mul_one,
      positiveGridWord_append_of_ge _ _ _ (by rw [hD]; nlinarith), hperm1, hD,
      wordStrands]
    congr 1
    ring
  · rw [fullTwistTurnPath, quarterPath_of_gt _ _ _ _ _ (not_le.mp h3), fullTwistTime,
      min_eq_right (by linarith), unitClamp_of_one_le (by linarith [ht.2]), mul_one, mul_one,
      positiveGridWord_append_of_ge _ _ _ (by rw [hD]; nlinarith), hperm1, hD,
      add_sub_cancel_left, positiveGridWord_of_length_le _ _ (by linarith)]
    rfl

/-- **The full twist** (Lemmas `J14:lem:rotation` and `J14:lem:product`). Turning the
canonical closed braid of a positive word `W` once counterclockwise gives a closed braid
isotopic through closed braids to the canonical closed braid of `fullTwistWord S ++ W`. -/
theorem fullTwist_twisted_isotopic (W : PositiveAdjacentWord S) :
    ClosedStrandBraidIsotopic
      (fun k t => Complex.exp (2 * π * (t : ℂ) * Complex.I) * positiveWordModel W 0 1 k t)
      (positiveWordModel (fullTwistWord S ++ W) 0 1) 0 1
      (PositiveAdjacentWord.permutation W)⁻¹ := by
  rcases lt_or_ge S 2 with hS | hS
  · -- At most one strand: both braids are constant at the origin.
    have hnil : ∀ V : PositiveAdjacentWord S, V = [] := by
      intro V
      match V with
      | [] => rfl
      | a :: _ => exact absurd a.isLt (by omega)
    have hval : ∀ k : Fin S, ((k.val : ℕ) : ℂ) = 0 := by
      intro k
      have := k.isLt
      have : k.val = 0 := by omega
      simp [this]
    have hconst : ∀ (V : PositiveAdjacentWord S) (k : Fin S) (t : ℝ),
        positiveGridWord V k t = 0 := by
      intro V k t
      rw [hnil V]
      rcases le_or_gt t 0 with h | h
      · rw [positiveGridWord_of_nonpos _ _ h, hval]
      · rw [positiveGridWord_of_length_le _ _ (by simpa using h.le)]
        simp only [PositiveAdjacentWord.permutation_nil]
        exact hval _
    have hcl := positiveWordModel_isClosedStrandBraid (fullTwistWord S ++ W) zero_lt_one
    rw [fullTwist_append_permutation] at hcl
    refine (ClosedStrandBraidIsotopic.refl hcl).congr (fun k t _ => ?_) (fun k t _ => rfl)
    simp [positiveWordModel, hconst]
  · exact ((twisted_isotopic_turnFirst W).congr
      (fun k t _ => by rw [positiveWordModel_zero_one]) (fun _ _ _ => rfl)).trans
      ((turnFirst_isotopic_semicircle hS W).trans ((semicircle_isotopic_cyclicShift hS W).trans
        ((cyclicShift_isotopic_fullTwist hS W).trans (fullTwistTurn_isotopic_model hS W))))

/-- **Full-twist prefix of a turned closed braid.** If a closed braid over a base period is
represented by `W`, then its product with the base circle `θ ↦ ρ e^{iθ}` is represented by
`fullTwistWord S ++ W`. -/
theorem IsRepresentedByPositiveWord.circlePath_mul {K : Fin S → ℝ → ℂ} {b : ℝ}
    {W : PositiveAdjacentWord S} (h : IsRepresentedByPositiveWord K b (b + 2 * π) W)
    {ρ : ℝ} (hρ : 0 < ρ) :
    IsRepresentedByPositiveWord (fun k θ => circlePath ρ θ * K k θ) b (b + 2 * π)
      (fullTwistWord S ++ W) := by
  obtain ⟨σ, hσ⟩ := h
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hg0 : ∀ θ ∈ Icc b (b + 2 * π), circlePath ρ θ ≠ 0 := by
    intro θ _
    apply norm_pos_iff.mp
    rw [norm_circlePath hρ.le]
    exact hρ
  have hmul := hσ.mul_left (continuous_circlePath ρ).continuousOn hg0
    (circlePath_add_two_pi ρ b)
  let φ : ℝ → ℝ := fun θ => (θ - b) / (2 * π)
  have hφc : Continuous φ := by fun_prop
  have hφm : MapsTo φ (Icc b (b + 2 * π)) (Icc 0 1) := by
    intro θ hθ
    exact ⟨div_nonneg (by linarith [hθ.1]) h2π.le, (div_le_one h2π).mpr (by linarith [hθ.2])⟩
  have hφb : φ b = 0 := by simp [φ]
  have hφd : φ (b + 2 * π) = 1 := by simp [φ]
  have hFT := (fullTwist_twisted_isotopic W).comp_time (by linarith) hφc.continuousOn hφm hφb hφd
  have hc : ((ρ : ℂ) * Complex.exp ((b : ℂ) * Complex.I)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hρ.ne') (Complex.exp_ne_zero _)
  have hscale := ClosedStrandBraidIsotopic.const_mul hFT.left hc
  refine ⟨σ, ?_⟩
  rw [fullTwist_append_permutation]
  refine hmul.trans ((hscale.symm.congr (fun k θ hθ => ?_) (fun _ _ _ => rfl)).trans
    (hFT.congr (fun _ _ _ => rfl) (fun k θ _ => ?_)))
  · -- The turned model is a constant multiple of the transported twisted model.
    have hmodel : positiveWordModel W 0 1 k (φ θ) = positiveWordModel W b (b + 2 * π) k θ := by
      simp only [positiveWordModel, positiveWordModelTime, φ]
      congr 1
      field_simp
      ring
    rw [hmodel, circlePath]
    rw [show ((ρ : ℂ) * Complex.exp ((b : ℂ) * Complex.I)) *
        (Complex.exp (2 * π * ((φ θ : ℝ) : ℂ) * Complex.I) *
          positiveWordModel W b (b + 2 * π) k θ) =
        (ρ : ℂ) * (Complex.exp ((b : ℂ) * Complex.I) *
          Complex.exp (2 * π * ((φ θ : ℝ) : ℂ) * Complex.I)) *
          positiveWordModel W b (b + 2 * π) k θ by ring, ← Complex.exp_add]
    congr 3
    simp only [φ]
    push_cast
    field_simp
    ring
  · simp only [positiveWordModel, positiveWordModelTime, φ]
    congr 1
    field_simp
    ring

end FullTwist

end OnLeConjecture.Analytic
