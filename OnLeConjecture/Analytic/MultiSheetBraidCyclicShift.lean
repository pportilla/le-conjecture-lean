/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidEventRepresentation
public import OnLeConjecture.KnotTheory.PositiveWordNormalForms
import all OnLeConjecture.KnotTheory.PositiveWordNormalForms
import all OnLeConjecture.KnotTheory.BraidPermutationCycles

/-!
# The cyclic shift on a semicircle and the canonical path of the Coxeter word

This module supplies the explicit model used in Lemma `J14:lem:rotation` of the written
proof. For `S ≥ 2` let

`φ(p) = π + π p / (S - 1) + π (S - 2) / (S - 1) · clamp₀₁(p)`.

The function `φ` is strictly increasing, increases by less than `2π` over every interval
of length at most `S - 1`, and satisfies `φ(p + S) = φ(p) + 2π` for `p ∈ [1 - S, 0]`. On
`[1 - S, 0]` it maps onto `[0, π]`, and on `[0, 1]` it is `π + π p`.

The *cyclic shift path* is `P_k(t) = exp(i φ(t - k))`, `t ∈ [0, S]`. During each unit time
interval one point travels along the lower unit semicircle from `-1` to `1`, while the
other points move counterclockwise along the upper semicircle to the position of their
left neighbour. Its configuration at integer times is the semicircle configuration
`Q_k = exp(i φ(-k))`, whose real parts increase with `k`.

The main result `cyclicShift_separation` compares the cyclic shift path, at time
`τ / (S - 1)`, with the canonical path `positiveGridWord (fullTwistWord S)` at time `τ`,
for `τ ∈ [0, S (S - 1)]`: for every pair of labels, either the real parts or the imaginary
parts of the two pairwise differences have the same strict sign. The proof reduces to a
single Coxeter word by the concatenation formula and computes the canonical path of the
Coxeter word in closed form.
-/

@[expose] public noncomputable section

open Set Filter Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-! ### The angle function -/

/-- The angle function of the cyclic shift on `S` points. -/
def cyclicShiftAngle (S : ℕ) (p : ℝ) : ℝ :=
  π + π / ((S : ℝ) - 1) * p + π * ((S : ℝ) - 2) / ((S : ℝ) - 1) * unitClamp p

theorem unitClamp_monotone : Monotone unitClamp := by
  intro x y hxy
  unfold unitClamp
  exact max_le_max le_rfl (min_le_min hxy le_rfl)

theorem unitClamp_sub_le {x y : ℝ} (hxy : x ≤ y) : unitClamp y - unitClamp x ≤ y - x := by
  unfold unitClamp
  rcases le_total y 0 with hy | hy
  · rw [max_eq_left (min_le_of_left_le hy), max_eq_left (min_le_of_left_le (hxy.trans hy))]
    linarith
  rcases le_total x 1 with hx | hx
  · rcases le_total x 0 with hx0 | hx0
    · rw [max_eq_left (min_le_of_left_le hx0)]
      rcases le_total y 1 with hy1 | hy1
      · rw [min_eq_left hy1, max_eq_right hy]
        linarith
      · rw [min_eq_right hy1, max_eq_right zero_le_one]
        linarith
    · rw [min_eq_left hx, max_eq_right hx0]
      rcases le_total y 1 with hy1 | hy1
      · rw [min_eq_left hy1, max_eq_right hy]
      · rw [min_eq_right hy1, max_eq_right zero_le_one]
        linarith
  · rw [min_eq_right hx, min_eq_right (hx.trans hxy), max_eq_right zero_le_one]
    linarith

theorem unitClamp_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : unitClamp x = x := by
  unfold unitClamp
  rw [min_eq_left hx.2, max_eq_right hx.1]

variable {S : ℕ}

theorem cyclicShiftAngle_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    cyclicShiftAngle S p = π + π / ((S : ℝ) - 1) * p := by
  simp [cyclicShiftAngle, unitClamp_of_nonpos hp]

theorem cyclicShiftAngle_of_mem_unit (hS : 2 ≤ S) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    cyclicShiftAngle S p = π + π * p := by
  have hS1 : (S : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  rw [cyclicShiftAngle, unitClamp_of_mem hp]
  field_simp
  ring

theorem cyclicShiftAngle_continuous (S : ℕ) : Continuous (cyclicShiftAngle S) := by
  unfold cyclicShiftAngle
  have := unitClamp_continuous
  fun_prop

theorem cyclicShiftAngle_strictMono (hS : 2 ≤ S) : StrictMono (cyclicShiftAngle S) := by
  intro x y hxy
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  have hS2 : (0 : ℝ) ≤ (S : ℝ) - 2 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  have hc := unitClamp_monotone hxy.le
  unfold cyclicShiftAngle
  have h1 : π / ((S : ℝ) - 1) * x < π / ((S : ℝ) - 1) * y :=
    mul_lt_mul_of_pos_left hxy (div_pos pi_pos hS1)
  have h2 : π * ((S : ℝ) - 2) / ((S : ℝ) - 1) * unitClamp x ≤
      π * ((S : ℝ) - 2) / ((S : ℝ) - 1) * unitClamp y :=
    mul_le_mul_of_nonneg_left hc (div_nonneg (mul_nonneg pi_pos.le hS2) hS1.le)
  linarith

/-- The angle increases by less than `2π` over every interval of length at most `S - 1`. -/
theorem cyclicShiftAngle_sub_lt (hS : 2 ≤ S) {x y : ℝ}
    (hlen : y - x ≤ (S : ℝ) - 1) : cyclicShiftAngle S y - cyclicShiftAngle S x < 2 * π := by
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  have hS2 : (0 : ℝ) ≤ (S : ℝ) - 2 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  have hc1 : unitClamp y - unitClamp x ≤ 1 := by
    have := unitClamp_mem y
    have := unitClamp_mem x
    linarith [(unitClamp_mem y).2, (unitClamp_mem x).1]
  have heq : cyclicShiftAngle S y - cyclicShiftAngle S x =
      π / ((S : ℝ) - 1) * (y - x) +
        π * ((S : ℝ) - 2) / ((S : ℝ) - 1) * (unitClamp y - unitClamp x) := by
    unfold cyclicShiftAngle
    ring
  rw [heq]
  have h1 : π / ((S : ℝ) - 1) * (y - x) ≤ π := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hS1]
    nlinarith [pi_pos]
  have h2 : π * ((S : ℝ) - 2) / ((S : ℝ) - 1) * (unitClamp y - unitClamp x) ≤
      π * ((S : ℝ) - 2) / ((S : ℝ) - 1) :=
    mul_le_of_le_one_right (div_nonneg (mul_nonneg pi_pos.le hS2) hS1.le) hc1
  have h3 : π * ((S : ℝ) - 2) / ((S : ℝ) - 1) < π := by
    rw [div_lt_iff₀ hS1]
    nlinarith [pi_pos]
  linarith

/-- The quasi-periodicity of the angle. -/
theorem cyclicShiftAngle_add (hS : 2 ≤ S) {p : ℝ} (hp : p ∈ Icc (1 - (S : ℝ)) 0) :
    cyclicShiftAngle S (p + S) = cyclicShiftAngle S p + 2 * π := by
  have hS1 : (S : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  have hc : unitClamp (p + S) = 1 := unitClamp_of_one_le (by linarith [hp.1])
  rw [cyclicShiftAngle, cyclicShiftAngle_of_nonpos hp.2, hc]
  field_simp
  ring

/-- On `[1 - S, 0]` the angle lies in `[0, π]`. -/
theorem cyclicShiftAngle_mem_of_nonpos (hS : 2 ≤ S) {p : ℝ} (hp : p ∈ Icc (1 - (S : ℝ)) 0) :
    cyclicShiftAngle S p ∈ Icc 0 π := by
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by
    have : (2 : ℝ) ≤ S := by exact_mod_cast hS
    linarith
  rw [cyclicShiftAngle_of_nonpos hp.2]
  constructor
  · have : π / ((S : ℝ) - 1) * p ≥ -π := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hS1]
      nlinarith [pi_pos, hp.1]
    linarith
  · have : π / ((S : ℝ) - 1) * p ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (div_pos pi_pos hS1).le hp.2
    linarith

/-! ### The cyclic shift path -/

/-- The cyclic shift path of `S` points on the unit circle. -/
def cyclicShiftPath (S : ℕ) (k : Fin S) (t : ℝ) : ℂ :=
  Complex.exp ((cyclicShiftAngle S (t - k) : ℂ) * Complex.I)

theorem cyclicShiftPath_continuous (S : ℕ) (k : Fin S) : Continuous (cyclicShiftPath S k) := by
  unfold cyclicShiftPath
  have := cyclicShiftAngle_continuous S
  fun_prop

/-! ### The canonical path of the Coxeter word in closed form -/

theorem coxeterPrefix_apply_val (j : ℕ) (hj : j ≤ S - 1) (x : Fin S) :
    ((positiveWordPrefix (coxeterWord S) j) x).val =
      if x.val < j then x.val + 1 else if x.val = j then 0 else x.val := by
  rw [positiveWordPrefix, PositiveAdjacentWord.permutation_eq_prod]
  exact prefixProduct_val j hj x

theorem coxeterPrefix_symm_val (j : ℕ) (hj : j ≤ S - 1) (y : Fin S) :
    ((positiveWordPrefix (coxeterWord S) j).symm y).val =
      if y.val = 0 then j else if y.val ≤ j then y.val - 1 else y.val := by
  have hy := y.isLt
  let z : Fin S := ⟨if y.val = 0 then j else if y.val ≤ j then y.val - 1 else y.val, by
    split_ifs <;> omega⟩
  have hz : positiveWordPrefix (coxeterWord S) j z = y := by
    apply Fin.ext
    rw [coxeterPrefix_apply_val j hj]
    simp only [z]
    split_ifs <;> omega
  have hsymm : (positiveWordPrefix (coxeterWord S) j).symm y = z :=
    (Equiv.symm_apply_eq _).mpr hz.symm
  rw [hsymm]

theorem coxeterWord_length (S : ℕ) : (coxeterWord S).length = S - 1 := by
  simp [coxeterWord]

/-- The real part of the canonical Coxeter path: the first strand moves from position `0`
to position `S - 1`, and strand `y ≥ 1` moves from `y` to `y - 1` during letter `y - 1`. -/
theorem coxeterWord_re (y : Fin S) (t : ℝ) :
    (positiveGridWord (coxeterWord S) y t).re =
      if y.val = 0 then ∑ j ∈ Finset.range (S - 1), Real.smoothTransition (t - j)
      else (y.val : ℝ) - Real.smoothTransition (t - ((y.val - 1 : ℕ) : ℝ)) := by
  have hy := y.isLt
  rw [positiveGridWord_re, positiveWordReal, coxeterWord_length]
  have hpos : ∀ j ∈ Finset.range (S - 1),
      (((positiveWordPrefix (coxeterWord S) (j + 1)).symm y).val : ℝ) -
          (((positiveWordPrefix (coxeterWord S) j).symm y).val : ℝ) =
        if y.val = 0 then 1 else if j = y.val - 1 then -1 else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [coxeterPrefix_symm_val (j + 1) (by omega), coxeterPrefix_symm_val j (by omega)]
    split_ifs <;> first | (exfalso; omega) | (push_cast; ring1) |
      (rw [Nat.cast_sub (show 1 ≤ y.val by omega)]; push_cast; ring1)
  rw [Finset.sum_congr rfl fun j hj => by rw [hpos j hj]]
  split_ifs with h0
  · simp [h0]
  · rw [Finset.sum_eq_single (y.val - 1)]
    · simp
      ring
    · intro j _ hj
      simp [hj]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim

/-- The imaginary part of the canonical Coxeter path: the first strand passes below
every other strand, and strand `y ≥ 1` passes above it during letter `y - 1`. -/
theorem coxeterWord_im (y : Fin S) (t : ℝ) :
    (positiveGridWord (coxeterWord S) y t).im =
      if y.val = 0 then -∑ j ∈ Finset.range (S - 1), positiveGridGeneratorBump (t - j)
      else positiveGridGeneratorBump (t - ((y.val - 1 : ℕ) : ℝ)) := by
  have hy := y.isLt
  rw [positiveGridWord_im, positiveGridWordImaginary_eq_sum_range, coxeterWord_length]
  have hterm : ∀ j ∈ Finset.range (S - 1),
      ((coxeterWord S)[j]?).elim 0 (fun i => positiveGridGeneratorImaginary i
        ((positiveWordPrefix (coxeterWord S) j).symm y) (t - j)) =
        if y.val = 0 then -positiveGridGeneratorBump (t - j)
        else if j = y.val - 1 then positiveGridGeneratorBump (t - j) else 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hget : (coxeterWord S)[j]? = some ⟨j, hj'⟩ := by
      rw [List.getElem?_eq_getElem (by rw [coxeterWord_length]; exact hj')]
      congr 1
      simp [coxeterWord]
    rw [hget]
    simp only [Option.elim_some, positiveGridGeneratorImaginary]
    have hv := coxeterPrefix_symm_val j (by omega) y
    have hL : ((positiveWordPrefix (coxeterWord S) j).symm y =
        adjacentLower (⟨j, hj'⟩ : Fin (S - 1))) ↔ y.val = 0 := by
      have hlow : ((adjacentLower (⟨j, hj'⟩ : Fin (S - 1)) : Fin S) : ℕ) = j := rfl
      rw [Fin.ext_iff, hv, hlow]
      split_ifs <;> constructor <;> intro <;> omega
    have hU : ((positiveWordPrefix (coxeterWord S) j).symm y =
        adjacentUpper (⟨j, hj'⟩ : Fin (S - 1))) ↔ (y.val ≠ 0 ∧ j = y.val - 1) := by
      have hup : ((adjacentUpper (⟨j, hj'⟩ : Fin (S - 1)) : Fin S) : ℕ) = j + 1 := rfl
      rw [Fin.ext_iff, hv, hup]
      split_ifs <;> constructor <;> intro <;> omega
    simp only [hL, hU]
    by_cases h0 : y.val = 0 <;> by_cases h1 : j = y.val - 1 <;> simp [h0, h1]
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h0
  · simp [Finset.sum_neg_distrib]
  · rw [Finset.sum_eq_single (y.val - 1)]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim

/-! ### Separation for one Coxeter word -/

theorem positiveGridGeneratorBump_nonneg (t : ℝ) : 0 ≤ positiveGridGeneratorBump t := by
  unfold positiveGridGeneratorBump
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  have : 0 ≤ 1 - Real.smoothTransition t := by linarith
  positivity

theorem positiveGridGeneratorBump_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < positiveGridGeneratorBump t := by
  unfold positiveGridGeneratorBump
  have h0 := Real.smoothTransition.pos_of_pos ht.1
  have h1 := Real.smoothTransition.lt_one_of_lt_one ht.2
  have : 0 < 1 - Real.smoothTransition t := by linarith
  positivity

theorem sum_smoothTransition_nat (i n : ℕ) (hi : i ≤ n) :
    ∑ j ∈ Finset.range n, Real.smoothTransition ((i : ℝ) - j) = i := by
  have hterm : ∀ j ∈ Finset.range n, Real.smoothTransition ((i : ℝ) - j) =
      if j < i then 1 else 0 := by
    intro j _
    split_ifs with h
    · apply Real.smoothTransition.one_of_one_le
      have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      linarith
    · apply Real.smoothTransition.zero_of_nonpos
      have : (i : ℝ) ≤ j := by exact_mod_cast (not_lt.mp h)
      linarith
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have : (Finset.range n).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem exp_ofReal_mul_I_re' (x : ℝ) : (Complex.exp ((x : ℂ) * Complex.I)).re = Real.cos x :=
  Complex.exp_ofReal_mul_I_re x

theorem exp_ofReal_mul_I_im' (x : ℝ) : (Complex.exp ((x : ℂ) * Complex.I)).im = Real.sin x :=
  Complex.exp_ofReal_mul_I_im x

/-- The separation predicate used for straight-line interpolation. -/
def PairSeparated (a b : ℂ) : Prop := 0 < a.re * b.re ∨ 0 < a.im * b.im

theorem PairSeparated.neg {a b : ℂ} (h : PairSeparated a b) : PairSeparated (-a) (-b) := by
  unfold PairSeparated at *
  simpa only [Complex.neg_re, Complex.neg_im, neg_mul_neg] using h

/-- Separation of the cyclic shift from the canonical Coxeter path over one letter block. -/
theorem coxeterStep_separation (hS : 2 ≤ S) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) ((S : ℝ) - 1))
    {y y' : Fin S} (hyy : y ≠ y') :
    PairSeparated
      (cyclicShiftPath S y (τ / ((S : ℝ) - 1)) - cyclicShiftPath S y' (τ / ((S : ℝ) - 1)))
      (positiveGridWord (coxeterWord S) y τ - positiveGridWord (coxeterWord S) y' τ) := by
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by linarith
  set t := τ / ((S : ℝ) - 1) with ht
  have ht01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hτ.1 hS1.le, (div_le_one hS1).mpr hτ.2⟩
  -- The angles of the cyclic shift.
  have hang0 : ∀ z : Fin S, z.val = 0 → cyclicShiftAngle S (t - z.val) = π + π * t := by
    intro z hz
    rw [hz, Nat.cast_zero, sub_zero, cyclicShiftAngle_of_mem_unit hS ht01]
  have hangpos : ∀ z : Fin S, 1 ≤ z.val →
      cyclicShiftAngle S (t - z.val) = π + π / ((S : ℝ) - 1) * (t - z.val) ∧
      cyclicShiftAngle S (t - z.val) ∈ Icc 0 π := by
    intro z hz
    have hzS : (z.val : ℝ) ≤ (S : ℝ) - 1 := by
      have := z.isLt
      have : (z.val : ℝ) + 1 ≤ S := by exact_mod_cast this
      linarith
    have hz1 : (1 : ℝ) ≤ z.val := by exact_mod_cast hz
    have hp : t - z.val ∈ Icc (1 - (S : ℝ)) 0 := ⟨by linarith [ht01.1], by linarith [ht01.2]⟩
    exact ⟨cyclicShiftAngle_of_nonpos hp.2, cyclicShiftAngle_mem_of_nonpos hS hp⟩
  have hP : ∀ z : Fin S, cyclicShiftPath S z t =
      Complex.exp ((cyclicShiftAngle S (t - z.val) : ℂ) * Complex.I) := fun z => rfl
  -- Two labels at least one.
  have hcase_pos : ∀ z z' : Fin S, 1 ≤ z.val → z.val < z'.val →
      PairSeparated (cyclicShiftPath S z t - cyclicShiftPath S z' t)
        (positiveGridWord (coxeterWord S) z τ - positiveGridWord (coxeterWord S) z' τ) := by
    intro z z' hz hzz'
    left
    have hz' : 1 ≤ z'.val := by omega
    obtain ⟨ha, haI⟩ := hangpos z hz
    obtain ⟨ha', haI'⟩ := hangpos z' hz'
    have hlt : cyclicShiftAngle S (t - z'.val) < cyclicShiftAngle S (t - z.val) :=
      cyclicShiftAngle_strictMono hS (by
        have : (z.val : ℝ) < z'.val := by exact_mod_cast hzz'
        linarith)
    have hPre : (cyclicShiftPath S z t - cyclicShiftPath S z' t).re < 0 := by
      rw [Complex.sub_re, hP, hP, exp_ofReal_mul_I_re', exp_ofReal_mul_I_re']
      have := Real.cos_lt_cos_of_nonneg_of_le_pi haI'.1 haI.2 hlt
      linarith
    have hCre : (positiveGridWord (coxeterWord S) z τ -
        positiveGridWord (coxeterWord S) z' τ).re < 0 := by
      rw [Complex.sub_re, coxeterWord_re, coxeterWord_re, if_neg (by omega), if_neg (by omega)]
      have hmono : Real.smoothTransition (τ - ((z'.val - 1 : ℕ) : ℝ)) ≤
          Real.smoothTransition (τ - ((z.val - 1 : ℕ) : ℝ)) := by
        apply Real.smoothTransition.monotone
        have : ((z.val - 1 : ℕ) : ℝ) ≤ ((z'.val - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : z.val - 1 ≤ z'.val - 1)
        linarith
      have hzz : (z.val : ℝ) + 1 ≤ z'.val := by exact_mod_cast hzz'
      linarith [Real.smoothTransition.le_one (τ - ((z.val - 1 : ℕ) : ℝ)),
        Real.smoothTransition.nonneg (τ - ((z'.val - 1 : ℕ) : ℝ))]
    exact mul_pos_of_neg_of_neg hPre hCre
  -- The first label against a later label.
  have hcase_zero : ∀ z z' : Fin S, z.val = 0 → 1 ≤ z'.val →
      PairSeparated (cyclicShiftPath S z t - cyclicShiftPath S z' t)
        (positiveGridWord (coxeterWord S) z τ - positiveGridWord (coxeterWord S) z' τ) := by
    intro z z' hz hz'
    obtain ⟨ha', haI'⟩ := hangpos z' hz'
    have hzS : (z'.val : ℝ) ≤ (S : ℝ) - 1 := by
      have := z'.isLt
      have : (z'.val : ℝ) + 1 ≤ S := by exact_mod_cast this
      linarith
    have hz1 : (1 : ℝ) ≤ z'.val := by exact_mod_cast hz'
    by_cases hint : ∃ i : ℕ, (i : ℝ) = τ
    · -- Integer time: compare real parts.
      left
      obtain ⟨i, hi⟩ := hint
      have hiS : i ≤ S - 1 := by
        have : (i : ℝ) ≤ (S : ℝ) - 1 := hi ▸ hτ.2
        have h' : ((i : ℕ) : ℝ) ≤ ((S - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          simpa using this
        exact_mod_cast h'
      have hCre : (positiveGridWord (coxeterWord S) z τ -
          positiveGridWord (coxeterWord S) z' τ).re =
          (i : ℝ) - z'.val + Real.smoothTransition ((i : ℝ) - ((z'.val - 1 : ℕ) : ℝ)) := by
        rw [Complex.sub_re, coxeterWord_re, coxeterWord_re, if_pos hz, if_neg (by omega), ← hi,
          sum_smoothTransition_nat i (S - 1) hiS]
        ring
      have hPre : (cyclicShiftPath S z t - cyclicShiftPath S z' t).re =
          Real.cos (π * (z'.val - t) / ((S : ℝ) - 1)) - Real.cos (π * t) := by
        rw [Complex.sub_re, hP, hP, exp_ofReal_mul_I_re', exp_ofReal_mul_I_re', hang0 z hz, ha',
          show π + π * t = π * t + π by ring, Real.cos_add_pi,
          show π + π / ((S : ℝ) - 1) * (t - z'.val) =
            -(π * (z'.val - t) / ((S : ℝ) - 1)) + π by ring, Real.cos_add_pi, Real.cos_neg]
        ring
      have hA0 : 0 ≤ π * (z'.val - t) / ((S : ℝ) - 1) :=
        div_nonneg (mul_nonneg pi_pos.le (by linarith [ht01.2])) hS1.le
      have hAπ : π * (z'.val - t) / ((S : ℝ) - 1) ≤ π := by
        rw [div_le_iff₀ hS1]
        nlinarith [pi_pos, ht01.1]
      have hB0 : 0 ≤ π * t := mul_nonneg pi_pos.le ht01.1
      have hBπ : π * t ≤ π := by nlinarith [pi_pos, ht01.2]
      have htval : t * ((S : ℝ) - 1) = i := by rw [ht, hi]; field_simp
      rcases le_or_gt z'.val i with hzi | hzi
      · -- The first strand has already passed strand `z'`.
        have hst : Real.smoothTransition ((i : ℝ) - ((z'.val - 1 : ℕ) : ℝ)) = 1 := by
          apply Real.smoothTransition.one_of_one_le
          rw [Nat.cast_sub hz']
          have : (z'.val : ℝ) ≤ i := by exact_mod_cast hzi
          push_cast
          linarith
        have hAB : π * (z'.val - t) / ((S : ℝ) - 1) < π * t := by
          rw [div_lt_iff₀ hS1]
          have hzi' : (z'.val : ℝ) ≤ i := by exact_mod_cast hzi
          have ht0 : 0 < t := by
            by_contra hle
            have : t = 0 := le_antisymm (not_lt.mp hle) ht01.1
            rw [this, zero_mul] at htval
            linarith
          have key : (z'.val : ℝ) - t < t * ((S : ℝ) - 1) := by linarith
          nlinarith [mul_lt_mul_of_pos_left key pi_pos]
        apply mul_pos
        · rw [hPre]
          have := Real.cos_lt_cos_of_nonneg_of_le_pi hA0 hBπ hAB
          linarith
        · rw [hCre, hst]
          have : (z'.val : ℝ) ≤ i := by exact_mod_cast hzi
          linarith
      · -- Strand `z'` has not yet been passed.
        have hst : Real.smoothTransition ((i : ℝ) - ((z'.val - 1 : ℕ) : ℝ)) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          rw [Nat.cast_sub hz']
          have : (i : ℝ) + 1 ≤ z'.val := by exact_mod_cast hzi
          push_cast
          linarith
        have hz'S : (z'.val : ℝ) + 1 ≤ S := by exact_mod_cast z'.isLt
        have hAB : π * t < π * (z'.val - t) / ((S : ℝ) - 1) := by
          rw [lt_div_iff₀ hS1]
          have hzi' : (i : ℝ) + 1 ≤ z'.val := by exact_mod_cast hzi
          have h1t : 0 ≤ (1 - t) * ((S : ℝ) - 1) := mul_nonneg (by linarith [ht01.2]) hS1.le
          have key : t * ((S : ℝ) - 1) < (z'.val : ℝ) - t := by
            by_contra hle
            have hle' := not_lt.mp hle
            nlinarith [ht01.2]
          nlinarith [mul_lt_mul_of_pos_left key pi_pos]
        apply mul_pos_of_neg_of_neg
        · rw [hPre]
          have := Real.cos_lt_cos_of_nonneg_of_le_pi hB0 hAπ hAB
          linarith
        · rw [hCre, hst]
          have : (i : ℝ) + 1 ≤ z'.val := by exact_mod_cast hzi
          linarith
    · -- Non-integer time: compare imaginary parts.
      right
      have hτ0 : 0 < τ := by
        rcases eq_or_lt_of_le hτ.1 with h | h
        · exact (hint ⟨0, by simp [← h]⟩).elim
        · exact h
      set j₀ := ⌊τ⌋₊ with hj₀
      have hj₀le : (j₀ : ℝ) ≤ τ := Nat.floor_le hτ.1
      have hj₀lt : τ < (j₀ : ℝ) + 1 := Nat.lt_floor_add_one τ
      have hj₀ne : (j₀ : ℝ) ≠ τ := fun h => hint ⟨j₀, h⟩
      have hj₀S : j₀ < S - 1 := by
        have hτS : τ < (S : ℝ) - 1 := by
          rcases eq_or_lt_of_le hτ.2 with h | h
          · exact (hint ⟨S - 1, by rw [Nat.cast_sub (by omega)]; simp [h]⟩).elim
          · exact h
        have : (j₀ : ℝ) < ((S - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          linarith
        exact_mod_cast this
      have hbump : 0 < positiveGridGeneratorBump (τ - j₀) :=
        positiveGridGeneratorBump_pos ⟨by linarith [lt_of_le_of_ne hj₀le hj₀ne], by linarith⟩
      have hsum : 0 < ∑ j ∈ Finset.range (S - 1), positiveGridGeneratorBump (τ - j) :=
        lt_of_lt_of_le hbump (Finset.single_le_sum (f := fun j : ℕ =>
          positiveGridGeneratorBump (τ - j)) (fun j _ => positiveGridGeneratorBump_nonneg _)
          (Finset.mem_range.mpr hj₀S))
      have ht0 : 0 < t := div_pos hτ0 hS1
      have ht1 : t < 1 := by
        rw [ht, div_lt_one hS1]
        rcases eq_or_lt_of_le hτ.2 with h | h
        · exact (hint ⟨S - 1, by rw [Nat.cast_sub (by omega)]; simp [h]⟩).elim
        · exact h
      apply mul_pos_of_neg_of_neg
      · rw [Complex.sub_im, hP, hP, exp_ofReal_mul_I_im', exp_ofReal_mul_I_im', hang0 z hz,
          show π + π * t = π * t + π by ring, Real.sin_add_pi]
        have h1 : 0 < Real.sin (π * t) :=
          Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
        have h2 : 0 ≤ Real.sin (cyclicShiftAngle S (t - z'.val)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi haI'.1 haI'.2
        linarith
      · rw [Complex.sub_im, coxeterWord_im, coxeterWord_im, if_pos hz, if_neg (by omega)]
        linarith [positiveGridGeneratorBump_nonneg (τ - ((z'.val - 1 : ℕ) : ℝ))]
  -- Assembly by symmetry.
  have hsymm : ∀ a b c d : ℂ, PairSeparated (a - b) (c - d) → PairSeparated (b - a) (d - c) := by
    intro a b c d h
    have := h.neg
    simpa only [neg_sub] using this
  by_cases hy0 : y.val = 0
  · have hy'0 : 1 ≤ y'.val := by
      by_contra h
      exact hyy (Fin.ext (by omega))
    exact hcase_zero y y' hy0 hy'0
  by_cases hy'0 : y'.val = 0
  · exact hsymm _ _ _ _ (hcase_zero y' y hy'0 (by omega))
  rcases lt_or_gt_of_ne (fun h : y.val = y'.val => hyy (Fin.ext h)) with h | h
  · exact hcase_pos y y' (by omega) h
  · exact hsymm _ _ _ _ (hcase_pos y' y (by omega) h)

/-! ### Separation over the full twist -/

theorem torusWord_add (m a b : ℕ) : torusWord m (a + b) = torusWord m a ++ torusWord m b := by
  simp only [torusWord, List.replicate_add, List.flatten_append]

theorem fullTwistWord_split {n : ℕ} (hn : n < S) :
    fullTwistWord S = torusWord S n ++ (coxeterWord S ++ torusWord S (S - n - 1)) := by
  have h : torusWord S S = torusWord S (n + (1 + (S - n - 1))) :=
    congrArg (torusWord S) (by omega)
  rw [fullTwistWord, h, torusWord_add, torusWord_add]
  congr 2
  simp [torusWord]

theorem finRotate_pow_apply_val (n : ℕ) (y : Fin S) :
    (((finRotate S) ^ n) y).val = (y.val + n) % S := by
  have hS : 0 < S := Fin.pos y
  obtain ⟨m, rfl⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  induction n with
  | zero => simp [Nat.mod_eq_of_lt y.isLt]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add_one]
    split_ifs with h
    · have h' : (((finRotate (m + 1)) ^ n) y).val = m := by
        rw [h]
        simp
      rw [ih] at h'
      rw [show y.val + (n + 1) = (y.val + n) + 1 by ring, Nat.add_mod, h']
      simp
    · have hlt : (((finRotate (m + 1)) ^ n) y).val < m := by
        have := (((finRotate (m + 1)) ^ n) y).isLt
        have hne : (((finRotate (m + 1)) ^ n) y).val ≠ m := fun he => h (Fin.ext (by simp [he]))
        omega
      rw [ih] at hlt ⊢
      rw [show y.val + (n + 1) = (y.val + n) + 1 by ring, Nat.add_mod (y.val + n) 1]
      rw [Nat.mod_eq_of_lt (show (y.val + n) % (m + 1) + 1 % (m + 1) < m + 1 by
        rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
        · rw [Nat.mod_eq_of_lt h1]
          omega
        · omega)]
      rcases Nat.lt_or_ge 1 (m + 1) with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]
      · omega

/-- Over the letter block `n`, the canonical full-twist path is the canonical Coxeter
path in the labels rotated by `n`. -/
theorem fullTwistWord_block {n : ℕ} (hn : n < S) (k : Fin S) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) ((S : ℝ) - 1)) :
    positiveGridWord (fullTwistWord S) k ((n : ℝ) * ((S : ℝ) - 1) + τ) =
      positiveGridWord (coxeterWord S) (((finRotate S) ^ n).symm k) τ := by
  have hS1 : 1 ≤ S := by omega
  have hlen : ((torusWord S n).length : ℝ) = (n : ℝ) * ((S : ℝ) - 1) := by
    rw [torusWord_length, Nat.cast_mul, Nat.cast_sub hS1]
    simp
  rw [fullTwistWord_split hn, positiveGridWord_append_of_ge _ _ _ (by rw [hlen]; linarith [hτ.1]),
    torusWord_permutation, hlen, add_sub_cancel_left,
    positiveGridWord_append_of_le _ _ _
      (by rw [coxeterWord_length, Nat.cast_sub hS1]; simpa using hτ.2)]

/-- Over the unit time interval `n`, the cyclic shift is the first unit interval in the
labels rotated by `n`. -/
theorem cyclicShiftPath_block (hS : 2 ≤ S) {n : ℕ} (hn : n < S) (k : Fin S) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    cyclicShiftPath S k ((n : ℝ) + t) = cyclicShiftPath S (((finRotate S) ^ n).symm k) t := by
  set y := ((finRotate S) ^ n).symm k with hy
  have hk : k = ((finRotate S) ^ n) y := by simp [hy]
  have hkval : k.val = (y.val + n) % S := by rw [hk]; exact finRotate_pow_apply_val n y
  have hyS := y.isLt
  unfold cyclicShiftPath
  rcases Nat.lt_or_ge (y.val + n) S with h | h
  · rw [Nat.mod_eq_of_lt h] at hkval
    have : (n : ℝ) + t - (k.val : ℝ) = t - y.val := by
      rw [hkval]
      push_cast
      ring
    rw [this]
  · have hk' : k.val = y.val + n - S := by
      rw [hkval, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    have hy1 : 1 ≤ y.val := by omega
    have : (n : ℝ) + t - (k.val : ℝ) = (t - y.val) + S := by
      rw [hk', Nat.cast_sub h]
      push_cast
      ring
    have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
    have hyr : (1 : ℝ) ≤ y.val := by exact_mod_cast hy1
    have hyS' : (y.val : ℝ) + 1 ≤ S := by exact_mod_cast hyS
    rw [this, cyclicShiftAngle_add hS ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    push_cast
    rw [add_mul, Complex.exp_add, show (2 * (π : ℂ)) * Complex.I = 2 * π * Complex.I by ring,
      Complex.exp_two_pi_mul_I, mul_one]

/-- **Separation of the cyclic shift from the canonical full twist.** -/
theorem cyclicShift_separation (hS : 2 ≤ S) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) ((S : ℝ) * ((S : ℝ) - 1))) {k l : Fin S} (hkl : k ≠ l) :
    PairSeparated
      (cyclicShiftPath S k (τ / ((S : ℝ) - 1)) - cyclicShiftPath S l (τ / ((S : ℝ) - 1)))
      (positiveGridWord (fullTwistWord S) k τ - positiveGridWord (fullTwistWord S) l τ) := by
  have hSr : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hS1 : (0 : ℝ) < (S : ℝ) - 1 := by linarith
  set u := τ / ((S : ℝ) - 1) with hu
  have hu0 : 0 ≤ u := div_nonneg hτ.1 hS1.le
  have huS : u ≤ S := by rw [hu, div_le_iff₀ hS1]; linarith [hτ.2]
  set n := min ⌊u⌋₊ (S - 1) with hn
  have hnS : n < S := by omega
  have hnu : (n : ℝ) ≤ u := (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hu0)
  have hun : u ≤ (n : ℝ) + 1 := by
    rcases le_total ⌊u⌋₊ (S - 1) with h | h
    · rw [hn, min_eq_left h]
      exact (Nat.lt_floor_add_one u).le
    · rw [hn, min_eq_right h, Nat.cast_sub (by omega)]
      push_cast
      linarith
  set t := u - n with htdef
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hτ' : t * ((S : ℝ) - 1) ∈ Icc (0 : ℝ) ((S : ℝ) - 1) :=
    ⟨mul_nonneg ht.1 hS1.le, by nlinarith [ht.2]⟩
  have hτeq : τ = (n : ℝ) * ((S : ℝ) - 1) + t * ((S : ℝ) - 1) := by
    rw [htdef, hu]
    field_simp
    ring
  have hueq : u = (n : ℝ) + t := by rw [htdef]; ring
  have htt : t * ((S : ℝ) - 1) / ((S : ℝ) - 1) = t := by field_simp
  rw [hueq, cyclicShiftPath_block hS hnS k ht, cyclicShiftPath_block hS hnS l ht, hτeq,
    fullTwistWord_block hnS k hτ', fullTwistWord_block hnS l hτ']
  have h := coxeterStep_separation hS hτ'
    (y := ((finRotate S) ^ n).symm k) (y' := ((finRotate S) ^ n).symm l)
    (fun he => hkl (((finRotate S) ^ n).symm.injective he))
  rwa [htt] at h

end OnLeConjecture.Analytic
