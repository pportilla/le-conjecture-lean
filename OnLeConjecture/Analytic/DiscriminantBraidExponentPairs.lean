/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WindingNumberCrossing
public import OnLeConjecture.KnotTheory.PositivePermutationWords

/-!
# Signed projected crossings of a closed family of sheets

A labelled family `y : Fin m → ℝ → ℂ` of pairwise distinct sheets over
`[b, b + 2π]`, closing up by a permutation `τ` of the labels, is projected by
`θ ↦ Re (c y_k(θ))` for a fixed nonzero `c`. `SheetCrossingData` records, for every
unordered pair `k < l`, the finite set of its projected crossings, all interior
and transverse. The signed crossing count `signedCount` uses the native positive
crossing convention `-Im d · (Re d)' > 0` for `d = c (y_k - y_l)`, and counts a
simultaneous crossing of several sheets once for each coincident unordered pair.

For each pair, the signed number of crossings is the change of
`⌊α / π - 1 / 2⌋` along a continuous argument `α` of `c (y_k - y_l)`. The
endpoint permutation permutes the unordered pairs, and exchanging the two members
of a pair changes the argument by an odd multiple of `π`. Hence the fractional
parts at the two endpoints cancel after summation over all pairs, and
`2 π · signedCount` is the argument change of `∏_{k ≠ l} (y_k - y_l)`.

A signed adjacent word assembled from per-event words whose exponents are the
signed numbers of coincident pairs has exponent `signedCount`. For a positive
word the exponent is the length.
-/

@[expose] public noncomputable section

open Set Real

namespace OnLeConjecture.Analytic

open KnotTheory

/-- Projected crossing data of a labelled family of `m` sheets over `[b, b + 2π]`
for the projection `θ ↦ Re (c y_k(θ))`. Every crossing of an unordered pair is
interior and transverse. -/
structure SheetCrossingData (m : ℕ) (y : Fin m → ℝ → ℂ) (b : ℝ) (c : ℂ) where
  /-- The projected crossing times of the pair `k < l`. -/
  crossings : Fin m → Fin m → Finset ℝ
  mem_crossings_iff : ∀ k l : Fin m, k < l → ∀ θ ∈ Icc b (b + 2 * π),
    (c * (y k θ - y l θ)).re = 0 ↔ θ ∈ crossings k l
  crossings_subset : ∀ k l : Fin m, k < l → ∀ θ ∈ crossings k l, θ ∈ Ioo b (b + 2 * π)
  /-- The derivative of the sheet difference at its crossing times. -/
  derivative : Fin m → Fin m → ℝ → ℂ
  hasDerivAt : ∀ k l : Fin m, k < l → ∀ θ ∈ crossings k l,
    HasDerivAt (fun t => y k t - y l t) (derivative k l θ) θ
  transverse : ∀ k l : Fin m, k < l → ∀ θ ∈ crossings k l, (c * derivative k l θ).re ≠ 0

namespace SheetCrossingData

variable {m : ℕ} {y : Fin m → ℝ → ℂ} {b : ℝ} {c : ℂ}

/-- The sign of the projected crossing of the ordered pair `(k, l)` at `θ`, with
the native positive-crossing convention `-Im d · (Re d)' > 0` for `d = c (y_k - y_l)`. -/
def crossingSign (D : SheetCrossingData m y b c) (k l : Fin m) (θ : ℝ) : ℤ :=
  realSignInt (-(c * (y k θ - y l θ)).im * (c * D.derivative k l θ).re)

/-- The signed number of projected crossings. A simultaneous crossing of several
sheets contributes one signed term for each coincident unordered pair. -/
def signedCount (D : SheetCrossingData m y b c) : ℤ :=
  ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2),
    ∑ θ ∈ D.crossings p.1 p.2, D.crossingSign p.1 p.2 θ

end SheetCrossingData

/-! ### Fractional parts of arguments -/

theorem fract_im_div_pi_eq_of_exp_eq {z w : ℂ} (h : Complex.exp z = Complex.exp w) :
    Int.fract (z.im / π - 1 / 2) = Int.fract (w.im / π - 1 / 2) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have him : z.im = w.im + 2 * π * n := by
    rw [hn]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [show z.im / π - 1 / 2 = (w.im / π - 1 / 2) + ((2 * n : ℤ) : ℝ) by
    rw [him]
    push_cast
    field_simp
    ring, Int.fract_add_intCast]

theorem fract_im_div_pi_eq_of_exp_eq_neg {z w : ℂ} (h : Complex.exp z = -Complex.exp w) :
    Int.fract (z.im / π - 1 / 2) = Int.fract (w.im / π - 1 / 2) := by
  have h' : Complex.exp z = Complex.exp (w + π * Complex.I) := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I, h]
    ring
  rw [fract_im_div_pi_eq_of_exp_eq h']
  rw [show (w + π * Complex.I).im / π - 1 / 2 = (w.im / π - 1 / 2) + ((1 : ℤ) : ℝ) by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    push_cast
    field_simp
    ring, Int.fract_add_intCast]

/-! ### The pair count -/

namespace SheetCrossingData

variable {m : ℕ} {y : Fin m → ℝ → ℂ} {b : ℝ} {c : ℂ}

/-- The pair-count identity: `2 π` times the signed crossing count is the
argument change of the product of all ordered sheet differences. -/
theorem argChange_prod_offDiag_eq (D : SheetCrossingData m y b c) (hc : c ≠ 0)
    (hy : ∀ k, ContinuousOn (y k) (Icc b (b + 2 * π)))
    (hinj : ∀ θ ∈ Icc b (b + 2 * π), Function.Injective fun k => y k θ)
    (τ : Equiv.Perm (Fin m)) (hτ : ∀ k, y k (b + 2 * π) = y (τ k) b) :
    argChange (fun θ => ∏ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 ≠ p.2), (y p.1 θ - y p.2 θ)) b (b + 2 * π) = 2 * π * D.signedCount := by
  classical
  set v := b + 2 * π with hv
  have huv : b ≤ v := by rw [hv]; linarith [Real.pi_pos]
  have hu : b ∈ Icc b v := left_mem_Icc.mpr huv
  have hvI : v ∈ Icc b v := right_mem_Icc.mpr huv
  have hdcont : ∀ k l : Fin m, ContinuousOn (fun θ => y k θ - y l θ) (Icc b v) :=
    fun k l => (hy k).sub (hy l)
  have hdne : ∀ k l : Fin m, k ≠ l → ∀ θ ∈ Icc b v, y k θ - y l θ ≠ 0 :=
    fun k l hkl θ hθ h => hkl (hinj θ hθ (sub_eq_zero.mp h))
  have hex : ∀ k l : Fin m, ∃ L : ℝ → ℂ,
      k ≠ l → IsContinuousLogOn (fun θ => c * (y k θ - y l θ)) L b v := by
    intro k l
    by_cases hkl : k = l
    · exact ⟨0, fun h => (h hkl).elim⟩
    · obtain ⟨L, hL⟩ := exists_isContinuousLogOn (continuousOn_const.mul (hdcont k l))
        (fun θ hθ => mul_ne_zero hc (hdne k l hkl θ hθ))
      exact ⟨L, fun _ => hL⟩
  choose L hL using hex
  let x : Fin m → Fin m → ℝ → ℝ := fun k l θ => (L k l θ).im / π - 1 / 2
  set S := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2) with hS
  -- Step 1: the pair count for every unordered pair.
  have hpair : ∀ p ∈ S, (⌊x p.1 p.2 v⌋ - ⌊x p.1 p.2 b⌋ : ℤ) =
      ∑ θ ∈ D.crossings p.1 p.2, D.crossingSign p.1 p.2 θ := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact (hL p.1 p.2 hlt.ne).floor_sub_floor_eq_sum_crossingSign huv (D.crossings p.1 p.2)
      (fun θ hθ => D.mem_crossings_iff p.1 p.2 hlt θ hθ) (D.crossings_subset p.1 p.2 hlt)
      (fun θ => c * D.derivative p.1 p.2 θ)
      (fun θ hθ => ⟨(D.hasDerivAt p.1 p.2 hlt θ hθ).const_mul c, D.transverse p.1 p.2 hlt θ hθ⟩)
  have hcount : (D.signedCount : ℝ) = ∑ p ∈ S, ((⌊x p.1 p.2 v⌋ : ℝ) - ⌊x p.1 p.2 b⌋) := by
    rw [signedCount, ← hS, Int.cast_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← hpair p hp]
    push_cast
    ring
  -- Step 2: the fractional parts at the two endpoints cancel.
  let q : Fin m × Fin m → Fin m × Fin m := fun p => (min (τ p.1) (τ p.2), max (τ p.1) (τ p.2))
  let q' : Fin m × Fin m → Fin m × Fin m :=
    fun p => (min (τ.symm p.1) (τ.symm p.2), max (τ.symm p.1) (τ.symm p.2))
  have hfract : ∑ p ∈ S, Int.fract (x p.1 p.2 v) = ∑ p ∈ S, Int.fract (x p.1 p.2 b) := by
    apply Finset.sum_nbij' q q'
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hne : τ p.1 ≠ τ p.2 := fun h => hlt.ne (τ.injective h)
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, q]
      exact min_lt_max.mpr hne
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hne : τ.symm p.1 ≠ τ.symm p.2 := fun h => hlt.ne (τ.symm.injective h)
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, q']
      exact min_lt_max.mpr hne
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      rcases lt_or_gt_of_ne (fun h : τ p.1 = τ p.2 => hlt.ne (τ.injective h)) with h | h
      · simp only [q, q', min_eq_left h.le, max_eq_right h.le, Equiv.symm_apply_apply,
          min_eq_left hlt.le, max_eq_right hlt.le]
      · simp only [q, q', min_eq_right h.le, max_eq_left h.le, Equiv.symm_apply_apply,
          min_eq_right hlt.le, max_eq_left hlt.le]
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      rcases lt_or_gt_of_ne (fun h : τ.symm p.1 = τ.symm p.2 => hlt.ne (τ.symm.injective h))
        with h | h
      · simp only [q, q', min_eq_left h.le, max_eq_right h.le, Equiv.apply_symm_apply,
          min_eq_left hlt.le, max_eq_right hlt.le]
      · simp only [q, q', min_eq_right h.le, max_eq_left h.le, Equiv.apply_symm_apply,
          min_eq_right hlt.le, max_eq_left hlt.le]
    · intro p hp
      have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      have hexpv : Complex.exp (L p.1 p.2 v) = c * (y (τ p.1) b - y (τ p.2) b) := by
        rw [(hL p.1 p.2 hlt.ne).2 v hvI]
        simp only [hτ]
      rcases lt_or_gt_of_ne (fun h : τ p.1 = τ p.2 => hlt.ne (τ.injective h)) with h | h
      · simp only [q, min_eq_left h.le, max_eq_right h.le]
        apply fract_im_div_pi_eq_of_exp_eq
        rw [hexpv, (hL (τ p.1) (τ p.2) h.ne).2 b hu]
      · simp only [q, min_eq_right h.le, max_eq_left h.le]
        apply fract_im_div_pi_eq_of_exp_eq_neg
        rw [hexpv, (hL (τ p.2) (τ p.1) h.ne).2 b hu]
        ring
  -- Step 3: the signed count is the sum of the argument changes over `π`.
  have hfloor : ∀ r : ℝ, (⌊r⌋ : ℝ) = r - Int.fract r := fun r => by rw [Int.fract]; ring
  have hcount' : (D.signedCount : ℝ) * π = ∑ p ∈ S, argChange
      (fun θ => c * (y p.1 θ - y p.2 θ)) b v := by
    rw [hcount, Finset.sum_mul]
    have hsplit : ∑ p ∈ S, ((⌊x p.1 p.2 v⌋ : ℝ) - ⌊x p.1 p.2 b⌋) * π =
        ∑ p ∈ S, (x p.1 p.2 v - x p.1 p.2 b) * π -
          (∑ p ∈ S, Int.fract (x p.1 p.2 v) - ∑ p ∈ S, Int.fract (x p.1 p.2 b)) * π := by
      rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hfloor, hfloor]
      ring
    rw [hsplit, hfract, sub_self, zero_mul, sub_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    rw [(hL p.1 p.2 hlt.ne).argChange_eq huv, Complex.sub_im]
    simp only [x]
    field_simp
    ring
  -- Step 4: the argument change of the product over ordered pairs.
  set T := (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 ≠ p.2) with hT
  have hprod : argChange (fun θ => ∏ p ∈ T, (y p.1 θ - y p.2 θ)) b v =
      ∑ p ∈ T, argChange (fun θ => y p.1 θ - y p.2 θ) b v :=
    argChange_finset_prod T huv (fun p _ => hdcont p.1 p.2)
      (fun p hp θ hθ => hdne p.1 p.2 (Finset.mem_filter.mp hp).2 θ hθ)
  have hconst : ∀ k l : Fin m, k ≠ l → argChange (fun θ => y k θ - y l θ) b v =
      argChange (fun θ => c * (y k θ - y l θ)) b v := fun k l hkl =>
    (argChange_const_mul huv (hdcont k l) (hdne k l hkl) hc).symm
  have hswap : ∀ k l : Fin m, k ≠ l → argChange (fun θ => y l θ - y k θ) b v =
      argChange (fun θ => y k θ - y l θ) b v := by
    intro k l hkl
    rw [argChange_congr (γ := fun θ => (-1 : ℂ) * (y k θ - y l θ)) huv
      (continuousOn_const.mul (hdcont k l))
      (fun θ hθ => mul_ne_zero (by norm_num) (hdne k l hkl θ hθ)) (fun θ _ => by ring)]
    exact argChange_const_mul huv (hdcont k l) (hdne k l hkl) (by norm_num)
  have hTsplit : ∑ p ∈ T, argChange (fun θ => y p.1 θ - y p.2 θ) b v =
      2 * ∑ p ∈ S, argChange (fun θ => c * (y p.1 θ - y p.2 θ)) b v := by
    have hunion : T = S ∪ (Finset.univ.filter fun p : Fin m × Fin m => p.2 < p.1) := by
      ext p
      simp only [T, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
    have hdisj : Disjoint S (Finset.univ.filter fun p : Fin m × Fin m => p.2 < p.1) := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      exact lt_asymm h1 h2
    rw [hunion, Finset.sum_union hdisj, two_mul]
    congr 1
    · exact Finset.sum_congr rfl fun p hp => hconst p.1 p.2 (Finset.mem_filter.mp hp).2.ne
    · apply Finset.sum_nbij' Prod.swap Prod.swap
      · intro p hp
        simpa [S] using hp
      · intro p hp
        simpa [S] using hp
      · intro p _
        simp
      · intro p _
        simp
      · intro p hp
        have hlt : p.2 < p.1 := (Finset.mem_filter.mp hp).2
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [← hconst p.2 p.1 hlt.ne, hswap p.2 p.1 hlt.ne]
  rw [hprod, hTsplit, ← hcount']
  ring

end SheetCrossingData

end OnLeConjecture.Analytic

/-! ### Exponents of signed words -/

namespace OnLeConjecture.KnotTheory

/-- The exponent sum of a signed adjacent word. -/
def SignedAdjacentWord.exponentSum {m : ℕ} (w : SignedAdjacentWord m) : ℤ :=
  (w.map fun a => ((a.2 : ℤˣ) : ℤ)).sum

@[simp] theorem SignedAdjacentWord.exponentSum_nil (m : ℕ) :
    SignedAdjacentWord.exponentSum ([] : SignedAdjacentWord m) = 0 := rfl

@[simp] theorem SignedAdjacentWord.exponentSum_append {m : ℕ} (v w : SignedAdjacentWord m) :
    SignedAdjacentWord.exponentSum (v ++ w) =
      SignedAdjacentWord.exponentSum v + SignedAdjacentWord.exponentSum w := by
  simp [SignedAdjacentWord.exponentSum]

theorem SignedAdjacentWord.exponentSum_flatten {m N : ℕ} (w : Fin N → SignedAdjacentWord m) :
    SignedAdjacentWord.exponentSum (List.ofFn w).flatten =
      ∑ j, SignedAdjacentWord.exponentSum (w j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.ofFn_succ, List.flatten_cons, SignedAdjacentWord.exponentSum_append,
      Fin.sum_univ_succ, ih (fun j => w j.succ)]

/-- A positive word has exponent sum equal to its length. -/
theorem PositiveAdjacentWord.exponentSum_toSigned {m : ℕ}
    (w : PositiveAdjacentWord m) :
    SignedAdjacentWord.exponentSum (PositiveAdjacentWord.toSigned w) = w.length := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (((i, (1 : ℤˣ)) :: PositiveAdjacentWord.toSigned w).map
      fun a => ((a.2 : ℤˣ) : ℤ)).sum = _
    rw [List.map_cons, List.sum_cons]
    change 1 + SignedAdjacentWord.exponentSum (PositiveAdjacentWord.toSigned w) = _
    rw [ih, List.length_cons]
    push_cast
    ring

end OnLeConjecture.KnotTheory

namespace OnLeConjecture.Analytic

open KnotTheory

namespace SheetCrossingData

variable {m : ℕ} {y : Fin m → ℝ → ℂ} {b : ℝ} {c : ℂ}

/-- Signed event words: if the events enumerate distinct times covering all
crossings, and the word of each event has as exponent the signed number of
unordered pairs crossing at that event, then the assembled word has exponent
equal to the signed crossing count. -/
theorem exponentSum_flatten_eq_signedCount (D : SheetCrossingData m y b c) {N : ℕ}
    (event : Fin N → ℝ) (hevent : Function.Injective event)
    (hcover : ∀ k l : Fin m, k < l → ∀ θ ∈ D.crossings k l, ∃ j, event j = θ)
    (w : Fin N → SignedAdjacentWord m)
    (hw : ∀ j, SignedAdjacentWord.exponentSum (w j) =
      ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter
          (fun p => p.1 < p.2 ∧ event j ∈ D.crossings p.1 p.2),
        D.crossingSign p.1 p.2 (event j)) :
    SignedAdjacentWord.exponentSum (List.ofFn w).flatten = D.signedCount := by
  classical
  rw [SignedAdjacentWord.exponentSum_flatten]
  simp only [hw, signedCount]
  -- Exchange the two sums.
  have h1 : ∀ j, ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter
      (fun p => p.1 < p.2 ∧ event j ∈ D.crossings p.1 p.2), D.crossingSign p.1 p.2 (event j) =
      ∑ p ∈ (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1 < p.2),
        if event j ∈ D.crossings p.1 p.2 then D.crossingSign p.1 p.2 (event j) else 0 := by
    intro j
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1 < p.2 <;> by_cases h' : event j ∈ D.crossings p.1 p.2 <;> simp [h, h']
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => event j)
  · intro j hj
    simpa using hj
  · intro j₁ _ j₂ _ h
    exact hevent h
  · intro θ hθ
    obtain ⟨j, hj⟩ := hcover p.1 p.2 hlt θ hθ
    exact ⟨j, by simpa [hj] using hθ, hj⟩
  · intro j _
    rfl

end SheetCrossingData

end OnLeConjecture.Analytic
