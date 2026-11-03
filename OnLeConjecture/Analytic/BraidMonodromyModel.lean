/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyExchange
public import OnLeConjecture.Analytic.BraidMonodromyHomotopy
public import OnLeConjecture.Analytic.MultiSheetBraidWordModel
public import OnLeConjecture.Analytic.ReducedCurveFullTwist

/-!
# Path words of the canonical word models, and the word form of job J14

The canonical smooth path `positiveGridWord W` of a positive word `W`
(`KnotTheory/PositiveBraidGridWordModel.lean`) runs the letters of `W` on consecutive unit
intervals, each letter by the fixed generator `positiveGridGenerator`. This module computes its
path word.

* `isPathWord_positiveGridGenerator`: the generator `σ_i` on `[0, 1]` has path word `σ_i`. Its
  lexicographic order is the identity up to time `1/2` and the exchange `σ_i` afterwards, and at
  time `1/2` the strand moving to the left is the higher one.
* `isPathWord_positiveGridWord`, `isPathWord_positiveWordModel`: the canonical closed braid of a
  positive word `W` has path word `W`.
* `IsRepresentedByPositiveWord.signedBraidConj`: a closed braid represented through closed
  braids by a positive word `W` (job J14) has every path word conjugate to `W` by a finite
  signed-word derivation.
* `Germ.exists_transverse_fullTwist_pathWord`: the word form of Theorem
  `J14:thm:transverse-germ`. For a transverse reduced germ of multiplicity `S`, the root braid
  `y r` over every sufficiently small circle has a path word, and every path word of `y r` is
  conjugate to `d_S w`, where `d_S = fullTwistWord S` and `w` is the J14 word, with the cycle
  and length identities of J14.

This answers the question raised in `docs/route-n/J22L-statement-E-lean-status.md` (§3, item 1):
the isotopy form of (I1) does give a finite signed-word derivation, up to whole-word conjugacy.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory OnLeConjecture.Analytic.Germ PlaneCurve

/-! ### The generator -/

theorem positiveGridGenerator_re_eq {n : ℕ} (i : Fin n) (k : Fin (n + 1)) (t : ℝ) :
    (positiveGridGenerator (m := n + 1) i k t).re =
      if k.val = i.val then i.val + Real.smoothTransition t
      else if k.val = i.val + 1 then i.val + 1 - Real.smoothTransition t else k.val := by
  simp only [positiveGridGenerator, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    positiveAdjacentReal, adjacentSwap_apply_val]
  split_ifs with h1 h2
  · rw [h1]; push_cast; ring
  · rw [h2]; push_cast; ring
  · ring

theorem smoothTransition_le_half {t : ℝ} (ht : t ≤ 1 / 2) : Real.smoothTransition t ≤ 1 / 2 := by
  have := Real.smoothTransition.monotone ht
  rwa [(KnotTheory.smoothTransition_eq_half_iff (1 / 2)).mpr rfl] at this

theorem half_lt_smoothTransition {t : ℝ} (ht : 1 / 2 < t) : 1 / 2 < Real.smoothTransition t := by
  have h1 := Real.smoothTransition.monotone ht.le
  rw [(KnotTheory.smoothTransition_eq_half_iff (1 / 2)).mpr rfl] at h1
  refine lt_of_le_of_ne h1 fun h => ?_
  have := (KnotTheory.smoothTransition_eq_half_iff t).mp h.symm
  linarith

theorem configSort_positiveGridGenerator_of_le {n : ℕ} (i : Fin n) {t : ℝ} (ht : t ≤ 1 / 2) :
    configSort (fun k => positiveGridGenerator (m := n + 1) i k t) = 1 := by
  symm
  apply eq_configSort (positiveGridGenerator_injective (m := n + 1) i t)
  simp only [Equiv.Perm.coe_one, id]
  rw [Fin.strictMono_iff_lt_succ]
  intro q
  have hs := smoothTransition_le_half ht
  have hs0 := Real.smoothTransition.nonneg t
  rw [lexKey_lt_iff, positiveGridGenerator_re_eq, positiveGridGenerator_re_eq]
  simp only [Fin.val_castSucc, Fin.val_succ]
  by_cases hq : q.val = i.val
  · rw [if_pos hq, if_neg (by omega), if_pos (by omega)]
    rcases lt_or_eq_of_le hs with hlt | heq
    · left; linarith
    · right
      have ht' : t = 1 / 2 := (KnotTheory.smoothTransition_eq_half_iff t).mp heq
      refine ⟨by linarith, ?_⟩
      have hlo : q.castSucc = adjacentLower (m := n + 1) i := Fin.ext (by simp [hq])
      have hup : q.succ = adjacentUpper (m := n + 1) i := Fin.ext (by simp [hq])
      rw [hlo, hup]
      simp only [positiveGridGenerator, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        positiveGridGeneratorImaginary_lower, positiveGridGeneratorImaginary_upper, ht',
        positiveGridGeneratorBump_half]
      norm_num
  · left
    by_cases hq1 : q.val = i.val + 1
    · rw [if_neg (by omega), if_pos hq1, if_neg (by omega), if_neg (by omega)]
      push_cast
      rw [hq1]
      push_cast
      linarith
    · by_cases hq2 : q.val + 1 = i.val
      · rw [if_neg hq, if_neg hq1, if_pos hq2]
        have : (q.val : ℝ) + 1 = i.val := by exact_mod_cast hq2
        linarith
      · rw [if_neg hq, if_neg hq1, if_neg hq2, if_neg (by omega)]
        push_cast
        linarith

theorem positiveGridGenerator_swap_re_eq {n : ℕ} (i : Fin n) (j : Fin (n + 1)) (t : ℝ) :
    (positiveGridGenerator (m := n + 1) i (adjacentSwap (m := n + 1) i j) t).re =
      if j.val = i.val then i.val + 1 - Real.smoothTransition t
      else if j.val = i.val + 1 then i.val + Real.smoothTransition t else j.val := by
  rw [positiveGridGenerator_re_eq, adjacentSwap_apply_val]
  by_cases h1 : j.val = i.val
  · simp [h1]
  · by_cases h2 : j.val = i.val + 1
    · simp [h2]
    · simp [h1, h2]

theorem configSort_positiveGridGenerator_of_gt {n : ℕ} (i : Fin n) {t : ℝ} (ht : 1 / 2 < t) :
    configSort (fun k => positiveGridGenerator (m := n + 1) i k t) =
      adjacentSwap (m := n + 1) i := by
  symm
  apply eq_configSort (positiveGridGenerator_injective (m := n + 1) i t)
  rw [Fin.strictMono_iff_lt_succ]
  intro q
  have hs := half_lt_smoothTransition ht
  have hs1 := Real.smoothTransition.le_one t
  rw [lexKey_lt_iff]
  left
  rw [positiveGridGenerator_swap_re_eq, positiveGridGenerator_swap_re_eq]
  simp only [Fin.val_castSucc, Fin.val_succ]
  have hqn : q.val < n := q.isLt
  by_cases hq : q.val = i.val
  · rw [if_pos hq, if_neg (by omega), if_pos (by omega)]
    linarith
  · by_cases hq1 : q.val = i.val + 1
    · rw [if_neg hq, if_pos hq1, if_neg (by omega), if_neg (by omega)]
      have : (q.val : ℝ) = i.val + 1 := by exact_mod_cast hq1
      push_cast
      linarith
    · by_cases hq2 : q.val + 1 = i.val
      · rw [if_neg hq, if_neg hq1, if_pos hq2]
        have : (q.val : ℝ) + 1 = i.val := by exact_mod_cast hq2
        linarith
      · rw [if_neg hq, if_neg hq1, if_neg hq2, if_neg (by omega)]
        push_cast
        linarith

/-- **The generator.** The fixed smooth representative of `σ_i` on `[0, 1]` has path word
`σ_i`. -/
theorem isPathWord_positiveGridGenerator {n : ℕ} (i : Fin n) :
    IsPathWord (positiveGridGenerator (m := n + 1) i) 0 1
      ([(i, 1)] : SignedAdjacentWord (n + 1)) := by
  have h := IsPathWord.of_positive_exchange (K := positiveGridGenerator (m := n + 1) i)
    (u := 0) (v := 1) (c := 1 / 2) (π := 1) (i := i)
    (fun k => (positiveGridGenerator_contDiff (m := n + 1) i k).continuous.continuousOn)
    (fun t _ => positiveGridGenerator_injective (m := n + 1) i t) (by norm_num) (by norm_num)
    (fun t _ ht => configSort_positiveGridGenerator_of_le i ht)
    (fun t _ ht => by rw [one_mul]; exact configSort_positiveGridGenerator_of_gt i ht)
  exact h

/-! ### Canonical word paths -/

/-- The letter `j` of the canonical word path has path word `σ_{w_j}` on `[j, j + 1]`. -/
theorem isPathWord_positiveGridWord_stage {n : ℕ} (w : PositiveAdjacentWord (n + 1)) (j : ℕ)
    (hj : j < w.length) :
    IsPathWord (positiveGridWord w) j (j + 1) ([(w[j], 1)] : SignedAdjacentWord (n + 1)) := by
  have h1 := isPathWord_positiveGridGenerator (n := n) w[j]
  have h2 : IsPathWord (fun k t => positiveGridGenerator (m := n + 1) w[j] k (t - j)) j (j + 1)
      ([(w[j], 1)] : SignedAdjacentWord (n + 1)) := by
    refine IsPathWord.comp_affine (K := positiveGridGenerator (m := n + 1) w[j])
      (φ := fun t => t - j) (α := 1) (β := -j) one_pos (fun t => by ring) ?_
    simpa using h1
  have h3 := (IsPathWord.relabel (K := fun k t => positiveGridGenerator (m := n + 1) w[j] k (t - j))
    (fun t _ => positiveGridGenerator_injective w[j] (t - j))
    (positiveWordPrefix w j).symm).mpr h2
  refine h3.of_eqOn fun k t ht => ?_
  exact (positiveGridWord_stage w j hj k ht).symm

/-- **The canonical word path.** The canonical smooth path of a positive word `W` on
`[0, length W + 1]` has path word `W`. -/
theorem isPathWord_positiveGridWord {n : ℕ} (w : PositiveAdjacentWord (n + 1)) :
    IsPathWord (positiveGridWord w) 0 ((w.length : ℝ) + 1) w.toSigned := by
  have hcont : ∀ (a b : ℝ) k, ContinuousOn (positiveGridWord w k) (Icc a b) :=
    fun a b k => (positiveGridWord_contDiff w k).continuous.continuousOn
  have hinj : ∀ t ∈ Icc (0 : ℝ) ((w.length : ℝ) + 1),
      Injective fun k => positiveGridWord w k t := fun t _ => positiveGridWord_injective w t
  -- The prefix of length `j ≥ 1`.
  have hprefix : ∀ j, 1 ≤ j → j ≤ w.length →
      IsPathWord (positiveGridWord w) 0 j (PositiveAdjacentWord.toSigned (w.take j)) := by
    intro j hj1 hjl
    induction j with
    | zero => omega
    | succ j ih =>
      have hstage := isPathWord_positiveGridWord_stage w j (by omega)
      have htake : w.take (j + 1) = w.take j ++ [w[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        rfl
      have hword : PositiveAdjacentWord.toSigned (w.take (j + 1)) =
          PositiveAdjacentWord.toSigned (w.take j) ++
            ([(w[j], 1)] : SignedAdjacentWord (n + 1)) := by
        rw [htake]
        simp only [PositiveAdjacentWord.toSigned, List.map_append, List.map_cons, List.map_nil]
      rw [hword]
      push_cast
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        simpa [PositiveAdjacentWord.toSigned] using hstage
      · have hih := ih hpos (by omega)
        exact hih.append (w := (j : ℝ) + 1) (by exact_mod_cast hpos) (by linarith)
          (hcont _ _) (fun t _ => positiveGridWord_injective w t) hstage
  have htail : IsPathWord (positiveGridWord w) w.length ((w.length : ℝ) + 1) [] := by
    refine IsPathWord.const fun k t ht => ?_
    rw [positiveGridWord_of_length_le w k ht.1, positiveGridWord_of_length_le w k le_rfl]
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · have hw : w = [] := List.eq_nil_of_length_eq_zero h0
    subst hw
    simpa [PositiveAdjacentWord.toSigned] using htail
  · have h1 := hprefix w.length hpos le_rfl
    rw [List.take_length] at h1
    simpa using h1.append (by exact_mod_cast hpos) (by linarith) (hcont _ _) hinj htail

/-- **The canonical closed braid of a positive word** `W`, parametrized by `[u, v]`, has path
word `W`. -/
theorem isPathWord_positiveWordModel {n : ℕ} (W : PositiveAdjacentWord (n + 1)) {u v : ℝ}
    (huv : u < v) : IsPathWord (positiveWordModel W u v) u v W.toSigned := by
  have hd : 0 < v - u := sub_pos.mpr huv
  have hL : (0 : ℝ) < (W.length : ℝ) + 1 := by positivity
  refine IsPathWord.comp_affine (K := positiveGridWord W) (φ := positiveWordModelTime W u v)
    (α := ((W.length : ℝ) + 1) / (v - u)) (β := -u * (((W.length : ℝ) + 1) / (v - u)))
    (div_pos hL hd) (fun t => by unfold positiveWordModelTime; field_simp; ring) ?_
  rw [positiveWordModelTime_left, positiveWordModelTime_right W huv]
  exact isPathWord_positiveGridWord W

/-! ### Closed braids represented by positive words -/

/-- A closed braid has a path word. -/
theorem IsClosedStrandBraid.exists_isPathWord {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ}
    {τ : Equiv.Perm (Fin S)} (h : IsClosedStrandBraid K u v τ) : ∃ W, IsPathWord K u v W :=
  OnLeConjecture.Analytic.exists_isPathWord h.lt h.continuousOn h.injective

/-- **Representation gives a finite word relation.** If the closed braid `K` over `[u, v]` is
represented through closed braids by the positive word `W`, every path word of `K` is conjugate
to `W` by a finite signed-word derivation. -/
theorem IsRepresentedByPositiveWord.signedBraidConj {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ}
    {W : PositiveAdjacentWord S} (h : IsRepresentedByPositiveWord K u v W)
    {W' : SignedAdjacentWord S} (hW' : IsPathWord K u v W') :
    SignedBraidConj W' W.toSigned := by
  obtain ⟨π, hiso⟩ := h
  have hleft := hiso.left
  have hinj : ∀ t ∈ Icc u v, Injective fun k => K k t := by
    intro t ht x y hxy
    have := hleft.injective t ht (show K (π (π.symm x)) t = K (π (π.symm y)) t by simpa using hxy)
    simpa using congrArg π this
  have h1 := (IsPathWord.relabel hinj π).mpr hW'
  rcases S with _ | n
  · have : W'.length = 0 ∨ True := Or.inr trivial
    have hW1 : W' = [] := by
      rcases W' with _ | ⟨a, _⟩
      · rfl
      · exact a.1.elim0
    have hW2 : W.toSigned = [] := by
      rcases W with _ | ⟨a, _⟩
      · rfl
      · exact a.elim0
    rw [hW1, hW2]
    exact SignedBraidConj.refl _
  exact hiso.signedBraidConj h1 (isPathWord_positiveWordModel W hleft.lt)

/-- A closed braid represented through closed braids by a positive word `W` has a path word, and
all its path words are conjugate to `W`. -/
theorem IsRepresentedByPositiveWord.exists_isPathWord_signedBraidConj {S : ℕ}
    {K : Fin S → ℝ → ℂ} {u v : ℝ} {W : PositiveAdjacentWord S}
    (h : IsRepresentedByPositiveWord K u v W) :
    ∃ W', IsPathWord K u v W' ∧ SignedBraidConj W' W.toSigned := by
  obtain ⟨π, hiso⟩ := h
  have hleft := hiso.left
  have hinj : ∀ t ∈ Icc u v, Injective fun k => K k t := by
    intro t ht x y hxy
    have := hleft.injective t ht (show K (π (π.symm x)) t = K (π (π.symm y)) t by simpa using hxy)
    simpa using congrArg π this
  have hcont : ∀ k, ContinuousOn (K k) (Icc u v) := by
    intro k
    simpa using hleft.continuousOn (π.symm k)
  obtain ⟨W', hW'⟩ := exists_isPathWord hleft.lt hcont hinj
  exact ⟨W', hW', IsRepresentedByPositiveWord.signedBraidConj ⟨π, hiso⟩ hW'⟩

/-- **The word form of Theorem `J14:thm:transverse-germ`.** For a transverse reduced germ of
multiplicity `S ≥ 1`, there is a positive word `w` with the cycle and length identities of J14
such that, for every sufficiently small radius `r` and every base angle `b`, the root braid
`y r` over the circle `ξ = r^q e^{iθ}`, `θ ∈ [b, b + 2π]`, has a path word, and every path word
of `y r` is conjugate to `d_S w` by a finite signed-word derivation. -/
theorem Germ.exists_transverse_fullTwist_pathWord (H : Source 2 → ℂ)
    (hH : AnalyticAt ℂ H 0) (hsq : Squarefree (ofFunction H hH)) {S : ℕ} (hS : 0 < S)
    (hreg : IsRegularInFirstCoordinateOfOrder (ofFunction H hH) S)
    (hmult : ofFunction H hH ∈ maximalIdeal 2 ^ S) :
    ∃ w : PositiveAdjacentWord S,
      (PositiveAdjacentWord.toSigned w).cycleCount = irreducibleBranchCount (ofFunction H hH) ∧
      (∃ (q : ℕ) (r₀ : ℝ) (y : ℝ → Fin S → ℝ → ℂ), 0 < q ∧ 0 < r₀ ∧
        ∀ r, 0 < r → r < r₀ → (∀ k θ, H ![y r k θ, circlePath (r ^ q) θ] = 0) ∧
          ∀ b : ℝ, (∃ W', IsPathWord (y r) b (b + 2 * Real.pi) W') ∧
            ∀ W', IsPathWord (y r) b (b + 2 * Real.pi) W' →
              SignedBraidConj W' (fullTwistWord S ++ w).toSigned) ∧
      (fullTwistWord S ++ w).length + 1 =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) + S ∧
      w.length + S ^ 2 + irreducibleBranchCount (ofFunction H hH) =
        2 * deltaInvariant (ofFunction H hH) + 2 * S := by
  obtain ⟨w, hcyc, ⟨q, r₀, y, hq, hr₀, hy⟩, hlen, hlen'⟩ :=
    Germ.exists_transverse_fullTwist_word_length H hH hsq hS hreg hmult
  refine ⟨w, hcyc, ⟨q, r₀, y, hq, hr₀, fun r hr hrr => ⟨(hy r hr hrr).1, fun b => ?_⟩⟩,
    hlen, hlen'⟩
  have hrep := (hy r hr hrr).2 b
  obtain ⟨W', hW', -⟩ := hrep.exists_isPathWord_signedBraidConj
  exact ⟨⟨W', hW'⟩, fun W'' hW'' => hrep.signedBraidConj hW''⟩

end OnLeConjecture.Analytic
