/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BraidMonodromyPathWord

/-!
# Path words of a single exchange

Let `K` be a strand family on `[u, v]`, continuous with pairwise distinct points, whose
lexicographic order (`configSort`) is `π` before a time `c` and `π σ_i` after it, where `σ_i`
exchanges the positions `i` and `i + 1`. At the time `c` the two exchanged strands have equal
real parts.

* `IsPathWord.of_positive_exchange`: if the order `π` holds up to and including `c`, the path
  word is the positive letter `σ_i`. At the time `c` the lexicographic order then places the
  lower strand first, so the strand moving to the left is the higher one.
* `IsPathWord.of_negative_exchange`: if the order `π σ_i` holds from `c` on, the path word is
  the negative letter `σ_i⁻¹`.

These are the elementary positive and negative crossings of the event words of Section 3 of the
written proof of Statement E. The sign convention agrees with the projected crossings of the
project: a crossing is positive when the strand moving to the left has the larger imaginary
part.
-/

@[expose] public noncomputable section

open Set Function

namespace OnLeConjecture.Analytic

open KnotTheory

/-- At the time of an exchange of two adjacent strands whose new order holds from the time
`c` on, the real parts agree and the strand moving to the left is the lower one. -/
theorem exchange_heights_of_negative {n : ℕ} {K : Fin (n + 1) → ℝ → ℂ} {u v c : ℝ}
    (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (hc : u < c) (hcv : c ≤ v)
    {π : Equiv.Perm (Fin (n + 1))} {i : Fin n}
    (hbefore : ∀ t ∈ Icc u v, t < c → configSort (fun k => K k t) = π)
    (hafter : configSort (fun k => K k c) = π * adjacentSwap (m := n + 1) i) :
    (K (π (adjacentLower (m := n + 1) i)) c).re = (K (π (adjacentUpper (m := n + 1) i)) c).re ∧
      (K (π (adjacentUpper (m := n + 1) i)) c).im <
        (K (π (adjacentLower (m := n + 1) i)) c).im := by
  set lo := π (adjacentLower (m := n + 1) i)
  set up := π (adjacentUpper (m := n + 1) i)
  have hcI : c ∈ Icc u v := ⟨hc.le, hcv⟩
  have hlex : lexKey (K up c) < lexKey (K lo c) := by
    apply (configSort_symm_lt_iff (hinj c hcI) up lo).mp
    rw [hafter]
    simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, adjacentSwap_symm, lo, up,
      Equiv.symm_apply_apply]
    rw [Fin.lt_def, adjacentSwap_apply_val, adjacentSwap_apply_val]
    simp
  have hre1 := re_le_of_lexKey_lt hlex
  have hre2 : (K lo c).re ≤ (K up c).re := by
    by_contra hlt
    simp only [not_le] at hlt
    have hf : ContinuousOn (fun t => (K lo t - K up t).re) (Icc u v) :=
      Complex.continuous_re.comp_continuousOn ((hcont lo).sub (hcont up))
    have hpos : 0 < (K lo c - K up c).re := by simp only [Complex.sub_re]; linarith
    obtain ⟨η, hη, hηf⟩ := Metric.continuousOn_iff.mp hf c hcI _ hpos
    set t := max u (c - η / 2) with ht
    have htI : t ∈ Icc u v := ⟨le_max_left _ _, max_le (hc.le.trans hcv) (by linarith)⟩
    have htc : t < c := max_lt hc (by linarith)
    have hdist : dist t c < η := by
      have h1 : c - η / 2 ≤ t := le_max_right _ _
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      linarith
    have h1 := hηf t htI hdist
    rw [Real.dist_eq] at h1
    have h2 : 0 < (K lo t - K up t).re := by
      have := abs_lt.mp h1
      linarith [this.1]
    have hlex' : lexKey (K up t) < lexKey (K lo t) := by
      rw [lexKey_lt_iff]
      left
      simp only [Complex.sub_re] at h2
      linarith
    have := (configSort_symm_lt_iff (hinj t htI) up lo).mpr hlex'
    rw [hbefore t htI htc] at this
    simp only [lo, up, Equiv.symm_apply_apply, Fin.lt_def] at this
    simp at this
  have hre : (K lo c).re = (K up c).re := le_antisymm hre2 hre1
  refine ⟨hre, ?_⟩
  rcases (lexKey_lt_iff _ _).mp hlex with h | h
  · exact absurd hre.symm h.ne
  · exact h.2

/-- The imaginary parts of two strands of a separated configuration with equal real parts are
at least the separation apart. -/
theorem le_im_sub_of_re_eq {m : ℝ} {a b : ℂ} (hsep : m ≤ ‖a - b‖) (hre : a.re = b.re)
    (him : a.im < b.im) : m ≤ b.im - a.im := by
  have h := Complex.norm_le_abs_re_add_abs_im (a - b)
  simp only [Complex.sub_re, Complex.sub_im, hre, sub_self, abs_zero, zero_add] at h
  rw [abs_of_neg (by linarith)] at h
  linarith

/-- **A positive exchange.** If the lexicographic order of `K` is `π` up to and including the
time `c` and `π σ_i` after `c`, then the path word of `K` on `[u, v]` is the positive letter
`σ_i`. -/
theorem IsPathWord.of_positive_exchange {n : ℕ} {K : Fin (n + 1) → ℝ → ℂ} {u v c : ℝ}
    (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (hc : u ≤ c) (hcv : c < v)
    {π : Equiv.Perm (Fin (n + 1))} {i : Fin n}
    (hbefore : ∀ t ∈ Icc u v, t ≤ c → configSort (fun k => K k t) = π)
    (hafter : ∀ t ∈ Icc u v, c < t →
      configSort (fun k => K k t) = π * adjacentSwap (m := n + 1) i) :
    IsPathWord K u v ([(i, 1)] : SignedAdjacentWord (n + 1)) := by
  obtain ⟨m, δ, hK⟩ := exists_pathModulus hcont hinj
  have hcI : c ∈ Icc u v := ⟨hc, hcv.le⟩
  obtain ⟨hre, him⟩ := exchange_heights_of_positive hcont hinj hc hcv
    (hbefore c hcI le_rfl) hafter
  set lo := π (adjacentLower (m := n + 1) i)
  set up := π (adjacentUpper (m := n + 1) i)
  have hgapc := le_im_sub_of_re_eq (hK.sep c hcI lo up (by
    simp [lo, up, Fin.ext_iff])) hre him
  refine ⟨δ / 2, half_pos hK.delta_pos, fun t N P => ?_⟩
  have key : ∀ a ≤ N, SignedBraidEquiv (chainWord (fun a k => K k (t a)) a)
      (if t a ≤ c then [] else ([(i, 1)] : SignedAdjacentWord (n + 1))) := by
    intro a
    induction a with
    | zero =>
      intro _
      rw [if_pos (P.zero ▸ hc)]
      exact SignedBraidEquiv.refl _
    | succ a ih =>
      intro ha
      have hstep := P.step a (by omega)
      have hgap := P.gap a (by omega)
      have hta := P.mem_Icc (a := a) (by omega)
      have hta1 := P.mem_Icc ha
      rw [chainWord_succ]
      by_cases h1 : t (a + 1) ≤ c
      · have h0 : t a ≤ c := hstep.le.trans h1
        rw [if_pos h1]
        have hl := localWord_of_configSort_eq (fun k => K k (t a))
          ((hbefore _ hta h0).trans (hbefore _ hta1 h1).symm)
        simpa [if_pos h0] using (ih (by omega)).append hl
      · rw [if_neg h1]
        by_cases h0 : t a ≤ c
        · -- The crossing step.
          rw [if_pos h0] at ih
          have hswap : configSort (fun k => K k (t (a + 1))) =
              configSort (fun k => K k (t a)) * adjacentSwap (m := n + 1) i := by
            rw [hbefore _ hta h0, hafter _ hta1 (lt_of_not_ge h1)]
          have hl := localWord_of_configSort_swap (hinj _ hta) i hswap
          rw [hbefore _ hta h0] at hl
          have hsign : exchangeSign (heightKey (K lo (t a))) (heightKey (K up (t a))) = 1 := by
            rw [exchangeSign, if_pos]
            rw [heightKey_lt_iff]
            left
            have hnear := hK.near (t a) hta c hcI (by
              rw [abs_lt]; constructor <;> linarith [lt_of_not_ge h1])
            have e1 := (Complex.abs_im_le_norm _).trans_lt (hnear lo)
            have e2 := (Complex.abs_im_le_norm _).trans_lt (hnear up)
            simp only [Complex.sub_im] at e1 e2
            rw [abs_lt] at e1 e2
            linarith [e1.1, e1.2, e2.1, e2.2, hK.pos]
          simp only [lo, up] at hsign
          rw [hsign] at hl
          simpa using ih (by omega) |>.append hl
        · rw [if_neg h0] at ih
          have hl := localWord_of_configSort_eq (fun k => K k (t a))
            ((hafter _ hta (lt_of_not_ge h0)).trans (hafter _ hta1 (lt_of_not_ge h1)).symm)
          simpa using (ih (by omega)).append hl
  have h := key N le_rfl
  rwa [if_neg (by rw [P.last]; exact not_le.mpr hcv)] at h

/-- **A negative exchange.** If the lexicographic order of `K` is `π` before the time `c` and
`π σ_i` from `c` on, then the path word of `K` on `[u, v]` is the negative letter `σ_i⁻¹`. -/
theorem IsPathWord.of_negative_exchange {n : ℕ} {K : Fin (n + 1) → ℝ → ℂ} {u v c : ℝ}
    (hcont : ∀ k, ContinuousOn (K k) (Icc u v))
    (hinj : ∀ t ∈ Icc u v, Injective fun k => K k t) (hc : u < c) (hcv : c ≤ v)
    {π : Equiv.Perm (Fin (n + 1))} {i : Fin n}
    (hbefore : ∀ t ∈ Icc u v, t < c → configSort (fun k => K k t) = π)
    (hafter : ∀ t ∈ Icc u v, c ≤ t →
      configSort (fun k => K k t) = π * adjacentSwap (m := n + 1) i) :
    IsPathWord K u v ([(i, -1)] : SignedAdjacentWord (n + 1)) := by
  obtain ⟨m, δ, hK⟩ := exists_pathModulus hcont hinj
  have hcI : c ∈ Icc u v := ⟨hc.le, hcv⟩
  obtain ⟨hre, him⟩ := exchange_heights_of_negative hcont hinj hc hcv hbefore
    (hafter c hcI le_rfl)
  set lo := π (adjacentLower (m := n + 1) i)
  set up := π (adjacentUpper (m := n + 1) i)
  have hgapc := le_im_sub_of_re_eq (hK.sep c hcI up lo (by
    simp [lo, up, Fin.ext_iff])) hre.symm him
  refine ⟨δ / 2, half_pos hK.delta_pos, fun t N P => ?_⟩
  have key : ∀ a ≤ N, SignedBraidEquiv (chainWord (fun a k => K k (t a)) a)
      (if t a < c then [] else ([(i, -1)] : SignedAdjacentWord (n + 1))) := by
    intro a
    induction a with
    | zero =>
      intro _
      rw [if_pos (P.zero ▸ hc)]
      exact SignedBraidEquiv.refl _
    | succ a ih =>
      intro ha
      have hstep := P.step a (by omega)
      have hgap := P.gap a (by omega)
      have hta := P.mem_Icc (a := a) (by omega)
      have hta1 := P.mem_Icc ha
      rw [chainWord_succ]
      by_cases h1 : t (a + 1) < c
      · have h0 : t a < c := hstep.trans h1
        rw [if_pos h1]
        have hl := localWord_of_configSort_eq (fun k => K k (t a))
          ((hbefore _ hta h0).trans (hbefore _ hta1 h1).symm)
        simpa [if_pos h0] using (ih (by omega)).append hl
      · rw [if_neg h1]
        by_cases h0 : t a < c
        · rw [if_pos h0] at ih
          have hswap : configSort (fun k => K k (t (a + 1))) =
              configSort (fun k => K k (t a)) * adjacentSwap (m := n + 1) i := by
            rw [hbefore _ hta h0, hafter _ hta1 (not_lt.mp h1)]
          have hl := localWord_of_configSort_swap (hinj _ hta) i hswap
          rw [hbefore _ hta h0] at hl
          have hsign : exchangeSign (heightKey (K lo (t a))) (heightKey (K up (t a))) = -1 := by
            rw [exchangeSign, if_neg]
            rw [heightKey_lt_iff]
            have hnear := hK.near (t a) hta c hcI (by
              rw [abs_lt]; constructor <;> linarith [not_lt.mp h1])
            have e1 := (Complex.abs_im_le_norm _).trans_lt (hnear lo)
            have e2 := (Complex.abs_im_le_norm _).trans_lt (hnear up)
            simp only [Complex.sub_im] at e1 e2
            rw [abs_lt] at e1 e2
            have : (K up (t a)).im < (K lo (t a)).im := by
              linarith [e1.1, e1.2, e2.1, e2.2, hK.pos]
            rintro (h | ⟨h, -⟩) <;> linarith
          simp only [lo, up] at hsign
          rw [hsign] at hl
          simpa using ih (by omega) |>.append hl
        · rw [if_neg h0] at ih
          have hl := localWord_of_configSort_eq (fun k => K k (t a))
            ((hafter _ hta (not_lt.mp h0)).trans (hafter _ hta1 (not_lt.mp h1)).symm)
          simpa using (ih (by omega)).append hl
  have h := key N le_rfl
  rwa [if_neg (by rw [P.last]; exact not_lt.mpr hcv)] at h

end OnLeConjecture.Analytic
