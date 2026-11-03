/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicReducedNormCoefficients

/-!
# An off-axis root of the reduced cyclic norm

Polynomial degree and root multiplicities give the required root. The
proof constructs a divisibility contradiction and uses no projective
intersection theorem.
-/

public section

namespace OnLeConjecture.DTwo

open _root_.Polynomial

/-- A polynomial supported at zero and the common roots of two unity
equations has bounded degree when the local multiplicities are bounded. -/
theorem natDegree_le_of_cyclic_boundary_roots
    (P : Polynomial ℂ) (hP : P ≠ 0) (k N q : ℕ) (hk : 0 < k)
    (hzero : P.rootMultiplicity 0 ≤ N)
    (hboundary : ∀ z : ℂ, P.IsRoot z → z ≠ 0 → z ^ k = 1 ∧ z ^ N = 1)
    (horder : ∀ z : ℂ, P.IsRoot z → z ^ k = 1 → P.rootMultiplicity z ≤ q) :
    P.natDegree ≤ N + q * Nat.gcd k N := by
  let δ := Nat.gcd k N
  have hδ : 0 < δ := Nat.gcd_pos_of_pos_left N hk
  let B : Polynomial ℂ := X ^ δ - 1
  have hB : B ≠ 0 := by
    intro h
    have heval := congrArg (fun Q : Polynomial ℂ ↦ Q.eval 0) h
    simp [B, zero_pow hδ.ne'] at heval
  let Q : Polynomial ℂ := X ^ N * B ^ q
  have hQ : Q ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hB)
  have hQzero : Q.rootMultiplicity 0 = N := by
    have hX : (X ^ N : Polynomial ℂ).rootMultiplicity 0 = N := by
      simpa using rootMultiplicity_X_sub_C_pow (0 : ℂ) N
    have hBzero : B.rootMultiplicity 0 = 0 :=
      rootMultiplicity_eq_zero (by simp [B, IsRoot.def, zero_pow hδ.ne'])
    rw [rootMultiplicity_mul hQ, hX,
      OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul B hB, hBzero, mul_zero, add_zero]
  have hdiv : P ∣ Q := by
    apply (IsAlgClosed.splits P).dvd_of_roots_le_roots hP
    rw [Multiset.le_iff_count]
    intro z
    rw [count_roots, count_roots]
    by_cases hroot : P.IsRoot z
    · by_cases hz : z = 0
      · simpa only [hz, hQzero] using hzero
      obtain ⟨hkz, hNz⟩ := hboundary z hroot hz
      have hδz : z ^ δ = 1 := pow_gcd_eq_one.mpr ⟨hkz, hNz⟩
      have hBroot : B.IsRoot z := by simp [B, IsRoot.def, hδz]
      have hBpos : 1 ≤ B.rootMultiplicity z :=
        (_root_.Polynomial.rootMultiplicity_pos hB).mpr hBroot
      have hQorder : q ≤ Q.rootMultiplicity z := by
        rw [rootMultiplicity_mul hQ,
          OnLeConjecture.Polynomial.rootMultiplicity_pow_eq_mul B hB]
        nlinarith
      exact (horder z hroot hkz).trans hQorder
    · rw [rootMultiplicity_eq_zero hroot]
      exact Nat.zero_le _
  have hdegree := natDegree_le_of_dvd hdiv hQ
  have hQdegree : Q.natDegree = N + q * δ := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hB), natDegree_X_pow,
      natDegree_pow]
    have hBdegree : B.natDegree = δ := by
      simpa only [B, map_one] using (natDegree_X_pow_sub_C (n := δ) (r := (1 : ℂ)))
    rw [hBdegree]
  simpa only [hQdegree] using hdegree

@[expose] noncomputable def cyclicReducedNorm
    (k N q r : ℕ) (c a : ℂ) (A : Polynomial ℂ) : Polynomial ℂ :=
  cyclicMixedPlanePolynomial k c ^ r * (expand ℂ k A) ^ q + C a * (1 - X ^ N) ^ q

theorem cyclicReducedNorm_expanded_form
    (k N q r : ℕ) (c a : ℂ) (A : Polynomial ℂ) :
    cyclicReducedNorm k N q r c a A =
      expand ℂ k ((C (c / 2) * (X - 1)) ^ r * A ^ q) + C a * (1 - X ^ N) ^ q := by
  simp only [cyclicReducedNorm, map_mul, map_pow, map_sub, map_one, expand_C, expand_X,
    cyclicMixedPlanePolynomial]

/-- Every boundary root lies at a common root of the two unity equations. -/
theorem cyclicReducedNorm_boundary_root
    (k N q r : ℕ) (_hq : 0 < q) (hr : 0 < r) (c a z : ℂ) (ha : a ≠ 0)
    (A : Polynomial ℂ) (hz : z ^ k = 1)
    (hroot : (cyclicReducedNorm k N q r c a A).IsRoot z) : z ^ N = 1 := by
  have hzero : a * (1 - z ^ N) ^ q = 0 := by
    simpa [cyclicReducedNorm, IsRoot.def, cyclicMixedPlanePolynomial_eval, hz,
      zero_pow hr.ne'] using hroot
  have hpower : (1 - z ^ N) ^ q = 0 := (mul_eq_zero.mp hzero).resolve_left ha
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpower)).symm

/-- Root multiplicities on `Yᵏ = 1` are at most `q`. -/
theorem cyclicReducedNorm_boundary_order
    (k N q r : ℕ) (hk : 0 < k) (hN : 0 < N) (hq : 0 < q) (hnot : ¬ q ∣ r)
    (c a z : ℂ) (hc : c ≠ 0) (ha : a ≠ 0) (A : Polynomial ℂ)
    (hz : z ^ k = 1) (hroot : (cyclicReducedNorm k N q r c a A).IsRoot z) :
    (cyclicReducedNorm k N q r c a A).rootMultiplicity z ≤ q := by
  have hr : 0 < r := by by_contra h; exact hnot (by simp [show r = 0 by omega])
  have hznonzero : z ≠ 0 := by intro h; simp [h, zero_pow hk.ne'] at hz
  have hzN := cyclicReducedNorm_boundary_root k N q r hq hr c a z ha A hz hroot
  have hG := cyclicMixedPlanePolynomial_rootMultiplicity k hk c z hc hznonzero hz
  have hGzero : cyclicMixedPlanePolynomial k c ≠ 0 := by intro h; simp [h] at hG
  have hT : ((1 : Polynomial ℂ) - X ^ N).rootMultiplicity z = 1 := by
    have heq : (1 : Polynomial ℂ) - X ^ N = cyclicMixedPlanePolynomial N (-2) := by
      simp [cyclicMixedPlanePolynomial]
    rw [heq]
    exact cyclicMixedPlanePolynomial_rootMultiplicity N hN (-2) z
      (by norm_num) hznonzero hzN
  have hTzero : (1 : Polynomial ℂ) - X ^ N ≠ 0 := by intro h; simp [h] at hT
  exact rootMultiplicity_reduced_power_sum_le (cyclicMixedPlanePolynomial k c)
    (expand ℂ k A) (1 - X ^ N) q r hq hnot a z ha hGzero hG hTzero hT

/-- The reduced norm has a root off `Y = 0` and `Yᵏ = 1`. All degree and
boundary multiplicity estimates follow from its displayed polynomial. -/
theorem cyclicReducedNorm_has_off_axis_root
    (k N q r : ℕ) (hk : 0 < k) (hN : k < N) (hq : 3 ≤ q)
    (hnot : ¬ k ∣ N) (hdiv : k ∣ q * N) (hgcd : q * Nat.gcd k N = k)
    (hr : ¬ q ∣ r) (c a : ℂ) (hc : c ≠ 0) (ha : a ≠ 0) (A : Polynomial ℂ) :
    ∃ z : ℂ, (cyclicReducedNorm k N q r c a A).IsRoot z ∧ z ≠ 0 ∧ z ^ k ≠ 1 := by
  let P := cyclicReducedNorm k N q r c a A
  have hform := cyclicReducedNorm_expanded_form k N q r c a A
  obtain ⟨hP, hdegree, hzero⟩ := cyclicNorm_degree_and_zero_order k N q hk (by omega)
    (by omega) hnot hdiv ((C (c / 2) * (X - 1)) ^ r * A ^ q) a ha
  rw [← hform] at hP hdegree hzero
  by_contra h
  push Not at h
  have hboundary : ∀ z : ℂ, P.IsRoot z → z ≠ 0 → z ^ k = 1 ∧ z ^ N = 1 := by
    intro z hz hznonzero
    have hzk := h z hz hznonzero
    refine ⟨hzk, cyclicReducedNorm_boundary_root k N q r (by omega) ?_ c a z ha A hzk hz⟩
    by_contra hzeroR
    exact hr (by simp [show r = 0 by omega])
  have hupper := natDegree_le_of_cyclic_boundary_roots P hP k N q hk hzero hboundary
    (fun z hz hzk ↦ cyclicReducedNorm_boundary_order k N q r hk (by omega) (by omega)
      hr c a z hc ha A hzk hz)
  rw [hgcd] at hupper
  change (cyclicReducedNorm k N q r c a A).natDegree ≤ N + k at hupper
  have hthree : 2 * N ≤ (q - 1) * N := Nat.mul_le_mul_right N (by omega)
  omega

end OnLeConjecture.DTwo
