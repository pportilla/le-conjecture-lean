/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidStrictWord
public import OnLeConjecture.Analytic.MultiSheetBraidFullTwist

/-!
# Full-twist factorization of the root braid of finitely many sheets

This module proves the word-level content of Theorem `J14:thm:factorization` of the written
proof for sheet data `D : MultiSheetData S`: there is a fibre rotation `c ≠ 0` and, for every
reference radius, a positive word `v`, the positive event word of the strict-transform braid
read through `Re (c ·)`, such that at every sufficiently small radius and every base angle

* the strict-transform braid is represented by `v`;
* the root braid `θ ↦ (r e^{iθ/q})^q U_k(r e^{iθ/q})` is represented, through closed braids,
  by `fullTwistWord S ++ v`;
* the permutations of `v` and of `fullTwistWord S ++ v` have as many cycles as the
  monodromy `τ`;
* at every regular base angle, the root braid has projected crossing data, all of whose
  crossings are positive, with signed crossing count equal to the exponent sum (the length)
  of `fullTwistWord S ++ v`.

"Represented through closed braids" is the predicate `IsRepresentedByPositiveWord`: after a
relabelling of the strands, isotopy through closed braids with the canonical closed braid of
the word.
-/

@[expose] public noncomputable section

open Set Filter Metric Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

theorem IsRepresentedByPositiveWord.congr_fun {S : ℕ} {K K' : Fin S → ℝ → ℂ} {u v : ℝ}
    {W : PositiveAdjacentWord S} (h : IsRepresentedByPositiveWord K u v W) (he : K' = K) :
    IsRepresentedByPositiveWord K' u v W := he ▸ h

namespace MultiSheetData

variable {S : ℕ} (D : MultiSheetData S)

/-- The root braid is represented by the full twist followed by any word representing the
strict-transform braid. -/
theorem root_isRepresented {c : ℂ} (hc : c ≠ 0) {r : ℝ} (hr : 0 < r) {b : ℝ}
    {v : PositiveAdjacentWord S} (hcl : IsClosedStrandBraid (D.strict c r) b (b + 2 * π) D.τ)
    (hrep : IsRepresentedByPositiveWord (D.strict c r) b (b + 2 * π) v) :
    IsRepresentedByPositiveWord (D.root 1 r) b (b + 2 * π) (fullTwistWord S ++ v) := by
  have hρ : 0 < r ^ D.q := pow_pos hr D.q
  have hroot := hrep.circlePath_mul hρ
  have hrootc : (fun k θ => circlePath (r ^ D.q) θ * D.strict c r k θ) = D.root c r :=
    funext fun k => funext fun θ => (D.root_eq c r k θ).symm
  rw [hrootc] at hroot
  have hg0 : ∀ θ ∈ Icc b (b + 2 * π), circlePath (r ^ D.q) θ ≠ 0 := by
    intro θ _
    apply norm_pos_iff.mp
    rw [norm_circlePath hρ.le]
    exact hρ
  have hclroot : IsClosedStrandBraid (D.root c r) b (b + 2 * π) D.τ := by
    have h := hcl.mul_left (continuous_circlePath _).continuousOn hg0
      (circlePath_add_two_pi _ b)
    rwa [hrootc] at h
  have h1 := hroot.const_mul hclroot (inv_ne_zero hc)
  refine h1.congr_fun (funext fun k => funext fun θ => ?_)
  rw [root, root, multiSheetStrands_eq_mul c D.rootSheet D.q r k θ, ← mul_assoc,
    inv_mul_cancel₀ hc, one_mul]

/-- **Full-twist factorization for sheet data** (word-level content of Theorem
`J14:thm:factorization` and Corollary `J14:cor:cycles`). -/
theorem exists_fullTwist_factorization {c : ℂ} (hc : c ≠ 0)
    (hproj : ∀ k l, D.U k 0 ≠ D.U l 0 → (c * (D.U k 0 - D.U l 0)).re ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ D.R ∧
      (∀ r, 0 < r → r < r₀ → IsPeriodicStrandBraid (D.strict c r) D.τ ∧
        IsPeriodicStrandBraid (D.root 1 r) D.τ ∧
        ∀ θ k l, k ≠ l → (D.strict c r k θ).re = (D.strict c r l θ).re →
          0 < -deriv (fun t => (D.strict c r k t - D.strict c r l t).re) θ *
            (D.strict c r k θ - D.strict c r l θ).im) ∧
      (∀ r, 0 < r → r < r₀ → ∀ u v : ℝ,
        {θ | θ ∈ Icc u v ∧ ∃ k l, k ≠ l ∧ (D.strict c r k θ).re = (D.strict c r l θ).re}.Finite ∧
        {θ | θ ∈ Icc u v ∧ ∃ k l, k ≠ l ∧ (D.root c r k θ).re = (D.root c r l θ).re}.Finite) ∧
      ∀ r₁, 0 < r₁ → r₁ < r₀ →
        ∃ (b₁ : ℝ) (E : Finset ℝ) (N : ℕ) (event left right : Fin N → ℝ)
          (σ : Fin (N + 1) → Equiv.Perm (Fin S)) (w : Fin N → PositiveAdjacentWord S),
          (∀ t, t ∈ E ↔ t ∈ Icc b₁ (b₁ + 2 * π) ∧
            ∃ k l : Fin S, k ≠ l ∧ (D.strict c r₁ k t).re = (D.strict c r₁ l t).re) ∧
          b₁ ∉ E ∧ b₁ + 2 * π ∉ E ∧
          N = E.card ∧ List.ofFn event = E.sort (· ≤ ·) ∧ StrictMono event ∧
          (∀ j : Fin N,
            b₁ < left j ∧ left j < event j ∧ event j < right j ∧ right j < b₁ + 2 * π ∧
            StrictMono (fun k => (D.strict c r₁ (σ j.castSucc k) (left j)).re) ∧
            StrictMono (fun k => (D.strict c r₁ (σ j.succ k) (right j)).re) ∧
            (∀ t ∈ Icc (left j) (right j), t ∈ E ↔ t = event j) ∧
            IsPositiveBraidEventWord (D.strict c r₁) (event j) (σ j.castSucc) (σ j.succ) (w j)) ∧
          (∀ j q, j < q → right j < left q) ∧
          (σ (Fin.last N)).trans D.τ = σ 0 ∧
          σ 0 * (PositiveAdjacentWord.toSigned ((List.ofFn w).flatten)).permutation =
            σ (Fin.last N) ∧
          (∀ r, 0 < r → r < r₀ → ∀ b : ℝ,
            IsRepresentedByPositiveWord (D.strict c r) b (b + 2 * π) (List.ofFn w).flatten ∧
            IsRepresentedByPositiveWord (D.root 1 r) b (b + 2 * π)
              (fullTwistWord S ++ (List.ofFn w).flatten)) ∧
          (PositiveAdjacentWord.toSigned (List.ofFn w).flatten).cycleCount =
            permCycleCount D.τ ∧
          (PositiveAdjacentWord.toSigned (fullTwistWord S ++ (List.ofFn w).flatten)).cycleCount =
            permCycleCount D.τ ∧
          ∀ r, 0 < r → r < r₀ → ∀ b : ℝ,
            (∀ k l, k ≠ l → (D.root c r k b).re ≠ (D.root c r l b).re) →
            ∃ Dy : SheetCrossingData S (D.root 1 r) b c,
              (∀ k l, k < l → ∀ θ ∈ Dy.crossings k l, Dy.crossingSign k l θ = 1) ∧
              Dy.signedCount = SignedAdjacentWord.exponentSum
                (PositiveAdjacentWord.toSigned (fullTwistWord S ++ (List.ofFn w).flatten)) := by
  obtain ⟨r₀, hr₀, hr₀R, hper, hfin, hall⟩ := D.exists_strict_event_word hc hproj
  refine ⟨r₀, hr₀, hr₀R, hper, hfin, fun r₁ hr₁ hr₁r => ?_⟩
  obtain ⟨b₁, E, N, event, left, right, σ, w, hE, hbE, hdE, hN, henum, hmono, hblocks, hsep,
    hσ, hperm, hrep, hcyc, hcross⟩ := hall r₁ hr₁ hr₁r
  refine ⟨b₁, E, N, event, left, right, σ, w, hE, hbE, hdE, hN, henum, hmono, hblocks, hsep,
    hσ, hperm, fun r hr hrr b => ⟨hrep r hr hrr b, D.root_isRepresented hc hr
      ((hper r hr hrr).1.isClosedStrandBraid b) (hrep r hr hrr b)⟩, hcyc, ?_, hcross⟩
  rw [SignedAdjacentWord.cycleCount_eq_permCycleCount] at hcyc ⊢
  change permCycleCount (PositiveAdjacentWord.permutation (fullTwistWord S ++ _)) = _
  rw [fullTwist_append_permutation]
  exact hcyc

end MultiSheetData

end OnLeConjecture.Analytic
