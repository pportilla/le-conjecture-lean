/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MultiSheetBraidEventRepresentation
public import OnLeConjecture.Analytic.DiscriminantBraidExponentPairs

/-!
# Crossing counts of closed braids and the winding of the strand discriminant

For labelled strands `K`, the *strand discriminant* is the product
`∏_{k ≠ l} (K_k - K_l)` over ordered pairs of distinct labels. For a closed braid it is
a closed nonvanishing loop, because the monodromy permutes the ordered pairs. Its winding
number is invariant under isotopy through closed braids.

For projected crossing data `SheetCrossingData` of the J15 module
`DiscriminantBraidExponentPairs`, the signed crossing count equals this winding number.
A positive event word has length equal to the signed crossing count when all crossings
are positive. This module also constructs `SheetCrossingData` from finitely many
transverse crossings.

These statements connect the event words of job J14 to the exponent identities of
job J15.
-/

@[expose] public noncomputable section

open Set Filter Real
open scoped Topology BigOperators

namespace OnLeConjecture.Analytic

open KnotTheory

/-! ### The strand discriminant -/

/-- The product of the differences of all ordered pairs of distinct strands. -/
def strandDiscriminant {S : ℕ} (K : Fin S → ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∏ p ∈ (Finset.univ : Finset (Fin S × Fin S)).filter (fun p => p.1 ≠ p.2),
    (K p.1 θ - K p.2 θ)

theorem prod_offDiag_relabel {S : ℕ} (z : Fin S → ℂ) (τ : Equiv.Perm (Fin S)) :
    ∏ p ∈ (Finset.univ : Finset (Fin S × Fin S)).filter (fun p => p.1 ≠ p.2),
        (z (τ p.1) - z (τ p.2)) =
      ∏ p ∈ (Finset.univ : Finset (Fin S × Fin S)).filter (fun p => p.1 ≠ p.2),
        (z p.1 - z p.2) := by
  classical
  rw [Finset.prod_filter, Finset.prod_filter]
  exact Fintype.prod_equiv (Equiv.prodCongr τ τ) _ _ (fun p => by
    simp [τ.injective.ne_iff])

namespace IsClosedStrandBraid

variable {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ} {τ : Equiv.Perm (Fin S)}

theorem strandDiscriminant_closing (h : IsClosedStrandBraid K u v τ) :
    strandDiscriminant K u = strandDiscriminant K v := by
  unfold strandDiscriminant
  simp only [h.closing]
  exact (prod_offDiag_relabel (fun k => K k u) τ).symm

theorem strandDiscriminant_ne_zero (h : IsClosedStrandBraid K u v τ) :
    ∀ t ∈ Icc u v, strandDiscriminant K t ≠ 0 := by
  intro t ht
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact sub_ne_zero.mpr fun he => (Finset.mem_filter.mp hp).2 (h.injective t ht he)

theorem strandDiscriminant_continuousOn (h : IsClosedStrandBraid K u v τ) :
    ContinuousOn (strandDiscriminant K) (Icc u v) := by
  unfold strandDiscriminant
  exact continuousOn_finsetProd _ fun p _ => (h.continuousOn p.1).sub (h.continuousOn p.2)

end IsClosedStrandBraid

/-- The winding number of the strand discriminant is invariant under isotopy through
closed braids. -/
theorem ClosedStrandBraidIsotopic.windingNumber_strandDiscriminant_eq {S : ℕ}
    {K₀ K₁ : Fin S → ℝ → ℂ} {u v : ℝ} {τ : Equiv.Perm (Fin S)}
    (h : ClosedStrandBraidIsotopic K₀ K₁ u v τ) :
    windingNumber (strandDiscriminant K₀) u v = windingNumber (strandDiscriminant K₁) u v := by
  have h₀ := h.left
  have h₁ := h.right
  obtain ⟨H, hH, hH0, hH1⟩ := h
  have huv := hH.lt.le
  have hloop : ∀ s ∈ Icc (0 : ℝ) 1, strandDiscriminant (H s) u = strandDiscriminant (H s) v :=
    fun s hs => (hH.slice hs).strandDiscriminant_closing
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc u v, strandDiscriminant (H s) t ≠ 0 :=
    fun s hs => (hH.slice hs).strandDiscriminant_ne_zero
  have hcont : ContinuousOn (fun p : ℝ × ℝ => strandDiscriminant (H p.1) p.2)
      (Icc 0 1 ×ˢ Icc u v) := by
    unfold strandDiscriminant
    exact continuousOn_finsetProd _ fun p _ => (hH.continuousOn p.1).sub (hH.continuousOn p.2)
  have hw := windingNumber_eq_of_homotopy huv hcont hne hloop
  have e0 : windingNumber (strandDiscriminant K₀) u v =
      windingNumber (strandDiscriminant (H 0)) u v := by
    refine windingNumber_congr huv
      (hH.slice (left_mem_Icc.mpr zero_le_one)).strandDiscriminant_continuousOn
      (hne 0 (left_mem_Icc.mpr zero_le_one)) fun t ht => ?_
    unfold strandDiscriminant
    exact Finset.prod_congr rfl fun p _ => by rw [hH0 p.1 t ht, hH0 p.2 t ht]
  have e1 : windingNumber (strandDiscriminant K₁) u v =
      windingNumber (strandDiscriminant (H 1)) u v := by
    refine windingNumber_congr huv
      (hH.slice (right_mem_Icc.mpr zero_le_one)).strandDiscriminant_continuousOn
      (hne 1 (right_mem_Icc.mpr zero_le_one)) fun t ht => ?_
    unfold strandDiscriminant
    exact Finset.prod_congr rfl fun p _ => by rw [hH1 p.1 t ht, hH1 p.2 t ht]
  rw [e0, e1]
  exact hw

/-- Multiplying all strands by a common nonvanishing closed loop with winding number `n`
adds `S (S - 1) n` to the winding number of the strand discriminant. -/
theorem windingNumber_strandDiscriminant_mul_left {S : ℕ} {K : Fin S → ℝ → ℂ} {u v : ℝ}
    {τ : Equiv.Perm (Fin S)} (hK : IsClosedStrandBraid K u v τ) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc u v)) (hg0 : ∀ t ∈ Icc u v, g t ≠ 0) (hgl : g u = g v) :
    windingNumber (strandDiscriminant fun k t => g t * K k t) u v =
      ((S * (S - 1) : ℕ) : ℤ) * windingNumber g u v +
        windingNumber (strandDiscriminant K) u v := by
  classical
  have huv := hK.lt.le
  have hcard : ((Finset.univ : Finset (Fin S × Fin S)).filter (fun p => p.1 ≠ p.2)).card =
      S * (S - 1) := by
    have h := Finset.offDiag_card (Finset.univ : Finset (Fin S))
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Nat.mul_sub_one, ← h]
    congr 1
    ext p
    simp [Finset.mem_offDiag]
  have heq : (strandDiscriminant fun k t => g t * K k t) =
      (g ^ (S * (S - 1))) * strandDiscriminant K := by
    funext t
    simp only [strandDiscriminant, Pi.mul_apply, Pi.pow_apply]
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hgpow : ContinuousOn (g ^ (S * (S - 1))) (Icc u v) := hg.pow _
  rw [heq, windingNumber_mul huv hgpow (fun t ht => pow_ne_zero _ (hg0 t ht))
    (by simp only [Pi.pow_apply, hgl]) hK.strandDiscriminant_continuousOn
    hK.strandDiscriminant_ne_zero hK.strandDiscriminant_closing,
    windingNumber_pow huv hg hg0 hgl]

/-! ### Signed crossing counts -/

/-- Projected crossing data from finitely many transverse crossings, none at the endpoints
of the period. -/
def sheetCrossingDataOfTransverse {m : ℕ} (y : Fin m → ℝ → ℂ) (b : ℝ) (c : ℂ)
    (hdiff : ∀ k, Differentiable ℝ (y k))
    (hfin : ∀ k l, k ≠ l →
      {θ | θ ∈ Icc b (b + 2 * π) ∧ (c * (y k θ - y l θ)).re = 0}.Finite)
    (hb : ∀ k l, k ≠ l → (c * (y k b - y l b)).re ≠ 0)
    (hd : ∀ k l, k ≠ l → (c * (y k (b + 2 * π) - y l (b + 2 * π))).re ≠ 0)
    (htr : ∀ k l, k ≠ l → ∀ θ, (c * (y k θ - y l θ)).re = 0 →
      (c * deriv (fun t => y k t - y l t) θ).re ≠ 0) :
    SheetCrossingData m y b c where
  crossings k l := if h : k = l then ∅ else (hfin k l h).toFinset
  mem_crossings_iff k l hkl θ hθ := by
    rw [dif_neg hkl.ne, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨hθ, h⟩, fun h => h.2⟩
  crossings_subset k l hkl θ hθ := by
    rw [dif_neg hkl.ne, Set.Finite.mem_toFinset] at hθ
    obtain ⟨hθI, hz⟩ := hθ
    refine ⟨lt_of_le_of_ne hθI.1 fun he => ?_, lt_of_le_of_ne hθI.2 fun he => ?_⟩
    · subst he
      exact hb k l hkl.ne hz
    · subst he
      exact hd k l hkl.ne hz
  derivative k l θ := deriv (fun t => y k t - y l t) θ
  hasDerivAt k l _ θ _ := (((hdiff k).sub (hdiff l)) θ).hasDerivAt
  transverse k l hkl θ hθ := by
    rw [dif_neg hkl.ne, Set.Finite.mem_toFinset] at hθ
    exact htr k l hkl.ne θ hθ.2

/-- The signed crossing count of a closed braid is the winding number of its strand
discriminant. -/
theorem SheetCrossingData.signedCount_eq_windingNumber {m : ℕ} {y : Fin m → ℝ → ℂ} {b : ℝ}
    {c : ℂ} (D : SheetCrossingData m y b c) (hc : c ≠ 0) {τ : Equiv.Perm (Fin m)}
    (hy : IsClosedStrandBraid y b (b + 2 * π) τ) :
    D.signedCount = windingNumber (strandDiscriminant y) b (b + 2 * π) := by
  have harg := D.argChange_prod_offDiag_eq hc hy.continuousOn hy.injective τ hy.closing
  have hw := argChange_eq_two_pi_mul_windingNumber hy.lt.le hy.strandDiscriminant_continuousOn
    hy.strandDiscriminant_ne_zero hy.strandDiscriminant_closing
  change argChange (strandDiscriminant y) b (b + 2 * π) = _ at harg
  rw [hw] at harg
  have h := mul_left_cancel₀ (by positivity : (2 * π) ≠ 0) harg
  exact_mod_cast h.symm

/-- Every crossing sign is `1` when every crossing is positive. -/
theorem SheetCrossingData.crossingSign_eq_one {m : ℕ} {y : Fin m → ℝ → ℂ} {b : ℝ}
    {c : ℂ} (D : SheetCrossingData m y b c) {k l : Fin m} {θ : ℝ}
    (hpos : 0 < -(c * (y k θ - y l θ)).im * (c * D.derivative k l θ).re) :
    D.crossingSign k l θ = 1 :=
  realSignInt_of_pos hpos

/-! ### Counting coincident pairs in positions and in labels -/

theorem card_offDiag_symm_eq_two_mul {S : ℕ} (R : Fin S → Fin S → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → R y x) :
    ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 ≠ p.2 ∧ R p.1 p.2).card =
      2 * ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 < p.2 ∧ R p.1 p.2).card := by
  classical
  have hsplit : ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 ≠ p.2 ∧ R p.1 p.2) =
      ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 < p.2 ∧ R p.1 p.2) ∪
        ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.2 < p.1 ∧ R p.1 p.2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨hne, hr⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h, hr⟩
      · exact Or.inr ⟨h, hr⟩
    · rintro (⟨h, hr⟩ | ⟨h, hr⟩)
      · exact ⟨h.ne, hr⟩
      · exact ⟨h.ne', hr⟩
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 < p.2 ∧ R p.1 p.2)
      ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.2 < p.1 ∧ R p.1 p.2) := by
    rw [Finset.disjoint_filter]
    intro p _ h h'
    exact lt_asymm h.1 h'.1
  have hswap : ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.2 < p.1 ∧ R p.1 p.2).card =
      ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 < p.2 ∧ R p.1 p.2).card := by
    apply Finset.card_bij (fun p _ => p.swap)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨hp.1, hR _ _ hp.2⟩
    · intro p _ p' _ h
      exact Prod.swap_injective h
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hp ⊢
      exact ⟨hp.1, hR _ _ hp.2⟩
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap]
  ring

/-- Counting coincident unordered pairs does not depend on the labelling. -/
theorem card_coincident_pairs_relabel {S : ℕ} (f : Fin S → ℝ) (σ : Equiv.Perm (Fin S)) :
    ((Finset.univ : Finset (Fin S × Fin S)).filter
        fun p => p.1 < p.2 ∧ f (σ p.1) = f (σ p.2)).card =
      ((Finset.univ : Finset (Fin S × Fin S)).filter fun p => p.1 < p.2 ∧ f p.1 = f p.2).card := by
  classical
  have h1 := card_offDiag_symm_eq_two_mul (fun x y => f (σ x) = f (σ y)) (fun _ _ h => h.symm)
  have h2 := card_offDiag_symm_eq_two_mul (fun x y => f x = f y) (fun _ _ h => h.symm)
  have hbij : ((Finset.univ : Finset (Fin S × Fin S)).filter
        fun p => p.1 ≠ p.2 ∧ f (σ p.1) = f (σ p.2)).card =
      ((Finset.univ : Finset (Fin S × Fin S)).filter
        fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2).card := by
    apply Finset.card_bij (fun p _ => (σ p.1, σ p.2))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨fun h => hp.1 (σ.injective h), hp.2⟩
    · intro p _ p' _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (σ.injective h.1) (σ.injective h.2)
    · intro p hp
      refine ⟨(σ.symm p.1, σ.symm p.2), ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      simp only [Equiv.apply_symm_apply]
      exact ⟨fun h => hp.1 (σ.symm.injective h), hp.2⟩
  omega

/-- A positive event word has as many letters as coincident unordered pairs of labels. -/
theorem IsPositiveBraidEventWord.length_eq_card_labels {S : ℕ} {K : Fin S → ℝ → ℂ} {θ : ℝ}
    {before after : Equiv.Perm (Fin S)} {w : PositiveAdjacentWord S}
    (h : IsPositiveBraidEventWord K θ before after w) :
    w.length = ((Finset.univ : Finset (Fin S × Fin S)).filter
      fun p => p.1 < p.2 ∧ (K p.1 θ).re = (K p.2 θ).re).card := by
  rw [h.2.2.2.2]
  exact card_coincident_pairs_relabel (fun k => (K k θ).re) after

end OnLeConjecture.Analytic
