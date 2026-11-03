/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationOCenter

/-!
# Partner coefficients in the full comparison projection

On chains supported on row-matching sources, the first comparison component reads
exactly the coefficients of the center partners. The homotopy therefore has zero
coefficients at these partners.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- On source-supported chains the first comparison component reads partner coefficients. -/
theorem fullStabilizationTransferredRetraction_proj_fst_of_source_support
    (c : LaurentChain R (n + 1))
    (hc : ∀ y, ¬RowMatchingSource s (G.X s) y → c y = 0) (x : GridState n) :
    ((fullStabilizationTransferredRetraction G s R).proj c).1 x =
      c (stabilizationPartnerState G s x).val := by
  classical
  let f : LaurentChain R (n + 1) →ₗ[LaurentPolynomial R] LaurentPolynomial R :=
    Finsupp.lapply x ∘ₗ LinearMap.fst _ _ _ ∘ₗ
      (fullStabilizationTransferredRetraction G s R).proj
  have hformula : f c = ∑ y : GridState (n + 1), c y * f (single y 1) := by
    have hsingle (y : GridState (n + 1)) : f (single y (c y)) = c y * f (single y 1) := by
      rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    conv_lhs => rw [← Finsupp.sum_single c, map_finsuppSum]
    simp only [Finsupp.sum, hsingle]
    exact Finset.sum_subset (Finset.subset_univ _) fun y _ hy => by
      rw [Finsupp.notMem_support_iff.mp hy, zero_mul]
  change f c = _
  rw [hformula, Finset.sum_eq_single (stabilizationPartnerState G s x).val]
  · have h : f (single (stabilizationPartnerState G s x).val 1) = 1 := by
      change ((fullStabilizationTransferredRetraction G s R).proj _).1 x = 1
      rw [fullStabilizationTransferredRetraction_proj_partner_single]
      exact Finsupp.single_eq_same
    rw [h, mul_one]
  · intro y _ hy
    by_cases hs : RowMatchingSource s (G.X s) y
    · obtain ⟨i, hi⟩ := (G.stabilizeXConeStateEquiv s).surjective y
      cases i with
      | inr z =>
        exact False.elim (G.not_stabilizeXMatchingSource_inr s z
          ((rowMatchingSource_coneState G s (.inr z)).mp (hi ▸ hs)))
      | inl i =>
        have hiy : i.val = y := by simpa only [G.stabilizeXConeStateEquiv_apply_inl] using hi
        have hsource := (rowMatchingSource_coneState G s (.inl i)).mp (hi ▸ hs)
        have hn : G.stabilizeXMatching s (.inl i) ≠ .inr x := by
          intro heq
          have hh := heq.trans (stabilizationPartnerState_matching G s x).symm
          have hh' := Sum.inl.inj
            (Function.Involutive.injective (G.stabilizeXMatching_involutive s) hh)
          apply hy
          exact hiy.symm.trans (congrArg Subtype.val hh')
        have hz : f (single y 1) = 0 := by
          change ((fullStabilizationTransferredRetraction G s R).proj _).1 x = 0
          rw [← hiy, fullStabilizationTransferredRetraction_proj_source_coefficient_eq
            G s R i hsource, if_neg hn]
        rw [hz, mul_zero]
    · rw [hc y hs, zero_mul]
  · simp

/-- The full homotopy has no coefficient at a center partner. -/
theorem fullStabilizationTransferredRetraction_homotopy_apply_partner
    (c : LaurentChain R (n + 1)) (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).homotopy c
      (stabilizationPartnerState G s x).val = 0 := by
  have h := congrArg (fun z : LaurentChain R n × LaurentChain R n => z.1 x)
    (LinearMap.congr_fun (fullStabilizationTransferredRetraction G s R).proj_comp_homotopy c)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Prod.fst_zero, Finsupp.zero_apply] at h
  rw [fullStabilizationTransferredRetraction_proj_fst_of_source_support G s R _
    (fullStabilizationTransferredRetraction_homotopy_apply_of_not_source G s R c) x] at h
  exact h

end OnLeConjecture.KnotFloer.GridFull
