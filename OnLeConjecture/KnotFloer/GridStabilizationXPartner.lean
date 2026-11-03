/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationXDerivativeSupport

/-!
# The X derivative from partners to centers

Its center coefficients are the already computed adjacent-row comparison coefficients.
This identifies the second critical set under the full projection.
-/

@[expose] public section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti Finsupp
variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- A full X-crossing rectangle from a partner to a center already avoids the other new X. -/
theorem stabilizationXPartnerRectangles_eq_local (x y : GridState n) :
    (GridRectangleBetween.emptyRectangles (stabilizationPartnerState G s x).val
      (y.insertPoint s.succ (G.X s).succ)).filter
      (fun r => (s.succ, (G.X s).castSucc) ∈ r.toGridRectangle.coveredSquares) =
        localComparisonRectangles G s (.inl (stabilizationPartnerState G s x)) (.inr y) := by
  classical
  have hXb : (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.succ = (G.X s).castSucc := by
    rw [GridDiagram.stabilizeX_castSucc_X, GridState.insertPoint_apply_newColumn]
  have hXa : (G.stabilizeX s.castSucc (G.X s).castSucc s).X s.castSucc = (G.X s).succ := by
    simp
  dsimp only [localComparisonRectangles, comparisonConeState]
  ext r
  simp only [Finset.mem_filter, hXb, hXa]
  constructor
  · rintro ⟨he, ha⟩
    refine ⟨he, ha, ?_⟩
    have hb : s.succ ≠ r.right := by
      intro h
      have hc := ((GridRectangle.mem_coveredSquares _ _).mp ha).1
      change s.succ ∈ Grid.cIco r.left r.right at hc
      rw [← h] at hc
      exact Grid.right_notMem_cIco _ _ hc
    have hl : r.left = s.succ := by
      by_contra h
      have hv := r.map_of_ne s.succ (Ne.symm h) hb
      simp only [stabilizationPartnerState, GridState.swapRows_apply,
        GridState.insertPoint_apply_newColumn, Equiv.swap_apply_right] at hv
      exact Fin.castSucc_lt_succ.ne hv.symm
    have ht : r.top = (G.X s).succ := by
      have hv := r.map_left
      rw [hl, GridState.insertPoint_apply_newColumn] at hv
      exact hv.symm
    intro hbad
    have hr := ((GridRectangle.mem_coveredSquares _ _).mp hbad).2
    change (G.X s).succ ∈ Grid.cIco r.bottom r.top at hr
    rw [ht] at hr
    exact Grid.right_notMem_cIco _ _ hr
  · exact fun h => ⟨h.1, h.2.1⟩

open Classical in
/-- The X derivative matrix from partners to centers is the identity. -/
theorem stabilizationXDerivative_partner_center_coefficient (x y : GridState n) :
    stabilizationXDerivative G s R (single (stabilizationPartnerState G s x).val 1)
      (y.insertPoint s.succ (G.X s).succ) = if x = y then 1 else 0 := by
  rw [stabilizationXDerivative_single_apply, stabilizationXPartnerRectangles_eq_local]
  simp_rw [squareWeight_oSquareWeight, laurentSpecialization_OMonomial]
  have h := fullStabilizationTransferredRetraction_proj_source_coefficient G s R
    (stabilizationPartnerState G s x) (stabilizationPartnerState_is_matching_source G s x) y
  rw [fullStabilizationTransferredRetraction_proj_partner_single] at h
  dsimp only [comparisonConeState] at h ⊢
  simpa only [Finsupp.single_apply] using h.symm

/-- The full homotopy kills the X derivative of each partner state. -/
theorem fullStabilizationTransferredRetraction_homotopy_XDerivative_partner
    (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).homotopy
      (stabilizationXDerivative G s R (single (stabilizationPartnerState G s x).val 1)) = 0 :=
  fullStabilizationTransferredRetraction_homotopy_XDerivative_eq_zero G s R _
    (fullStabilizationTransferredRetraction_homotopy_partner_single G s R x)

/-- The X derivative takes the partner basis to the second copy under the full projection. -/
theorem fullStabilizationTransferredRetraction_proj_XDerivative_partner (x : GridState n) :
    (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationXDerivative G s R (single (stabilizationPartnerState G s x).val 1)) =
        (0, single x 1) := by
  classical
  apply Prod.ext
  · exact fullStabilizationTransferredRetraction_proj_XDerivative_fst G s R _
  · have h := congrArg (laurentStabilizationCenterProjection G s R)
      ((fullStabilizationTransferredRetraction G s R).incl_proj_apply
        (stabilizationXDerivative G s R (single (stabilizationPartnerState G s x).val 1)))
    rw [centerProjection_fullStabilizationTransferredRetraction_incl,
      fullStabilizationTransferredRetraction_homotopy_XDerivative_partner, map_zero,
      sub_zero, map_sub, centerProjection_fullStabilizationTransferredRetraction_homotopy,
      sub_zero] at h
    rw [h]
    apply Finsupp.ext
    intro y
    rw [laurentStabilizationCenterProjection_apply,
      stabilizationXDerivative_partner_center_coefficient, Finsupp.single_apply]

/-- The second-to-first component of the actual transferred differential vanishes on generators. -/
theorem stabilizationTransferredDifferential_second_fst_single (x : GridState n) :
    (stabilizationTransferredDifferential G s R (0, single x 1)).1 = 0 := by
  let c := single (stabilizationPartnerState G s x).val (1 : LaurentPolynomial R)
  have h := (fullStabilizationTransferredRetraction G s R).proj_dM_apply
    (stabilizationXDerivative G s R c)
  rw [show (fullStabilizationTransferredRetraction G s R).proj
      (stabilizationXDerivative G s R c) = (0, single x 1) from
        fullStabilizationTransferredRetraction_proj_XDerivative_partner G s R x] at h
  have hD := LinearMap.congr_fun (stabilizationXDerivative_chain G s R) c
  simp only [LinearMap.comp_apply] at hD
  rw [hD] at h
  exact (congrArg Prod.fst h).symm.trans
    (fullStabilizationTransferredRetraction_proj_XDerivative_fst G s R _)

/-- The second-to-first block of the constructed full transferred differential is zero. -/
theorem stabilizationTransferredDifferential_second_fst :
    LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
      stabilizationTransferredDifferential G s R ∘ₗ
        LinearMap.inr (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) = 0 := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  exact stabilizationTransferredDifferential_second_fst_single G s R x


/-- The actual transferred differential consists of two equal diagonal components. -/
theorem stabilizationTransferredDifferential_eq_repeated_diagonal :
    stabilizationTransferredDifferential G s R =
      (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationTransferredDifferential G s R ∘ₗ
          LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)).prodMap
      (LinearMap.fst (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n) ∘ₗ
        stabilizationTransferredDifferential G s R ∘ₗ
          LinearMap.inl (LaurentPolynomial R) (LaurentChain R n) (LaurentChain R n)) := by
  apply LinearMap.ext
  intro z
  have hfirst : (stabilizationTransferredDifferential G s R (z.1, 0)).2 = 0 :=
    LinearMap.congr_fun (stabilizationTransferredDifferential_first_snd G s R) z.1
  have hsecond : (stabilizationTransferredDifferential G s R (0, z.2)).1 = 0 :=
    LinearMap.congr_fun (stabilizationTransferredDifferential_second_fst G s R) z.2
  have hz : z = (z.1, 0) + (0, z.2) := by simp
  apply Prod.ext
  · change (stabilizationTransferredDifferential G s R z).1 =
      (stabilizationTransferredDifferential G s R (z.1, 0)).1
    conv_lhs => rw [hz, map_add, Prod.fst_add, hsecond, add_zero]
  · change (stabilizationTransferredDifferential G s R z).2 =
      (stabilizationTransferredDifferential G s R (z.2, 0)).1
    conv_lhs => rw [hz, map_add, Prod.snd_add, hfirst, zero_add]
    exact (stabilizationTransferredDifferential_diagonal_eq G s R z.2).symm

end OnLeConjecture.KnotFloer.GridFull
