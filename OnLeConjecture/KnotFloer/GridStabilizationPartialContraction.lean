/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationPartialFactor
public import OnLeConjecture.KnotFloer.SpecialContractionProduct

/-!
# Retraction of the partially blocked stabilized grid

The two new X markings remain blocked here. The stabilized complex retracts to two
copies of the old complex with its split X marking blocked. The inclusion contains
the correction determined by the connecting block and the constructed homotopy.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- Separate a stabilized chain into its off-center and center parts. -/
noncomputable def laurentStabilizationSplitEquiv : LaurentChain R (n + 1) ≃ₗ[LaurentPolynomial R]
    ((G.StabilizeXOffCenterState s →₀ LaurentPolynomial R) × LaurentChain R n) where
  toFun c := (laurentOffCenterProjection G s R c, laurentStabilizationCenterProjection G s R c)
  invFun c := laurentOffCenterInclusion G s R c.1 + laurentStabilizationCenterInclusion G s R c.2
  left_inv c := by
    change laurentOffCenterInclusion G s R (laurentOffCenterProjection G s R c) +
      laurentStabilizationCenterInclusion G s R (laurentStabilizationCenterProjection G s R c) = c
    exact (add_comm _ _).trans (laurentStabilizationCenter_add_offCenter G s R c)
  right_inv c := by
    apply Prod.ext
    · simp only [map_add, laurentOffCenterProjection_inclusion,
        laurentOffCenterProjection_centerInclusion, add_zero]
    · simp only [map_add, laurentStabilizationCenterProjection_offCenterInclusion, zero_add]
      exact LinearMap.congr_fun (laurentStabilizationCenterProjection_comp_inclusion G s R) c.2
  map_add' c d := by simp only [map_add, Prod.mk_add_mk]
  map_smul' a c := by simp only [map_smul, RingHom.id_apply, Prod.smul_mk]

/-- The partially blocked differential in the stated splitting is triangular. -/
theorem laurentStabilizationSplitEquiv_differential (c : LaurentChain R (n + 1)) :
    laurentStabilizationSplitEquiv G s R
      (laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
        R {s.castSucc, s.succ} c) =
    SpecialContraction.triangularDifferential (localComparisonOffCenterDifferential G s R)
      (laurentXBlockedDifferential G R {s}) (localStabilizationConnecting G s R)
      (laurentStabilizationSplitEquiv G s R c) := by
  have hc := LinearMap.congr_fun (localComparisonOffCenterInclusion_chain G s R)
    (laurentOffCenterProjection G s R c)
  simp only [LinearMap.comp_apply] at hc
  conv_lhs => rw [← laurentStabilizationCenter_add_offCenter G s R c]
  rw [map_add, localStabilizationDifferential_centerInclusion, ← hc]
  apply Prod.ext
  · change laurentOffCenterProjection G s R (_ + _) = _
    simp only [map_add, laurentOffCenterProjection_centerInclusion,
      laurentOffCenterProjection_inclusion, zero_add]
    exact add_comm _ _
  · change laurentStabilizationCenterProjection G s R (_ + _) = _
    simp only [map_add, laurentStabilizationCenterProjection_offCenterInclusion, add_zero]
    exact LinearMap.congr_fun (laurentStabilizationCenterProjection_comp_inclusion G s R) _

variable [CharP R 2]

/-- The actual connecting block anticommutes with its two differentials. -/
theorem localStabilizationConnecting_chain :
    localComparisonOffCenterDifferential G s R ∘ₗ localStabilizationConnecting G s R +
      localStabilizationConnecting G s R ∘ₗ laurentXBlockedDifferential G R {s} = 0 := by
  apply LinearMap.ext
  intro c
  have h := congrArg (laurentOffCenterProjection G s R)
    (LinearMap.congr_fun (laurentXBlockedDifferential_comp_self
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ})
      (laurentStabilizationCenterInclusion G s R c))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] at h
  rw [localStabilizationDifferential_centerInclusion, map_add,
    localStabilizationDifferential_centerInclusion, map_add, map_add,
    laurentOffCenterProjection_centerInclusion, zero_add,
    laurentOffCenterProjection_inclusion] at h
  change localStabilizationConnecting G s R (laurentXBlockedDifferential G R {s} c) +
    localComparisonOffCenterDifferential G s R (localStabilizationConnecting G s R c) = 0 at h
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply, add_comm] using h

/-- The product-coordinate retraction uses the actual connecting map. -/
noncomputable def localStabilizationProductRetraction :=
  SpecialContraction.triangular (localComparisonRetraction G s R)
    (laurentXBlockedDifferential G R {s}) (localStabilizationConnecting G s R)
    (localStabilizationConnecting_chain G s R) (localComparisonForward_connecting G s R)

omit [CharP R 2] in
/-- Conjugating the triangular differential recovers the actual partially blocked differential. -/
theorem localStabilizationConjugateDifferential :
    (laurentStabilizationSplitEquiv G s R).symm.toLinearMap ∘ₗ
      SpecialContraction.triangularDifferential (localComparisonOffCenterDifferential G s R)
        (laurentXBlockedDifferential G R {s}) (localStabilizationConnecting G s R) ∘ₗ
          (laurentStabilizationSplitEquiv G s R).toLinearMap =
    laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
      R {s.castSucc, s.succ} := by
  apply LinearMap.ext
  intro c
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    congrArg (laurentStabilizationSplitEquiv G s R).symm
      (laurentStabilizationSplitEquiv_differential G s R c).symm

/-- The actual two-new-X-blocked stabilized complex retracts to two old blocked copies. -/
noncomputable def localStabilizationRetraction :
    LinearSpecialContraction
      (laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
        R {s.castSucc, s.succ})
      ((laurentXBlockedDifferential G R {s}).prodMap (laurentXBlockedDifferential G R {s})) := by
  let c := SpecialContraction.transportSource (localStabilizationProductRetraction G s R)
    (laurentStabilizationSplitEquiv G s R)
  exact {
    incl := c.incl
    proj := c.proj
    homotopy := c.homotopy
    dM_comp_incl := by rw [← localStabilizationConjugateDifferential]; exact c.dM_comp_incl
    proj_comp_dM := by rw [← localStabilizationConjugateDifferential]; exact c.proj_comp_dM
    proj_comp_incl := c.proj_comp_incl
    dM_comp_homotopy_add_homotopy_comp_dM := by
      rw [← localStabilizationConjugateDifferential]
      exact c.dM_comp_homotopy_add_homotopy_comp_dM
    homotopy_comp_incl := c.homotopy_comp_incl
    proj_comp_homotopy := c.proj_comp_homotopy
    homotopy_comp_homotopy := c.homotopy_comp_homotopy }

/-- Its projection consists of the crossing comparison and center restriction. -/
theorem localStabilizationRetraction_proj (c : LaurentChain R (n + 1)) :
    (localStabilizationRetraction G s R).proj c =
      (localComparisonOffCenterToCenter G s R (laurentOffCenterProjection G s R c),
        laurentStabilizationCenterProjection G s R c) := rfl

/-- Its homotopy is the included off-center homotopy. -/
theorem localStabilizationRetraction_homotopy (c : LaurentChain R (n + 1)) :
    (localStabilizationRetraction G s R).homotopy c =
      -laurentOffCenterInclusion G s R
        (localComparisonOffCenterInverseHomotopy G s R (laurentOffCenterProjection G s R c)) := by
  change laurentOffCenterInclusion G s R (-_) + laurentStabilizationCenterInclusion G s R 0 = _
  rw [map_zero, add_zero, map_neg]
  rfl

/-- Its inclusion has the correction dictated by the connecting block. -/
theorem localStabilizationRetraction_incl (c : LaurentChain R n × LaurentChain R n) :
    (localStabilizationRetraction G s R).incl c =
      laurentOffCenterInclusion G s R
        (localComparisonBackward G s R c.1 + localComparisonOffCenterInverseHomotopy G s R
          (localStabilizationConnecting G s R c.2)) +
      laurentStabilizationCenterInclusion G s R c.2 := by
  change laurentOffCenterInclusion G s R (_ - -_) + _ = _
  rw [sub_neg_eq_add]
  rfl

end OnLeConjecture.KnotFloer.GridFull
