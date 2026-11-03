/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMatchingInverse
public import OnLeConjecture.KnotFloer.FiniteBlockCancellation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Full seam cancellation in actual state coordinates

The full state basis splits into all factor pairs, increasing matching
sources, and their decreasing partners. The proved inverse of the actual
full source-to-target differential block gives an unconditional special
contraction. The retained differential is expressed by its complete
weighted Schur formula. These retained coordinates have not been identified
with the graded tensor basis, and no filtration estimate is assumed.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti
open scoped Matrix
variable {n m : ℕ}

abbrev SeamRetainedIndex (n m : ℕ) := GridState (n + 1) × GridState (m + 1)
abbrev SeamThreeIndex (n m : ℕ) :=
  SeamRetainedIndex n m ⊕ (SeamMatchingSource n m ⊕ SeamMatchingSource n m)

/-- The three actual state sectors, with no assumption on the second factor's state. -/
def seamThreeState : SeamThreeIndex n m → GridState (n + m + 1)
  | .inl p => seamState p.1 p.2
  | .inr (.inl x) => x.val.val
  | .inr (.inr x) => (seamComplementPartner x.val).val

private theorem seam_matching_source_ne_target (x y : SeamMatchingSource n m) :
    x.val.val ≠ (seamComplementPartner y.val).val := by
  intro h
  have he : x.val = seamComplementPartner y.val := Subtype.ext h
  exact ((seamComplementSource_partner_iff y.val).mp (he ▸ x.property)) y.property

theorem seamThreeState_injective : Function.Injective (seamThreeState (n := n) (m := m)) := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [seamThreeState] at h
  · exact congrArg Sum.inl (seamState_injective h)
  · exact False.elim (b.val.property (h ▸ seamState_mem_pairSector a.1 a.2))
  · exact False.elim ((seamComplementPartner b.val).property
      (h ▸ seamState_mem_pairSector a.1 a.2))
  · exact False.elim (a.val.property (h.symm ▸ seamState_mem_pairSector b.1 b.2))
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext (Subtype.ext h))
  · exact False.elim (seam_matching_source_ne_target a b h)
  · exact False.elim ((seamComplementPartner a.val).property
      (h.symm ▸ seamState_mem_pairSector b.1 b.2))
  · exact False.elim (seam_matching_source_ne_target b a h.symm)
  · apply congrArg (Sum.inr ∘ Sum.inr)
    apply Subtype.ext
    apply seamComplementPartner_involutive.injective
    exact Subtype.ext h

theorem seamThreeState_surjective : Function.Surjective (seamThreeState (n := n) (m := m)) := by
  classical
  intro w
  by_cases hw : SeamPairSector w
  · obtain ⟨x, z, rfl⟩ := exists_seamState_of_pairSector w hw
    exact ⟨.inl (x, z), rfl⟩
  · let c : SeamComplement n m := ⟨w, hw⟩
    by_cases hc : SeamComplementSource c
    · exact ⟨.inr (.inl ⟨c, hc⟩), rfl⟩
    · refine ⟨.inr (.inr ⟨seamComplementPartner c,
        (seamComplementSource_partner_iff c).mpr hc⟩), ?_⟩
      exact congrArg Subtype.val (seamComplementPartner_involutive c)

/-- The complete basis partition as an equivalence. -/
def seamThreeStateEquiv : SeamThreeIndex n m ≃ GridState (n + m + 1) :=
  Equiv.ofBijective seamThreeState ⟨seamThreeState_injective, seamThreeState_surjective⟩

@[simp] theorem seamThreeStateEquiv_apply (i : SeamThreeIndex n m) :
    seamThreeStateEquiv i = seamThreeState i := rfl

abbrev SeamRetainedCoordinates (R : Type*) [CommRing R] (n m : ℕ) :=
  SeamRetainedIndex n m → LaurentPolynomial R
abbrev SeamMatchingCoordinates (R : Type*) [CommRing R] (n m : ℕ) :=
  SeamMatchingSource n m → LaurentPolynomial R
abbrev SeamCoordinates (R : Type*) [CommRing R] (n m : ℕ) :=
  SeamRetainedCoordinates R n m × (SeamMatchingCoordinates R n m × SeamMatchingCoordinates R n m)

/-- Read the three coefficients of the full Laurent state module in their exact state sectors. -/
def seamCoordinateEquiv (R : Type*) [CommRing R] :
    LaurentChain R (n + m + 1) ≃ₗ[LaurentPolynomial R] SeamCoordinates R n m :=
  (Finsupp.linearEquivFunOnFinite (LaurentPolynomial R) (LaurentPolynomial R) _).trans
    ((LinearEquiv.funCongrLeft (LaurentPolynomial R) (LaurentPolynomial R)
      seamThreeStateEquiv).trans
      ((LinearEquiv.sumArrowLequivProdArrow _ _ (LaurentPolynomial R) (LaurentPolynomial R)).trans
        (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
          (LinearEquiv.sumArrowLequivProdArrow _ _ (LaurentPolynomial R) (LaurentPolynomial R)))))

@[simp] theorem seamCoordinateEquiv_retained (R : Type*) [CommRing R]
    (c : LaurentChain R (n + m + 1)) (p : SeamRetainedIndex n m) :
    (seamCoordinateEquiv R c).1 p = c (seamState p.1 p.2) := rfl

@[simp] theorem seamCoordinateEquiv_source (R : Type*) [CommRing R]
    (c : LaurentChain R (n + m + 1)) (x : SeamMatchingSource n m) :
    (seamCoordinateEquiv R c).2.1 x = c x.val.val := rfl

@[simp] theorem seamCoordinateEquiv_target (R : Type*) [CommRing R]
    (c : LaurentChain R (n + m + 1)) (x : SeamMatchingSource n m) :
    (seamCoordinateEquiv R c).2.2 x = c (seamComplementPartner x.val).val := rfl

@[simp] theorem seamCoordinateEquiv_symm_retained (R : Type*) [CommRing R]
    (c : SeamCoordinates R n m) (p : SeamRetainedIndex n m) :
    (seamCoordinateEquiv R).symm c (seamState p.1 p.2) = c.1 p :=
  congrArg (fun z => z.1 p) ((seamCoordinateEquiv R).apply_symm_apply c)

@[simp] theorem seamCoordinateEquiv_symm_source (R : Type*) [CommRing R]
    (c : SeamCoordinates R n m) (x : SeamMatchingSource n m) :
    (seamCoordinateEquiv R).symm c x.val.val = c.2.1 x :=
  congrArg (fun z => z.2.1 x) ((seamCoordinateEquiv R).apply_symm_apply c)

@[simp] theorem seamCoordinateEquiv_symm_target (R : Type*) [CommRing R]
    (c : SeamCoordinates R n m) (x : SeamMatchingSource n m) :
    (seamCoordinateEquiv R).symm c (seamComplementPartner x.val).val = c.2.2 x :=
  congrArg (fun z => z.2.2 x) ((seamCoordinateEquiv R).apply_symm_apply c)

/-- The actual full seam differential expressed in the proved three-sector coordinates. -/
def seamCoordinateDifferential
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] : Module.End (LaurentPolynomial R) (SeamCoordinates R n m) :=
  (seamCoordinateEquiv R).toLinearMap ∘ₗ
    laurentDifferential (connectedSumSeamGrid G H hG hH) R ∘ₗ
      (seamCoordinateEquiv R).symm.toLinearMap

theorem seamCoordinateDifferential_comp_self
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] :
    seamCoordinateDifferential G H hG hH R ∘ₗ seamCoordinateDifferential G H hG hH R = 0 := by
  apply LinearMap.ext
  intro c
  simp only [seamCoordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, laurentDifferential_sq_eq_zero, map_zero, LinearMap.zero_apply]

/-- The normalized full matching matrix acts by a proved linear equivalence. -/
def seamNormalizedMatchingEquiv
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    SeamMatchingCoordinates R n m ≃ₗ[LaurentPolynomial R] SeamMatchingCoordinates R n m :=
  { (seamMatchingMatrix G H hG hH R).mulVecLin with
    invFun := (seamMatchingMatrixInverse G H hG hH R).mulVecLin
    left_inv := by
      intro c
      change seamMatchingMatrixInverse G H hG hH R *ᵥ
        (seamMatchingMatrix G H hG hH R *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, seamMatchingMatrix_inverse_mul, Matrix.one_mulVec]
    right_inv := by
      intro c
      change seamMatchingMatrix G H hG hH R *ᵥ
        (seamMatchingMatrixInverse G H hG hH R *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, seamMatchingMatrix_mul_inverse, Matrix.one_mulVec] }

/-- Restore the unit removed from each target row of the internal differential. -/
def seamTargetUnitEquiv
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1)) (R : Type*) [CommRing R] :
    SeamMatchingCoordinates R n m ≃ₗ[LaurentPolynomial R] SeamMatchingCoordinates R n m where
  toFun c y := LaurentPolynomial.T (seamComplementOCount G H y.val : ℤ) * c y
  invFun c y := LaurentPolynomial.T (-(seamComplementOCount G H y.val : ℤ)) * c y
  left_inv c := by
    funext y
    dsimp only
    rw [← mul_assoc, ← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero, one_mul]
  right_inv c := by
    funext y
    dsimp only
    rw [← mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero, one_mul]
  map_add' c d := by funext y; exact mul_add _ _ _
  map_smul' a c := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The unnormalized source-to-target block of the actual full differential. -/
def seamFullMatchingBlockEquiv
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    SeamMatchingCoordinates R n m ≃ₗ[LaurentPolynomial R] SeamMatchingCoordinates R n m :=
  (seamNormalizedMatchingEquiv G H hG hH R).trans (seamTargetUnitEquiv G H R)

theorem seamFullMatchingBlockEquiv_apply
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) (y : SeamMatchingSource n m) :
    seamFullMatchingBlockEquiv G H hG hH R c y =
      ∑ x : SeamMatchingSource n m, laurentCoefficient (connectedSumSeamGrid G H hG hH) R
        x.val.val (seamComplementPartner y.val).val * c x := by
  change LaurentPolynomial.T _ * (∑ x, (LaurentPolynomial.T _ *
    laurentCoefficient (connectedSumSeamGrid G H hG hH) R
      x.val.val (seamComplementPartner y.val).val) * c x) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← mul_assoc, ← mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero, one_mul]

/-- The differential's target component on source coordinates is exactly the constructed block. -/
theorem seamCoordinateDifferential_source_target
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) :
    (seamCoordinateDifferential G H hG hH R (0, (c, 0))).2.2 =
      seamFullMatchingBlockEquiv G H hG hH R c := by
  classical
  funext y
  rw [seamCoordinateDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, seamCoordinateEquiv_target,
    laurentDifferential_apply_apply, Finsupp.sum_fintype _ _ (by intro z; exact zero_mul _)]
  rw [← (seamThreeStateEquiv (n := n) (m := m)).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [seamThreeStateEquiv_apply, seamThreeState,
    seamCoordinateEquiv_symm_retained, seamCoordinateEquiv_symm_source,
    seamCoordinateEquiv_symm_target, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero]
  rw [seamFullMatchingBlockEquiv_apply]
  apply Finset.sum_congr rfl
  intro x hx
  exact mul_comm _ _

/-- The exact inverse block includes the reciprocal of the removed row monomial. -/
theorem seamFullMatchingBlockEquiv_symm_apply
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) (x : SeamMatchingSource n m) :
    (seamFullMatchingBlockEquiv G H hG hH R).symm c x =
      ∑ y : SeamMatchingSource n m, seamMatchingMatrixInverse G H hG hH R x y *
        (LaurentPolynomial.T (-(seamComplementOCount G H y.val : ℤ)) * c y) := rfl

/-- The actual retained differential after cancellation of all complementary state pairs. -/
def seamRetainedDifferential
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    Module.End (LaurentPolynomial R) (SeamRetainedCoordinates R n m) :=
  FiniteBlockCancellation.transferredDifferential (seamCoordinateDifferential G H hG hH R)
    (seamFullMatchingBlockEquiv G H hG hH R)

/-- Cancellation in the proved three-sector coordinates uses the full differential block. -/
def seamCoordinateContraction
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] :
    LinearSpecialContraction (seamCoordinateDifferential G H hG hH R)
      (seamRetainedDifferential G H hG hH R) :=
  FiniteBlockCancellation.toSpecialContraction (seamCoordinateDifferential G H hG hH R)
    (seamFullMatchingBlockEquiv G H hG hH R)
    (seamCoordinateDifferential_source_target G H hG hH R)
    (seamCoordinateDifferential_comp_self G H hG hH R)

/-- Undoing the proved coordinate change returns the original full seam differential. -/
theorem seamCoordinateDifferential_conjugate
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    (seamCoordinateEquiv R).symm.toLinearMap ∘ₗ seamCoordinateDifferential G H hG hH R ∘ₗ
      (seamCoordinateEquiv R).toLinearMap =
        laurentDifferential (connectedSumSeamGrid G H hG hH) R := by
  apply LinearMap.ext
  intro c
  simp only [seamCoordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- A special contraction of the full seam complex to its transferred differential. -/
def seamFullContraction
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] :
    LinearSpecialContraction (laurentDifferential (connectedSumSeamGrid G H hG hH) R)
      (seamRetainedDifferential G H hG hH R) := by
  have c := SpecialContraction.transportSource (seamCoordinateContraction G H hG hH R)
    (seamCoordinateEquiv R)
  rw [seamCoordinateDifferential_conjugate] at c
  exact c

/-- The retained differential squares to zero as a consequence of actual full cancellation. -/
theorem seamRetainedDifferential_comp_self
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] [CharP R 2] :
    seamRetainedDifferential G H hG hH R ∘ₗ seamRetainedDifferential G H hG hH R = 0 :=
  FiniteBlockCancellation.transferredDifferential_comp_self
    (seamCoordinateDifferential G H hG hH R) (seamFullMatchingBlockEquiv G H hG hH R)
    (seamCoordinateDifferential_source_target G H hG hH R)
    (seamCoordinateDifferential_comp_self G H hG hH R)

/-- The retained differential is the direct block minus its complete inverse correction. -/
theorem seamRetainedDifferential_eq_schur
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] :
    seamRetainedDifferential G H hG hH R =
      FiniteBlockCancellation.retainedProjection ∘ₗ
        seamCoordinateDifferential G H hG hH R ∘ₗ FiniteBlockCancellation.retainedInclusion -
      FiniteBlockCancellation.retainedProjection ∘ₗ
        seamCoordinateDifferential G H hG hH R ∘ₗ
          FiniteBlockCancellation.homotopy (seamFullMatchingBlockEquiv G H hG hH R) ∘ₗ
            seamCoordinateDifferential G H hG hH R ∘ₗ FiniteBlockCancellation.retainedInclusion :=
  FiniteBlockCancellation.transferredDifferential_eq_schur _ _

/-- A retained generator has its factor-pair coordinate and no complementary coordinates. -/
theorem seamCoordinateEquiv_single_retained (R : Type*) [CommRing R]
    (p : SeamRetainedIndex n m) (a : LaurentPolynomial R) :
    seamCoordinateEquiv R (Finsupp.single (seamState p.1 p.2) a) = (Pi.single p a, (0, 0)) := by
  classical
  apply Prod.ext
  · funext q
    simp only [seamCoordinateEquiv_retained, Finsupp.single_apply, Pi.single_apply,
      seamState_injective.eq_iff, eq_comm]
  · apply Prod.ext
    · funext x
      change Finsupp.single (seamState p.1 p.2) a x.val.val = 0
      rw [Finsupp.single_eq_of_ne]
      intro h
      exact x.val.property (h.symm ▸ seamState_mem_pairSector p.1 p.2)
    · funext x
      change Finsupp.single (seamState p.1 p.2) a (seamComplementPartner x.val).val = 0
      rw [Finsupp.single_eq_of_ne]
      intro h
      exact (seamComplementPartner x.val).property (h.symm ▸ seamState_mem_pairSector p.1 p.2)

@[simp] theorem seamCoordinateEquiv_symm_single_retained (R : Type*) [CommRing R]
    (p : SeamRetainedIndex n m) (a : LaurentPolynomial R) :
    (seamCoordinateEquiv R).symm (Pi.single p a, (0, 0)) =
      Finsupp.single (seamState p.1 p.2) a := by
  apply (seamCoordinateEquiv R).injective
  rw [LinearEquiv.apply_symm_apply, seamCoordinateEquiv_single_retained]

/-- Source-to-retained coefficients are the unchanged full rectangle coefficients. -/
theorem seamCoordinateDifferential_source_retained
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (c : SeamMatchingCoordinates R n m) (p : SeamRetainedIndex n m) :
    (seamCoordinateDifferential G H hG hH R (0, (c, 0))).1 p =
      ∑ x : SeamMatchingSource n m,
        laurentCoefficient (connectedSumSeamGrid G H hG hH) R x.val.val (seamState p.1 p.2) *
          c x := by
  classical
  rw [seamCoordinateDifferential, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, seamCoordinateEquiv_retained,
    laurentDifferential_apply_apply, Finsupp.sum_fintype _ _ (by intro z; exact zero_mul _)]
  rw [← (seamThreeStateEquiv (n := n) (m := m)).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [seamThreeStateEquiv_apply, seamThreeState,
    seamCoordinateEquiv_symm_retained, seamCoordinateEquiv_symm_source,
    seamCoordinateEquiv_symm_target, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro x hx
  exact mul_comm _ _

/-- The direct retained matrix entry is an actual full seam coefficient. -/
theorem seamCoordinateDifferential_retained_single_retained
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) :
    (seamCoordinateDifferential G H hG hH R (Pi.single p 1, (0, 0))).1 q =
      laurentCoefficient (connectedSumSeamGrid G H hG hH) R
        (seamState p.1 p.2) (seamState q.1 q.2) := by
  change laurentDifferential (connectedSumSeamGrid G H hG hH) R
    ((seamCoordinateEquiv R).symm (Pi.single p 1, (0, 0))) (seamState q.1 q.2) = _
  rw [seamCoordinateEquiv_symm_single_retained, laurentDifferential_single,
    laurentOnGenerator_apply]

/-- The retained-to-target entry also uses the actual full seam coefficient. -/
theorem seamCoordinateDifferential_retained_single_target
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (p : SeamRetainedIndex n m) (y : SeamMatchingSource n m) :
    (seamCoordinateDifferential G H hG hH R (Pi.single p 1, (0, 0))).2.2 y =
      laurentCoefficient (connectedSumSeamGrid G H hG hH) R
        (seamState p.1 p.2) (seamComplementPartner y.val).val := by
  change laurentDifferential (connectedSumSeamGrid G H hG hH) R
    ((seamCoordinateEquiv R).symm (Pi.single p 1, (0, 0)))
      (seamComplementPartner y.val).val = _
  rw [seamCoordinateEquiv_symm_single_retained, laurentDifferential_single,
    laurentOnGenerator_apply]

/-- The transferred coefficient retains the full inverse correction with its Laurent weights. -/
theorem seamRetainedDifferential_single_apply_eq_schur
    (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0)
    (R : Type*) [CommRing R] (p q : SeamRetainedIndex n m) :
    seamRetainedDifferential G H hG hH R (Pi.single p 1) q =
      laurentCoefficient (connectedSumSeamGrid G H hG hH) R
        (seamState p.1 p.2) (seamState q.1 q.2) -
      ∑ x : SeamMatchingSource n m,
        laurentCoefficient (connectedSumSeamGrid G H hG hH) R x.val.val (seamState q.1 q.2) *
          ∑ y : SeamMatchingSource n m, seamMatchingMatrixInverse G H hG hH R x y *
            (LaurentPolynomial.T (-(seamComplementOCount G H y.val : ℤ)) *
              laurentCoefficient (connectedSumSeamGrid G H hG hH) R
                (seamState p.1 p.2) (seamComplementPartner y.val).val) := by
  rw [seamRetainedDifferential_eq_schur]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    FiniteBlockCancellation.retainedProjection, LinearMap.fst_apply,
    FiniteBlockCancellation.retainedInclusion, LinearMap.coe_mk, AddHom.coe_mk,
    FiniteBlockCancellation.homotopy_apply, Pi.sub_apply]
  rw [seamCoordinateDifferential_retained_single_retained,
    seamCoordinateDifferential_source_retained]
  simp_rw [seamFullMatchingBlockEquiv_symm_apply,
    seamCoordinateDifferential_retained_single_target]

end OnLeConjecture.KnotFloer.GridFull
