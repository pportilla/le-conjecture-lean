/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTensorCoordinates
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSpecialization

/-!
# The full balanced tensor differential in seam coordinates

The factor coefficient formula is proved for the tensor differential
under the explicit basis equivalence. Thus equality with the actual
retained Schur differential is precisely the finite specialized parity
identity, rather than an additional weight or grading assertion.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti TensorProduct
variable {n m : ℕ} {K : Type*} [Field K]
variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))

/-- The genuine full balanced tensor differential in the pair-state basis. -/
def seamTensorCoordinateDifferential : Module.End (LaurentPolynomial K)
    (SeamRetainedCoordinates K n m) :=
  (seamTensorCoordinatesEquiv K).toLinearMap ∘ₗ laurentTensorDifferential G H ∘ₗ
    (seamTensorCoordinatesEquiv K).symm.toLinearMap

/-- The entries are the full factor rectangle coefficients, with the other factor fixed. -/
theorem seamTensorCoordinateDifferential_single_apply (p q : SeamRetainedIndex n m) :
    seamTensorCoordinateDifferential (K := K) G H (Pi.single p 1) q =
      seamTensorCoefficient G H K p q := by
  classical
  simp only [seamTensorCoordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    seamTensorCoordinatesEquiv_symm_single, laurentTensorDifferential_tmul, map_add, Pi.add_apply,
    seamTensorCoordinatesEquiv_tmul_apply, laurentDifferential_single, laurentOnGenerator_apply,
    seamTensorCoefficient, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- The tensor operator is the coefficient matrix already used in the specialization statement. -/
theorem seamTensorCoordinateDifferential_apply (c : SeamRetainedCoordinates K n m)
    (q : SeamRetainedIndex n m) :
    seamTensorCoordinateDifferential (K := K) G H c q =
      ∑ p : SeamRetainedIndex n m, c p * seamTensorCoefficient G H K p q := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single c]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have hs : Pi.single p (c p) = (c p) • Pi.single p (1 : LaurentPolynomial K) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hs, map_smul, Pi.smul_apply, smul_eq_mul, seamTensorCoordinateDifferential_single_apply]

private theorem end_eq_iff_single_entries
    (A B : Module.End (LaurentPolynomial K) (SeamRetainedCoordinates K n m)) :
    A = B ↔ ∀ p q, A (Pi.single p 1) q = B (Pi.single p 1) q := by
  classical
  constructor
  · intro h p q
    rw [h]
  · intro h
    apply LinearMap.ext
    intro c
    rw [← Finset.univ_sum_single c, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hs : Pi.single p (c p) = (c p) • Pi.single p (1 : LaurentPolynomial K) := by
      simp only [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul]
    exact congrArg (fun v => (c p) • v) (funext (h p))

/-- No coefficient or basis condition beyond the exact Schur parity identity is needed. -/
theorem seamRetainedDifferential_eq_tensorCoordinate_iff_evalOne
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0) :
    seamRetainedDifferential G H hG hH K = seamTensorCoordinateDifferential (K := K) G H ↔
      ∀ p q : SeamRetainedIndex n m,
        laurentEvalOne (seamRetainedDifferential G H hG hH K (Pi.single p 1) q) =
          (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : K) else 0) +
            if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : K) else 0 := by
  rw [end_eq_iff_single_entries]
  simp only [seamTensorCoordinateDifferential_single_apply,
    seamRetainedDifferential_eq_tensor_iff_evalOne G H hG hH hO]

/-- Exact operator intertwining is equivalent to that same finite parity identity. -/
theorem seamTensorCoordinates_intertwines_iff_evalOne
    (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0) :
    seamRetainedDifferential G H hG hH K ∘ₗ (seamTensorCoordinatesEquiv K).toLinearMap =
      (seamTensorCoordinatesEquiv K).toLinearMap ∘ₗ laurentTensorDifferential G H ↔
      ∀ p q : SeamRetainedIndex n m,
        laurentEvalOne (seamRetainedDifferential G H hG hH K (Pi.single p 1) q) =
          (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : K) else 0) +
            if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : K) else 0 := by
  rw [← seamRetainedDifferential_eq_tensorCoordinate_iff_evalOne G H hG hH hO]
  constructor
  · intro h
    apply LinearMap.ext
    intro c
    have hh := LinearMap.congr_fun h ((seamTensorCoordinatesEquiv K).symm c)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      seamTensorCoordinateDifferential] using hh
  · intro h
    rw [h]
    apply LinearMap.ext
    intro c
    simp only [seamTensorCoordinateDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]

end OnLeConjecture.KnotFloer.GridFull
