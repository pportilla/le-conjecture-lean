/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPreparedNative
public import OnLeConjecture.KnotFloer.GridLaurentTensorMaslov
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# The balanced tensor basis and the retained seam coefficients

Mathlib's tensor product of finitely supported functions identifies the
retained pair coefficients with the balanced Laurent tensor module.
For the prepared seam this identification respects the summed Maslov
degree and the convolved filtration. No differential identity is asserted.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti TensorProduct
variable {n m : ℕ}

/-- Read a balanced tensor in its pair-state basis. -/
def seamTensorCoordinatesEquiv (R : Type*) [CommRing R] :
    (LaurentChain R (n + 1) ⊗[LaurentPolynomial R] LaurentChain R (m + 1)) ≃ₗ[LaurentPolynomial R]
      SeamRetainedCoordinates R n m :=
  (finsuppTensorFinsupp' (LaurentPolynomial R) _ _).trans
    (Finsupp.linearEquivFunOnFinite (LaurentPolynomial R) (LaurentPolynomial R) _)

@[simp] theorem seamTensorCoordinatesEquiv_tmul_apply (R : Type*) [CommRing R]
    (c : LaurentChain R (n + 1)) (d : LaurentChain R (m + 1)) (p : SeamRetainedIndex n m) :
    seamTensorCoordinatesEquiv R (c ⊗ₜ[LaurentPolynomial R] d) p = c p.1 * d p.2 := by
  exact finsuppTensorFinsupp'_apply_apply _ _ _ c d p.1 p.2

/-- One retained basis coefficient is the corresponding balanced pure tensor. -/
theorem seamTensorCoordinatesEquiv_symm_single (R : Type*) [CommRing R]
    (p : SeamRetainedIndex n m) (a : LaurentPolynomial R) :
    (seamTensorCoordinatesEquiv R).symm (Pi.single p a) =
      Finsupp.single p.1 a ⊗ₜ[LaurentPolynomial R] Finsupp.single p.2 1 := by
  apply (seamTensorCoordinatesEquiv R).injective
  rw [LinearEquiv.apply_symm_apply]
  funext q
  simp only [seamTensorCoordinatesEquiv_tmul_apply, Pi.single_apply, Finsupp.single_apply]
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  by_cases h1 : q1 = p1 <;> by_cases h2 : q2 = p2 <;> simp_all [eq_comm]

private theorem seamCoordinates_mem_of_monomials
    {K : Type*} [Field K]
    {M : Type*} [AddCommMonoid M] [Module K M]
    (f : SeamRetainedCoordinates K n m →ₗ[K] M) (S : Submodule K M)
    (c : SeamRetainedCoordinates K n m)
    (hc : ∀ p j, j ∈ (c p).coeff.support →
      f (Pi.single p (LaurentPolynomial.T j)) ∈ S) :
    f c ∈ S := by
  classical
  have hexp : c = ∑ p : SeamRetainedIndex n m, ∑ j ∈ (c p).coeff.support,
      (c p).coeff j • Pi.single p (LaurentPolynomial.T j) := by
    funext q
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_eq_single q]
    · simp only [ite_true]
      have he := AddMonoidAlgebra.sum_coeff_single (c q)
      simpa only [Finsupp.sum, LaurentPolynomial.T, AddMonoidAlgebra.smul_single,
        smul_eq_mul, mul_one] using he.symm
    · intro p hp hpq
      simp [Ne.symm hpq]
    · simp
  rw [hexp, map_sum]
  apply S.sum_mem
  intro p hp
  rw [map_sum]
  apply S.sum_mem
  intro j hj
  rw [map_smul]
  exact S.smul_mem _ (hc p j hj)

private theorem seam_monomial_mem_bifiltration {K : Type*} [Field K]
    {l : ℕ} (G : GridDiagram l) (j : ℤ) (x : GridState l) :
    (Finsupp.single x (LaurentPolynomial.T j) : LaurentChain K l) ∈
      laurentBifiltrationLevel G K (-(j : ℝ)) ((G.alexander x : ℝ) - j) := by
  classical
  intro y k hk
  change k ∈ ((Finsupp.single x (AddMonoidAlgebra.single j (1 : K))) y).coeff.support at hk
  rcases eq_or_ne y x with rfl | hy
  · rw [Finsupp.single_eq_same, AddMonoidAlgebra.coeff_single] at hk
    have hkj := Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    simp only [hkj, le_refl, and_self]
  · rw [Finsupp.single_eq_of_ne hy] at hk
    simp at hk

variable {K : Type*} [Field K]
variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)
include hO

/-- Retained coefficients in degree d give a tensor in the sum degree d. -/
theorem seamTensorCoordinatesEquiv_symm_mem_maslov {d : ℤ} {c : SeamRetainedCoordinates K n m}
    (hc : c ∈ seamRetainedMaslovPiece G H hG hH K d) :
    (seamTensorCoordinatesEquiv K).symm c ∈ laurentTensorMaslovPiece G H d := by
  refine seamCoordinates_mem_of_monomials
    ((seamTensorCoordinatesEquiv K).symm.toLinearMap.restrictScalars K) _ c ?_
  intro p j hj
  change (seamTensorCoordinatesEquiv K).symm (Pi.single p (LaurentPolynomial.T j)) ∈ _
  rw [seamTensorCoordinatesEquiv_symm_single]
  have hh := (mem_seamRetainedMaslovPiece_iff_of_last_O G H hG hH hO K d c).mp hc p j hj
  have hsum : laurentMaslovDegree G j p.1 + laurentMaslovDegree H 0 p.2 = d := by
    simp only [laurentMaslovDegree] at hh ⊢
    omega
  rw [← hsum]
  apply tmul_mem_laurentTensorMaslovPiece
  · exact laurentMonomialGenerator_mem_laurentMaslovPiece G K j p.1
  · exact laurentMonomialGenerator_mem_laurentMaslovPiece H K 0 p.2

/-- The inverse tensor basis map preserves both convolved filtration bounds. -/
theorem seamTensorCoordinatesEquiv_symm_mem_bifiltration
    {u v : ℝ} {c : SeamRetainedCoordinates K n m}
    (hc : c ∈ seamRetainedBifiltrationLevel G H hG hH K u v) :
    (seamTensorCoordinatesEquiv K).symm c ∈ laurentTensorBifiltrationLevel G H u v := by
  refine seamCoordinates_mem_of_monomials
    ((seamTensorCoordinatesEquiv K).symm.toLinearMap.restrictScalars K) _ c ?_
  intro p j hj
  change (seamTensorCoordinatesEquiv K).symm (Pi.single p (LaurentPolynomial.T j)) ∈ _
  rw [seamTensorCoordinatesEquiv_symm_single]
  have hh := hc (seamState p.1 p.2) j
  change j ∈ ((seamCoordinateEquiv K).symm (c, (0, 0))
    (seamState p.1 p.2)).coeff.support → _ at hh
  rw [seamCoordinateEquiv_symm_retained] at hh
  have hh := hh hj
  have hA : ((connectedSumSeamGrid G H hG hH).alexander (seamState p.1 p.2) : ℝ) =
      (G.alexander p.1 : ℝ) + (H.alexander p.2 : ℝ) := by
    exact_mod_cast connectedSumSeamGrid_alexander_of_last_O G H hG hH hO p.1 p.2
  refine Submodule.subset_span ⟨-(j : ℝ), (G.alexander p.1 : ℝ) - j,
    0, (H.alexander p.2 : ℝ), _, _, seam_monomial_mem_bifiltration G j p.1, ?_, ?_, ?_, rfl⟩
  · simpa only [neg_zero, Int.cast_zero, sub_zero, LaurentPolynomial.T_zero] using
      seam_monomial_mem_bifiltration (K := K) H 0 p.2
  · simpa only [add_zero] using hh.1
  · rw [hA] at hh
    linarith [hh.2]

/-- A homogeneous tensor has exactly the retained sum grading in the prepared seam. -/
theorem seamTensorCoordinatesEquiv_mem_maslov {d : ℤ}
    {c : LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1)}
    (hc : c ∈ laurentTensorMaslovPiece G H d) :
    seamTensorCoordinatesEquiv K c ∈ seamRetainedMaslovPiece G H hG hH K d := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, b, x, y, hx, hy, hab, rfl⟩ := hc
    rw [mem_seamRetainedMaslovPiece_iff_of_last_O G H hG hH hO]
    intro p j hj
    rw [seamTensorCoordinatesEquiv_tmul_apply] at hj
    obtain ⟨k, hk, l, hl, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hj)
    have hx := hx p.1 k hk
    have hy := hy p.2 l hl
    change laurentMaslovDegree G k p.1 = a at hx
    change laurentMaslovDegree H l p.2 = b at hy
    simp only [laurentMaslovDegree] at hx hy
    omega
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add c e _ _ hc he => rw [map_add]; exact Submodule.add_mem _ hc he
  | smul a c _ hc =>
    change (seamTensorCoordinatesEquiv K).restrictScalars K (a • c) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hc



/-- Exact coefficient bounds on retained chains after the prepared grading comparison. -/
theorem mem_seamRetainedBifiltrationLevel_iff_of_last_O
    (u v : ℝ) (c : SeamRetainedCoordinates K n m) :
    c ∈ seamRetainedBifiltrationLevel G H hG hH K u v ↔
      ∀ p k, k ∈ (c p).coeff.support →
        -(k : ℝ) ≤ u ∧ (G.alexander p.1 : ℝ) + (H.alexander p.2 : ℝ) - k ≤ v := by
  have hA (p : SeamRetainedIndex n m) :
      ((connectedSumSeamGrid G H hG hH).alexander (seamState p.1 p.2) : ℝ) =
        (G.alexander p.1 : ℝ) + (H.alexander p.2 : ℝ) := by
    exact_mod_cast connectedSumSeamGrid_alexander_of_last_O G H hG hH hO p.1 p.2
  constructor
  · intro hc p k hk
    have hh := hc (seamState p.1 p.2) k
    change k ∈ ((seamCoordinateEquiv K).symm (c, (0, 0))
      (seamState p.1 p.2)).coeff.support → _ at hh
    rw [seamCoordinateEquiv_symm_retained] at hh
    simpa only [hA p] using hh hk
  · intro hc w k hk
    obtain ⟨a, rfl⟩ := seamThreeState_surjective w
    rcases a with p | x
    · change k ∈ ((seamCoordinateEquiv K).symm (c, (0, 0))
        (seamState p.1 p.2)).coeff.support at hk
      rw [seamCoordinateEquiv_symm_retained] at hk
      change -(k : ℝ) ≤ u ∧
        ((connectedSumSeamGrid G H hG hH).alexander (seamState p.1 p.2) : ℝ) - k ≤ v
      simpa only [hA p] using hc p k hk
    · rcases x with x | y
      · change k ∈ ((seamCoordinateEquiv K).symm (c, (0, 0)) x.val.val).coeff.support at hk
        rw [seamCoordinateEquiv_symm_source] at hk
        simp at hk
      · change k ∈ ((seamCoordinateEquiv K).symm (c, (0, 0))
          (seamComplementPartner y.val).val).coeff.support at hk
        rw [seamCoordinateEquiv_symm_target] at hk
        simp at hk

/-- The tensor coordinate map preserves the convolved filtration. -/
theorem seamTensorCoordinatesEquiv_mem_bifiltration {u v : ℝ}
    {c : LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1)}
    (hc : c ∈ laurentTensorBifiltrationLevel G H u v) :
    seamTensorCoordinatesEquiv K c ∈ seamRetainedBifiltrationLevel G H hG hH K u v := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨a, b, e, f, x, y, hx, hy, hau, hbv, rfl⟩ := hc
    rw [mem_seamRetainedBifiltrationLevel_iff_of_last_O G H hG hH hO]
    intro p j hj
    rw [seamTensorCoordinatesEquiv_tmul_apply] at hj
    obtain ⟨k, hk, l, hl, rfl⟩ :=
      Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset _ _ hj)
    have hx := hx p.1 k hk
    have hy := hy p.2 l hl
    push_cast
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add c e _ _ hc he => rw [map_add]; exact Submodule.add_mem _ hc he
  | smul a c _ hc =>
    change (seamTensorCoordinatesEquiv K).restrictScalars K (a • c) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hc

/-- Exact homogeneous-submodule correspondence under the balanced tensor basis map. -/
theorem seamTensorCoordinatesEquiv_maslov_iff (d : ℤ)
    (c : LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1)) :
    seamTensorCoordinatesEquiv K c ∈ seamRetainedMaslovPiece G H hG hH K d ↔
      c ∈ laurentTensorMaslovPiece G H d := by
  constructor
  · intro hc
    simpa only [LinearEquiv.symm_apply_apply] using
      seamTensorCoordinatesEquiv_symm_mem_maslov G H hG hH hO hc
  · exact seamTensorCoordinatesEquiv_mem_maslov G H hG hH hO

/-- Exact convolved-filtration correspondence under the balanced tensor basis map. -/
theorem seamTensorCoordinatesEquiv_bifiltration_iff (u v : ℝ)
    (c : LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1)) :
    seamTensorCoordinatesEquiv K c ∈ seamRetainedBifiltrationLevel G H hG hH K u v ↔
      c ∈ laurentTensorBifiltrationLevel G H u v := by
  constructor
  · intro hc
    simpa only [LinearEquiv.symm_apply_apply] using
      seamTensorCoordinatesEquiv_symm_mem_bifiltration G H hG hH hO hc
  · exact seamTensorCoordinatesEquiv_mem_bifiltration G H hG hH hO

end OnLeConjecture.KnotFloer.GridFull
