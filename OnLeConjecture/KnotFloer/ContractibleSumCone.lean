/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.TauCeti.Algebra.Homology.SquareZero
import Mathlib.Tactic.Abel

/-!
# Explicit inverse maps extracted from a contracting comparison cone

The inverse is the upper-right component of the specified contracting homotopy.
The diagonal components give the two inverse homotopies. Thus the construction
retains the actual map and its support, rather than selecting a homology isomorphism.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.ContractibleSumCone

open Finsupp

variable {S ι κ : Type*} [CommRing S]

/-- Write the specified cone homotopy on the product of its two summands. -/
noncomputable def productHomotopy (H : Module.End S ((ι ⊕ κ) →₀ S)) :
    Module.End S ((ι →₀ S) × (κ →₀ S)) :=
  (sumFinsuppLEquivProdFinsupp S).toLinearMap ∘ₗ H ∘ₗ
    (sumFinsuppLEquivProdFinsupp S).symm.toLinearMap

@[simp]
theorem productHomotopy_apply (H : Module.End S ((ι ⊕ κ) →₀ S))
    (z : (ι →₀ S) × (κ →₀ S)) :
    productHomotopy H z = (sumFinsuppLEquivProdFinsupp S)
      (H ((sumFinsuppLEquivProdFinsupp S).symm z)) := rfl


/-- The square-zero side condition is preserved when the cone homotopy is written on a product. -/
theorem productHomotopy_comp_self (H : Module.End S ((ι ⊕ κ) →₀ S))
    (hH : H ∘ₗ H = 0) (z : (ι →₀ S) × (κ →₀ S)) :
    productHomotopy H (productHomotopy H z) = 0 := by
  simp only [productHomotopy_apply, LinearEquiv.symm_apply_apply]
  have hz := LinearMap.congr_fun hH ((sumFinsuppLEquivProdFinsupp S).symm z)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
  rw [hz, map_zero]

/-- The upper-right component, giving the concrete reverse comparison. -/
noncomputable def backward (H : Module.End S ((ι ⊕ κ) →₀ S)) : (κ →₀ S) →ₗ[S] (ι →₀ S) :=
  LinearMap.fst S _ _ ∘ₗ productHomotopy H ∘ₗ LinearMap.inr S _ _

/-- The upper-left component, giving the first inverse homotopy. -/
noncomputable def leftHomotopy (H : Module.End S ((ι ⊕ κ) →₀ S)) : Module.End S (ι →₀ S) :=
  LinearMap.fst S _ _ ∘ₗ productHomotopy H ∘ₗ LinearMap.inl S _ _

/-- The lower-right component, giving the second inverse homotopy. -/
noncomputable def rightHomotopy (H : Module.End S ((ι ⊕ κ) →₀ S)) : Module.End S (κ →₀ S) :=
  LinearMap.snd S _ _ ∘ₗ productHomotopy H ∘ₗ LinearMap.inr S _ _


/-- A single generator in the first summand remains that generator under the sum equivalence. -/
theorem sumEquiv_symm_single_left (i : ι) (a : S) :
    (sumFinsuppLEquivProdFinsupp S).symm ((single i a), (0 : κ →₀ S)) =
      single (.inl i) a := by
  classical
  apply Finsupp.ext
  intro q
  cases q <;> simp [Finsupp.single_apply]

/-- A single generator in the second summand remains that generator under the sum equivalence. -/
theorem sumEquiv_symm_single_right (j : κ) (a : S) :
    (sumFinsuppLEquivProdFinsupp S).symm ((0 : ι →₀ S), (single j a)) =
      single (.inr j) a := by
  classical
  apply Finsupp.ext
  intro q
  cases q <;> simp [Finsupp.single_apply]

/-- A reverse-comparison matrix coefficient is the corresponding cone homotopy coefficient. -/
theorem backward_single_apply (H : Module.End S ((ι ⊕ κ) →₀ S)) (j : κ) (i : ι) (a : S) :
    backward H (single j a) i = H (single (.inr j) a) (.inl i) := by
  simp only [backward, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inr_apply,
    productHomotopy_apply, sumEquiv_symm_single_right, fst_sumFinsuppLEquivProdFinsupp]

/-- The first inverse homotopy is the upper-left matrix component. -/
theorem leftHomotopy_single_apply (H : Module.End S ((ι ⊕ κ) →₀ S)) (i j : ι) (a : S) :
    leftHomotopy H (single i a) j = H (single (.inl i) a) (.inl j) := by
  simp only [leftHomotopy, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inl_apply,
    productHomotopy_apply, sumEquiv_symm_single_left, fst_sumFinsuppLEquivProdFinsupp]

/-- The second inverse homotopy is the lower-right matrix component. -/
theorem rightHomotopy_single_apply (H : Module.End S ((ι ⊕ κ) →₀ S)) (i j : κ) (a : S) :
    rightHomotopy H (single i a) j = H (single (.inr i) a) (.inr j) := by
  simp only [rightHomotopy, LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.inr_apply,
    productHomotopy_apply, sumEquiv_symm_single_right, snd_sumFinsuppLEquivProdFinsupp]

variable (d : Module.End S (ι →₀ S)) (e : Module.End S (κ →₀ S))
  (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) (H : Module.End S ((ι ⊕ κ) →₀ S))
  (hH : LinearMap.sumMappingCone d e f ∘ₗ H + H ∘ₗ LinearMap.sumMappingCone d e f = LinearMap.id)

include hH

/-- Transporting the given contracting equation to the product loses no information. -/
theorem productHomotopy_contracts (z : (ι →₀ S) × (κ →₀ S)) :
    LinearMap.mappingCone d e f (productHomotopy H z) +
      productHomotopy H (LinearMap.mappingCone d e f z) = z := by
  have h := congrArg (sumFinsuppLEquivProdFinsupp S)
    (LinearMap.congr_fun hH ((sumFinsuppLEquivProdFinsupp S).symm z))
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add,
    LinearMap.sumMappingCone_apply, LinearEquiv.apply_symm_apply,
    productHomotopy_apply] using h

/-- The extracted reverse comparison is a chain map. -/
theorem backward_chain : d ∘ₗ backward H = backward H ∘ₗ e := by
  apply LinearMap.ext
  intro y
  have h := congrArg Prod.fst (productHomotopy_contracts d e f H hH (0, y))
  simp only [LinearMap.mappingCone_apply, Prod.fst_add, map_zero, neg_zero, zero_add] at h
  change -d (backward H y) + backward H (e y) = 0 at h
  change d (backward H y) = backward H (e y)
  exact neg_add_eq_zero.mp h

/-- The first composite differs from the identity by the first explicitly extracted homotopy. -/
theorem backward_forward :
    backward H ∘ₗ f - LinearMap.id = d ∘ₗ leftHomotopy H + leftHomotopy H ∘ₗ d := by
  apply LinearMap.ext
  intro x
  have h := congrArg Prod.fst (productHomotopy_contracts d e f H hH (x, 0))
  have hsplit : (-d x, f x + e 0) = (-d x, 0) + (0, f x) := by simp
  simp only [LinearMap.mappingCone_apply] at h
  rw [hsplit, map_add] at h
  simp only [Prod.fst_add] at h
  have hneg : (productHomotopy H (-d x, 0)).1 = -leftHomotopy H (d x) := by
    have hpair : (-d x, (0 : κ →₀ S)) = -(d x, 0) := by simp
    rw [hpair, map_neg]
    rfl
  rw [hneg] at h
  change -d (leftHomotopy H x) + (-leftHomotopy H (d x) + backward H (f x)) = x at h
  change backward H (f x) - x = d (leftHomotopy H x) + leftHomotopy H (d x)
  calc
    _ = backward H (f x) -
        (-d (leftHomotopy H x) + (-leftHomotopy H (d x) + backward H (f x))) := by rw [h]
    _ = _ := by abel

/-- The second composite differs from the identity by the second extracted homotopy. -/
theorem forward_backward :
    LinearMap.id - f ∘ₗ backward H = e ∘ₗ rightHomotopy H + rightHomotopy H ∘ₗ e := by
  apply LinearMap.ext
  intro y
  have h := congrArg Prod.snd (productHomotopy_contracts d e f H hH (0, y))
  simp only [LinearMap.mappingCone_apply, Prod.snd_add, map_zero, neg_zero, zero_add] at h
  change f (backward H y) + e (rightHomotopy H y) + rightHomotopy H (e y) = y at h
  change y - f (backward H y) = e (rightHomotopy H y) + rightHomotopy H (e y)
  calc
    _ = (f (backward H y) + e (rightHomotopy H y) + rightHomotopy H (e y)) -
        f (backward H y) := by rw [h]
    _ = _ := by abel

end OnLeConjecture.KnotFloer.ContractibleSumCone
