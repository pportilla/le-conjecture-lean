/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorSingleton

/-!
# Reindexing the finite tensor of native grid complexes

An equivalence `e : ι ≃ ι'` of finite index types induces, through Mathlib's
`PiTensorProduct.reindex`, an isomorphism between the finite tensor complex of a
family `D` and that of the reindexed family `fun i' => D (e.symm i')`. Both directions
have shifts `(0,0)`, and the isomorphism carries the canonical finite tensor class to
the canonical finite tensor class of the reindexed family (M610).

A family of grid diagrams whose sizes depend on the index is also compared with a
propositionally equal family, presented through the sigma type of sized grids. This
transport is used for size casts.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct CategoryTheory HomologicalComplex

section Reindex

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- Reindexing of the underlying finite tensors, as a linear equivalence over the coefficients. -/
def laurentFiniteReindexEquiv :
    LaurentFiniteTensor (K := K) (n := n) ≃ₗ[K]
      LaurentFiniteTensor (K := K) (n := fun i' => n (e.symm i')) :=
  (PiTensorProduct.reindex (LaurentPolynomial K) (fun i => LaurentChain K (n i)) e).restrictScalars
    K

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
theorem laurentFiniteReindexEquiv_apply (z : LaurentFiniteTensor (K := K) (n := n)) :
    laurentFiniteReindexEquiv e z =
      PiTensorProduct.reindex (LaurentPolynomial K) (fun i => LaurentChain K (n i)) e z := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- Reindexing a scaled pure tensor. -/
theorem laurentFiniteReindexEquiv_smul_tprod (j : ℤ) (x : ∀ i, LaurentChain K (n i)) :
    laurentFiniteReindexEquiv e
        ((LaurentPolynomial.T j : LaurentPolynomial K) • tprod (LaurentPolynomial K) x) =
      (LaurentPolynomial.T j : LaurentPolynomial K) •
        tprod (LaurentPolynomial K) (fun i' => x (e.symm i')) := by
  rw [laurentFiniteReindexEquiv_apply, map_smul, reindex_tprod]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- Every pure tensor of the reindexed family is the reindexing of a pure tensor. -/
theorem laurentFiniteReindexEquiv_symm_smul_tprod (j : ℤ)
    (y : ∀ i', LaurentChain K (n (e.symm i'))) :
    (laurentFiniteReindexEquiv (K := K) e).symm
        ((LaurentPolynomial.T j : LaurentPolynomial K) • tprod (LaurentPolynomial K) y) =
      (LaurentPolynomial.T j : LaurentPolynomial K) • tprod (LaurentPolynomial K)
        ((Equiv.piCongrLeft' (fun i => LaurentChain K (n i)) e).symm y) := by
  rw [LinearEquiv.symm_apply_eq, laurentFiniteReindexEquiv_smul_tprod]
  congr 2
  funext i'
  exact (Equiv.piCongrLeft'_symm_apply_apply (fun i => LaurentChain K (n i)) e y i').symm

omit [DecidableEq ι] [DecidableEq ι'] in
/-- Reindexing preserves and reflects every finite Maslov piece. -/
theorem laurentFiniteReindexEquiv_mem_maslovPiece_iff (r : ℤ)
    (z : LaurentFiniteTensor (K := K) (n := n)) :
    laurentFiniteReindexEquiv e z ∈ laurentFiniteMaslovPiece (fun i' => G (e.symm i')) r ↔
      z ∈ laurentFiniteMaslovPiece G r := by
  constructor
  · intro h
    rw [← (laurentFiniteReindexEquiv (K := K) e).symm_apply_apply z]
    generalize laurentFiniteReindexEquiv e z = w at h
    induction h using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, p, y, hy, hr, rfl⟩ := hw
      rw [laurentFiniteReindexEquiv_symm_smul_tprod]
      apply Submodule.subset_span
      refine ⟨j, fun i => p (e i), _, fun i => ?_, ?_, rfl⟩
      · obtain ⟨i', rfl⟩ := e.symm.surjective i
        rw [Equiv.piCongrLeft'_symm_apply_apply]
        simpa only [Equiv.apply_symm_apply] using hy i'
      · rw [← hr, Equiv.sum_comp e p]
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => simpa using Submodule.add_mem _ hw hw'
    | smul a w _ hw => simpa using Submodule.smul_mem _ a hw
  · intro h
    induction h using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, p, x, hx, hr, rfl⟩ := hz
      rw [laurentFiniteReindexEquiv_smul_tprod]
      apply Submodule.subset_span
      refine ⟨j, fun i' => p (e.symm i'), _, fun i' => hx (e.symm i'), ?_, rfl⟩
      rw [← hr, Equiv.sum_comp e.symm p]
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
    | smul a z _ hz => simpa using Submodule.smul_mem _ a hz

omit [DecidableEq ι] [DecidableEq ι'] in
/-- Reindexing preserves and reflects every finite filtration level. -/
theorem laurentFiniteReindexEquiv_mem_bifiltrationLevel_iff (a b : ℝ)
    (z : LaurentFiniteTensor (K := K) (n := n)) :
    laurentFiniteReindexEquiv e z ∈
        laurentFiniteBifiltrationLevel (fun i' => G (e.symm i')) a b ↔
      z ∈ laurentFiniteBifiltrationLevel G a b := by
  constructor
  · intro h
    rw [← (laurentFiniteReindexEquiv (K := K) e).symm_apply_apply z]
    generalize laurentFiniteReindexEquiv e z = w at h
    induction h using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, u, v, y, hy, hA, hB, rfl⟩ := hw
      rw [laurentFiniteReindexEquiv_symm_smul_tprod]
      apply Submodule.subset_span
      refine ⟨j, fun i => u (e i), fun i => v (e i), _, fun i => ?_, ?_, ?_, rfl⟩
      · obtain ⟨i', rfl⟩ := e.symm.surjective i
        rw [Equiv.piCongrLeft'_symm_apply_apply]
        simpa only [Equiv.apply_symm_apply] using hy i'
      · rwa [Equiv.sum_comp e u]
      · rwa [Equiv.sum_comp e v]
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => simpa using Submodule.add_mem _ hw hw'
    | smul c w _ hw => simpa using Submodule.smul_mem _ c hw
  · intro h
    induction h using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, u, v, x, hx, hA, hB, rfl⟩ := hz
      rw [laurentFiniteReindexEquiv_smul_tprod]
      apply Submodule.subset_span
      refine ⟨j, fun i' => u (e.symm i'), fun i' => v (e.symm i'), _,
        fun i' => hx (e.symm i'), ?_, ?_, rfl⟩
      · rwa [Equiv.sum_comp e.symm u]
      · rwa [Equiv.sum_comp e.symm v]
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
    | smul c z _ hz => simpa using Submodule.smul_mem _ c hz

omit [Fintype ι] [Fintype ι'] [DecidableEq ι'] in
private theorem update_comp_symm {β : ι → Type*} (x : ∀ i, β i) (i' : ι') (v : β (e.symm i'))
    [DecidableEq ι'] :
    (fun k => Function.update x (e.symm i') v (e.symm k)) =
      Function.update (fun k => x (e.symm k)) i' v := by
  funext k
  by_cases h : k = i'
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne (e.symm.injective.ne h)]

/-- Reindexing intertwines the finite tensor differentials. -/
theorem laurentFiniteReindexEquiv_differential (z : LaurentFiniteTensor (K := K) (n := n)) :
    laurentFiniteReindexEquiv e (laurentFiniteDifferential G z) =
      laurentFiniteDifferential (fun i' => G (e.symm i')) (laurentFiniteReindexEquiv e z) := by
  have h : (PiTensorProduct.reindex (LaurentPolynomial K) (fun i => LaurentChain K (n i))
      e).toLinearMap ∘ₗ laurentFiniteDifferential (K := K) G =
      laurentFiniteDifferential (fun i' => G (e.symm i')) ∘ₗ
        (PiTensorProduct.reindex (LaurentPolynomial K) (fun i => LaurentChain K (n i))
          e).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      laurentFiniteDifferential_tprod, map_sum, reindex_tprod]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [update_comp_symm e x i']
  exact LinearMap.congr_fun h z

variable [CharP K 2]

/-- Reindexing gives an isomorphism of finite tensor complexes. -/
def laurentFiniteMaslovReindexIso :
    laurentFiniteMaslovComplex (K := K) G ≅
      laurentFiniteMaslovComplex (K := K) (fun i' => G (e.symm i')) :=
  (laurentFinitePieceData G).iso (laurentFinitePieceData (fun i' => G (e.symm i')))
    (laurentFiniteReindexEquiv e)
    (fun r z => laurentFiniteReindexEquiv_mem_maslovPiece_iff e G r z)
    (fun z => laurentFiniteReindexEquiv_differential e G z)

/-- On underlying tensors, the reindexing isomorphism is Mathlib's reindexing. -/
theorem laurentFiniteMaslovReindexIso_hom_apply (r : ℤ)
    (z : (laurentFiniteMaslovComplex (K := K) G).X r) :
    (laurentFiniteMaslovChainEquiv (fun i' => G (e.symm i')) r
        ((laurentFiniteMaslovReindexIso e G).hom.f r z) :
          LaurentFiniteTensor (K := K) (n := fun i' => n (e.symm i'))) =
      PiTensorProduct.reindex (LaurentPolynomial K) (fun i => LaurentChain K (n i)) e
        (laurentFiniteMaslovChainEquiv G r z : LaurentFiniteTensor (K := K) (n := n)) :=
  PieceComplexData.iso_hom_apply _ _ _ _ _ r z

/-- The reindexing isomorphism has shifts `(0,0)`. -/
theorem laurentFiniteMaslovReindexIso_hom_shifts :
    (laurentFiniteMaslovBifiltration G).Shifts
      (laurentFiniteMaslovBifiltration (fun i' => G (e.symm i')))
      (laurentFiniteMaslovReindexIso (K := K) e G).hom 0 0 :=
  PieceComplexData.iso_hom_shifts (laurentFinitePieceData G)
    (laurentFinitePieceData (fun i' => G (e.symm i'))) _ _ _
    (fun a b z hz => (laurentFiniteReindexEquiv_mem_bifiltrationLevel_iff e G a b z).mpr hz)

/-- The inverse reindexing isomorphism has shifts `(0,0)`. -/
theorem laurentFiniteMaslovReindexIso_inv_shifts :
    (laurentFiniteMaslovBifiltration (fun i' => G (e.symm i'))).Shifts
      (laurentFiniteMaslovBifiltration G)
      (laurentFiniteMaslovReindexIso (K := K) e G).inv 0 0 :=
  PieceComplexData.iso_inv_shifts (laurentFinitePieceData G)
    (laurentFinitePieceData (fun i' => G (e.symm i'))) _ _ _
    (fun a b w hw => (laurentFiniteReindexEquiv_mem_bifiltrationLevel_iff e G a b _).mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact hw))

end Reindex

section ReindexCanonical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
variable {sizes : ι → ℕ} (D : ∀ i, GridDiagram (sizes i)) (hD : ∀ i, 2 ≤ sizes i)

/-- Reindexing carries the selected finite native cycle to the reindexed selected cycle. -/
theorem laurentFiniteMaslovReindexIso_hom_canonicalCycle :
    (laurentFiniteMaslovReindexIso (K := ZMod 2) e D).hom.f 0
        ((laurentFiniteMaslovComplex (K := ZMod 2) D).iCycles 0
          (laurentFiniteNativeCycle D (fun i => gridCanonicalCycle (D i) (hD i)))) =
      (laurentFiniteMaslovComplex (K := ZMod 2) (fun i' => D (e.symm i'))).iCycles 0
        (laurentFiniteNativeCycle (fun i' => D (e.symm i'))
          (fun i' => gridCanonicalCycle (D (e.symm i')) (hD (e.symm i')))) := by
  rw [laurentFiniteNativeCycle_iCycles, laurentFiniteNativeCycle_iCycles]
  apply (laurentFiniteMaslovChainEquiv (fun i' => D (e.symm i')) 0).injective
  apply Subtype.ext
  rw [laurentFiniteMaslovReindexIso_hom_apply]
  simp only [laurentFiniteNativeChain, LinearEquiv.apply_symm_apply, reindex_tprod]

/-- Reindexing carries the canonical finite tensor class to the reindexed canonical class. -/
theorem laurentFiniteMaslovReindexIso_hom_canonicalClass :
    homologyMap (laurentFiniteMaslovReindexIso (K := ZMod 2) e D).hom 0
        (gridCanonicalFiniteTensorClass D hD) =
      gridCanonicalFiniteTensorClass (fun i' => D (e.symm i')) (fun i' => hD (e.symm i')) :=
  homologyMap_homologyπ_eq_of_iCycles _ _ _
    (laurentFiniteMaslovReindexIso_hom_canonicalCycle e D hD)

/-- The inverse reindexing isomorphism carries the reindexed canonical class back. -/
theorem laurentFiniteMaslovReindexIso_inv_canonicalClass :
    homologyMap (laurentFiniteMaslovReindexIso (K := ZMod 2) e D).inv 0
        (gridCanonicalFiniteTensorClass (fun i' => D (e.symm i')) (fun i' => hD (e.symm i'))) =
      gridCanonicalFiniteTensorClass D hD := by
  rw [← laurentFiniteMaslovReindexIso_hom_canonicalClass e D hD,
    ← ModuleCat.comp_apply, ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id]
  rfl

end ReindexCanonical

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [CharP K 2]

/-- Equal families of sized grid diagrams have isomorphic finite tensor complexes. -/
def laurentFiniteMaslovFamilyIso {F₁ F₂ : ι → Σ n, GridDiagram n} (h : F₁ = F₂) :
    laurentFiniteMaslovComplex (K := K) (fun i => (F₁ i).2) ≅
      laurentFiniteMaslovComplex (K := K) (fun i => (F₂ i).2) :=
  eqToIso (by rw [h])

/-- The family transport has shifts `(0,0)`. -/
theorem laurentFiniteMaslovFamilyIso_hom_shifts {F₁ F₂ : ι → Σ n, GridDiagram n}
    (h : F₁ = F₂) :
    (laurentFiniteMaslovBifiltration (K := K) (fun i => (F₁ i).2)).Shifts
      (laurentFiniteMaslovBifiltration (fun i => (F₂ i).2))
      (laurentFiniteMaslovFamilyIso h).hom 0 0 := by
  subst h
  intro a b r x hx
  simpa [laurentFiniteMaslovFamilyIso] using hx

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The family transport carries the canonical finite tensor class to the canonical class. -/
theorem laurentFiniteMaslovFamilyIso_hom_canonicalClass {F₁ F₂ : ι → Σ n, GridDiagram n}
    (h : F₁ = F₂) (hD₁ : ∀ i, 2 ≤ (F₁ i).1) (hD₂ : ∀ i, 2 ≤ (F₂ i).1) :
    homologyMap (laurentFiniteMaslovFamilyIso (K := ZMod 2) h).hom 0
        (gridCanonicalFiniteTensorClass (fun i => (F₁ i).2) hD₁) =
      gridCanonicalFiniteTensorClass (fun i => (F₂ i).2) hD₂ := by
  subst h
  simp [laurentFiniteMaslovFamilyIso]

end Family

end OnLeConjecture.KnotFloer.GridFull
