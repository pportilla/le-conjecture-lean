/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.LinearAlgebra.Prod

/-!
# Codimension identities for linear maps

For a linear map `L : X → V` and a subspace `B` of `X`, the codimension of
`L(B)` in `V` is the codimension of the range of `L` plus the codimension of
`B ⊔ ker L` in `X`. For two linear maps `α : X → Y` and `β : X → Z`, the
codimension of the range of `x ↦ (α x, β x)` is the sum of the
codimensions of the two ranges and the codimension of `ker α ⊔ ker β`.
Finite dimensionality of each quotient on the right gives finite
dimensionality of the quotient on the left.
-/

@[expose] public section

namespace OnLeConjecture.DeltaLinearAlgebra

open Module

variable {K X Y Z V : Type*} [Field K] [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
  [AddCommGroup V] [Module K V]

/-- Codimension of the image of a subspace under a linear map. -/
theorem finiteDimensional_and_finrank_quotient_map (L : X →ₗ[K] V) (B : Submodule K X)
    (hV : FiniteDimensional K (V ⧸ LinearMap.range L))
    (hX : FiniteDimensional K (X ⧸ (B ⊔ LinearMap.ker L))) :
    FiniteDimensional K (V ⧸ B.map L) ∧
      finrank K (V ⧸ B.map L) =
        finrank K (V ⧸ LinearMap.range L) + finrank K (X ⧸ (B ⊔ LinearMap.ker L)) := by
  have hle : B.map L ≤ LinearMap.range L := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  let A := B.map L
  let W : Submodule K (V ⧸ A) := (LinearMap.range L).map A.mkQ
  have hW : LinearMap.range (A.mkQ ∘ₗ L) = W := LinearMap.range_comp L A.mkQ
  have hker : LinearMap.ker (A.mkQ ∘ₗ L) = B ⊔ LinearMap.ker L := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_map_eq]
  let e₁ : ((V ⧸ A) ⧸ W) ≃ₗ[K] V ⧸ LinearMap.range L :=
    Submodule.quotientQuotientEquivQuotient A _ hle
  let e₂ : (X ⧸ (B ⊔ LinearMap.ker L)) ≃ₗ[K] W :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((A.mkQ ∘ₗ L).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hW))
  have hWfin : FiniteDimensional K W := e₂.finiteDimensional
  have hQfin : FiniteDimensional K ((V ⧸ A) ⧸ W) := e₁.symm.finiteDimensional
  have hfin : FiniteDimensional K (V ⧸ A) := Module.Finite.of_submodule_quotient W
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank W
  rw [e₁.finrank_eq, ← e₂.finrank_eq] at h
  change finrank K (V ⧸ A) = _
  omega

/-- An element `(α x, 0)` lies in the range of `x ↦ (α x, β x)` exactly
when `x ∈ ker α ⊔ ker β`. -/
theorem inl_mem_range_prod_iff (α : X →ₗ[K] Y) (β : X →ₗ[K] Z) (x : X) :
    (α x, (0 : Z)) ∈ LinearMap.range (α.prod β) ↔
      x ∈ LinearMap.ker α ⊔ LinearMap.ker β := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 : α w = α x := congrArg Prod.fst hw
    have h2 : β w = 0 := congrArg Prod.snd hw
    rw [Submodule.mem_sup]
    refine ⟨x - w, ?_, w, ?_, by abel⟩
    · rw [LinearMap.mem_ker, map_sub, h1, sub_self]
    · exact h2
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨b, ?_⟩
    rw [LinearMap.mem_ker] at ha hb
    simp [ha, hb]

/-- Codimension of the range of a product of two linear maps. -/
theorem finiteDimensional_and_finrank_quotient_range_prod (α : X →ₗ[K] Y) (β : X →ₗ[K] Z)
    (hα : FiniteDimensional K (Y ⧸ LinearMap.range α))
    (hβ : FiniteDimensional K (Z ⧸ LinearMap.range β))
    (hX : FiniteDimensional K (X ⧸ (LinearMap.ker α ⊔ LinearMap.ker β))) :
    FiniteDimensional K ((Y × Z) ⧸ LinearMap.range (α.prod β)) ∧
      finrank K ((Y × Z) ⧸ LinearMap.range (α.prod β)) =
        finrank K (Y ⧸ LinearMap.range α) + finrank K (Z ⧸ LinearMap.range β) +
          finrank K (X ⧸ (LinearMap.ker α ⊔ LinearMap.ker β)) := by
  let A := LinearMap.range (α.prod β)
  let R : Submodule K (Y × Z) := (LinearMap.range α).prod (LinearMap.range β)
  have hle : A ≤ R := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
  let W : Submodule K ((Y × Z) ⧸ A) := R.map A.mkQ
  let Φ : X →ₗ[K] (Y × Z) ⧸ A := A.mkQ ∘ₗ (LinearMap.inl K Y Z) ∘ₗ α
  have hΦ : LinearMap.range Φ = W := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(α x, 0), ⟨⟨x, rfl⟩, Submodule.zero_mem _⟩, rfl⟩
    · rintro _ ⟨⟨y, z⟩, ⟨⟨x, rfl⟩, ⟨x', rfl⟩⟩, rfl⟩
      refine ⟨x - x', ?_⟩
      change A.mkQ (α (x - x'), 0) = A.mkQ (α x, β x')
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      refine ⟨-x', ?_⟩
      ext <;> simp
  have hker : LinearMap.ker Φ = LinearMap.ker α ⊔ LinearMap.ker β := by
    ext x
    rw [LinearMap.mem_ker]
    change A.mkQ (α x, 0) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact inl_mem_range_prod_iff α β x
  let e₁ : (((Y × Z) ⧸ A) ⧸ W) ≃ₗ[K] ((Y × Z) ⧸ R) :=
    Submodule.quotientQuotientEquivQuotient A R hle
  let e₂ : (X ⧸ (LinearMap.ker α ⊔ LinearMap.ker β)) ≃ₗ[K] W :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (Φ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hΦ))
  let P : Y × Z →ₗ[K] (Y ⧸ LinearMap.range α) × (Z ⧸ LinearMap.range β) :=
    (LinearMap.range α).mkQ.prodMap (LinearMap.range β).mkQ
  have hPsurj : Function.Surjective P := by
    rintro ⟨y, z⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨(y, z), rfl⟩
  have hPker : LinearMap.ker P = R := by
    rw [LinearMap.ker_prodMap, Submodule.ker_mkQ, Submodule.ker_mkQ]
  let e₃ : ((Y × Z) ⧸ R) ≃ₗ[K] (Y ⧸ LinearMap.range α) × (Z ⧸ LinearMap.range β) :=
    (Submodule.quotEquivOfEq _ _ hPker.symm).trans (P.quotKerEquivOfSurjective hPsurj)
  have hWfin : FiniteDimensional K W := e₂.finiteDimensional
  have hQfin : FiniteDimensional K (((Y × Z) ⧸ A) ⧸ W) :=
    (e₁.trans e₃).symm.finiteDimensional
  have hfin : FiniteDimensional K ((Y × Z) ⧸ A) := Module.Finite.of_submodule_quotient W
  refine ⟨hfin, ?_⟩
  have h := Submodule.finrank_quotient_add_finrank W
  rw [(e₁.trans e₃).finrank_eq, Module.finrank_prod, ← e₂.finrank_eq] at h
  change finrank K ((Y × Z) ⧸ A) = _
  omega

end OnLeConjecture.DeltaLinearAlgebra
