/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DifferentialTopology.RationalCurveHomology

/-!
# The Mayer–Vietoris count for one open piece

Let `X = U ∪ V` with `U` and `V` open. If `X`, `V` and `U ∩ V` have curve homology
with Euler characteristics `a`, `b` and `c`, then `U` has curve homology with Euler
characteristic `a + c − b` (`HasCurveRatHomology.of_mayerVietoris_complement`).

In degrees `n ≥ 2` the exact sequence `H_n(U ∩ V) → H_n(U) ⊕ H_n(V) → H_n(X)` has
both ends zero, so `H_n(U) = 0`. In low degrees the rational Mayer–Vietoris sequence
gives the exact sequence
`0 → H₁(U ∩ V) → H₁(U) ⊕ H₁(V) → H₁(X) → H₀(U ∩ V) → H₀(U) ⊕ H₀(V) → H₀(X) → 0`,
where injectivity on the left follows from `H₂(X) = 0`. A dimension count along this
sequence (`exact_six_finrank`) gives finiteness of `H₀(U)` and `H₁(U)` and the Euler
characteristic.

We also give versions for subsets of an ambient space `Z`: the subspaces `U` and `V`
of a subspace `X` are given as intersections of `X` with open subsets of `Z`
(`HasCurveRatHomology.of_mayerVietoris_complement_subset` and
`HasCurveRatHomology.mayerVietoris_subset`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace OnLeConjecture.DifferentialTopology

open OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

section LinearAlgebra

variable {A₁ B₁ C₁ A₀ B₀ C₀ : Type*}
  [AddCommGroup A₁] [Module ℚ A₁] [AddCommGroup B₁] [Module ℚ B₁]
  [AddCommGroup C₁] [Module ℚ C₁] [AddCommGroup A₀] [Module ℚ A₀]
  [AddCommGroup B₀] [Module ℚ B₀] [AddCommGroup C₀] [Module ℚ C₀]

/-- Dimension count along an exact sequence
`0 → A₁ → B₁ → C₁ → A₀ → B₀ → C₀ → 0` of rational vector spaces with `A₁`, `C₁`,
`A₀` and `C₀` finite dimensional. Then `B₁` and `B₀` are finite dimensional and
`dim B₀ − dim B₁ = (dim C₀ − dim C₁) + (dim A₀ − dim A₁)`. -/
theorem exact_six_finrank (α : A₁ →ₗ[ℚ] B₁) (β : B₁ →ₗ[ℚ] C₁) (γ : C₁ →ₗ[ℚ] A₀)
    (δ : A₀ →ₗ[ℚ] B₀) (σ : B₀ →ₗ[ℚ] C₀) (hα : Function.Injective α)
    (hαβ : LinearMap.range α = LinearMap.ker β) (hβγ : LinearMap.range β = LinearMap.ker γ)
    (hγδ : LinearMap.range γ = LinearMap.ker δ) (hδσ : LinearMap.range δ = LinearMap.ker σ)
    (hσ : Function.Surjective σ) [Module.Finite ℚ A₁] [Module.Finite ℚ C₁]
    [Module.Finite ℚ A₀] [Module.Finite ℚ C₀] :
    Module.Finite ℚ B₁ ∧ Module.Finite ℚ B₀ ∧
      (Module.finrank ℚ B₀ : ℤ) - Module.finrank ℚ B₁ =
        ((Module.finrank ℚ C₀ : ℤ) - Module.finrank ℚ C₁) +
          ((Module.finrank ℚ A₀ : ℤ) - Module.finrank ℚ A₁) := by
  have hB₁ : Module.Finite ℚ B₁ := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker β ?_ ?_⟩
    · exact Module.Finite.iff_fg.mp inferInstance
    · rw [top_inf_eq, ← hαβ, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map α
  have hB₀ : Module.Finite ℚ B₀ := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker σ ?_ ?_⟩
    · exact Module.Finite.iff_fg.mp inferInstance
    · rw [top_inf_eq, ← hδσ, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map δ
  refine ⟨hB₁, hB₀, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker β
  have h2 := LinearMap.finrank_range_add_finrank_ker γ
  have h3 := LinearMap.finrank_range_add_finrank_ker δ
  have h4 := LinearMap.finrank_range_add_finrank_ker σ
  have hrα : Module.finrank ℚ (LinearMap.range α) = Module.finrank ℚ A₁ :=
    LinearMap.finrank_range_of_inj hα
  rw [← hαβ, hrα] at h1
  rw [← hβγ] at h2
  rw [← hγδ] at h3
  rw [← hδσ, LinearMap.range_eq_top.mpr hσ, finrank_top] at h4
  omega

end LinearAlgebra

section Biproduct

/-- The first summand of a finite dimensional binary biproduct is finite dimensional. -/
theorem module_finite_biprod_left {M N : ModuleCat.{0} ℚ} (h : Module.Finite ℚ ↑(M ⊞ N)) :
    Module.Finite ℚ M := by
  have e := (ModuleCat.biprodIsoProd M N).toLinearEquiv
  have := h
  have : Module.Finite ℚ (M × N) := Module.Finite.equiv e
  exact Module.Finite.of_surjective (LinearMap.fst ℚ M N) LinearMap.fst_surjective

/-- If a binary biproduct is zero, then so is its first summand. -/
theorem isZero_biprod_left {M N : ModuleCat.{0} ℚ} (h : IsZero (M ⊞ N)) : IsZero M :=
  h.of_mono biprod.inl

end Biproduct

section MayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- **Mayer–Vietoris count for one open piece.** Let `X = U ∪ V` with `U` and `V`
open. If `X`, `V` and `U ∩ V` have curve homology with Euler characteristics `a`, `b`
and `c`, then `U` has curve homology with Euler characteristic `a + c − b`. -/
theorem HasCurveRatHomology.of_mayerVietoris_complement (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) {a b c : ℤ}
    (hX : HasCurveRatHomology X a) (hVh : HasCurveRatHomology V b)
    (hUV : HasCurveRatHomology (U ∩ V : Set X) c) :
    HasCurveRatHomology U (a + c - b) := by
  let T : TopCat.{0} := TopCat.of X
  have hUo : IsOpen (U : Set T) := hU
  have hVo : IsOpen (V : Set T) := hV
  -- vanishing of the sum in degrees at least two
  have hsum : ∀ n, 2 ≤ n → IsZero (ratH U n ⊞ ratH V n) := by
    intro n hn
    have hex := rationalMayerVietoris_exact_middle T U V hUo hVo hcover n
    have hA : IsZero (ratH (U ∩ V : Set X) n) := hUV.isZero n hn
    have hC : IsZero (ratH X n) := hX.isZero n hn
    exact hex.isZero_X₂ (hA.eq_of_src _ _) (hC.eq_of_tgt _ _)
  have hvan : ∀ n, 2 ≤ n → IsZero (ratH U n) := fun n hn => isZero_biprod_left (hsum n hn)
  -- the six term exact sequence in degrees one and zero
  have hfX0 := hX.finite₀
  have hfX1 := hX.finite₁
  have hfC0 := hUV.finite₀
  have hfC1 := hUV.finite₁
  have hfV0 := hVh.finite₀
  have hfV1 := hVh.finite₁
  have hinj : Function.Injective (rationalMayerVietorisInclusion T U V 1).hom := by
    rw [← LinearMap.ker_eq_bot, ← (rationalMayerVietoris_exact_intersection T U V hUo hVo
      hcover 1).moduleCat_range_eq_ker]
    have : Subsingleton (ratH X 2) :=
      ModuleCat.subsingleton_of_isZero (hX.isZero 2 le_rfl)
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x 0, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨hB1, hB0, hcount⟩ := exact_six_finrank
    (rationalMayerVietorisInclusion T U V 1).hom
    (rationalMayerVietorisSum T U V 1).hom
    (rationalMayerVietorisBoundary T U V hUo hVo hcover 0).hom
    (rationalMayerVietorisInclusion T U V 0).hom
    (rationalMayerVietorisSum T U V 0).hom hinj
    (rationalMayerVietoris_exact_middle T U V hUo hVo hcover 1).moduleCat_range_eq_ker
    (rationalMayerVietoris_exact_ambient T U V hUo hVo hcover 0).moduleCat_range_eq_ker
    (rationalMayerVietoris_exact_intersection T U V hUo hVo hcover 0).moduleCat_range_eq_ker
    (rationalMayerVietoris_exact_middle T U V hUo hVo hcover 0).moduleCat_range_eq_ker
    (rationalMayerVietorisSum_zero_surjective T U V hUo hVo hcover)
  have hU1 : Module.Finite ℚ (ratH U 1) := module_finite_biprod_left hB1
  have hU0 : Module.Finite ℚ (ratH U 0) := module_finite_biprod_left hB0
  refine ⟨hU0, hU1, hvan, ?_⟩
  obtain ⟨-, hA1r⟩ := finrank_biprod (ratH U 1) (ratH V 1)
  obtain ⟨-, hA0r⟩ := finrank_biprod (ratH U 0) (ratH V 0)
  have ha := hX.euler
  have hb := hVh.euler
  have hc := hUV.euler
  change ((Module.finrank ℚ ↑(ratH U 0 ⊞ ratH V 0) : ℕ) : ℤ) -
      ((Module.finrank ℚ ↑(ratH U 1 ⊞ ratH V 1) : ℕ) : ℤ) =
      ((Module.finrank ℚ (ratH X 0) : ℕ) : ℤ) - ((Module.finrank ℚ (ratH X 1) : ℕ) : ℤ) +
        (((Module.finrank ℚ (ratH (U ∩ V : Set X) 0) : ℕ) : ℤ) -
          ((Module.finrank ℚ (ratH (U ∩ V : Set X) 1) : ℕ) : ℤ)) at hcount
  rw [hA0r, hA1r] at hcount
  push_cast at hcount
  linarith

end MayerVietoris

section AmbientSubsets

variable {Z : Type} [TopologicalSpace Z]

/-- If `S ⊆ T`, then the subspace of `T` formed by the points lying in `S` is
homeomorphic to `S`. -/
def homeomorphSubtypePreimageVal {S T : Set Z} (hST : S ⊆ T) :
    ((Subtype.val : T → Z) ⁻¹' S) ≃ₜ S where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hST y.2⟩, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [TopologicalSpace Z] in
theorem preimage_val_eq_preimage_val_of_eq_inter {X U O : Set Z} (hU : U = X ∩ O) :
    (Subtype.val : X → Z) ⁻¹' U = (Subtype.val : X → Z) ⁻¹' O := by
  ext x
  simp [hU]

theorem isOpen_preimage_val_of_eq_inter {X U O : Set Z} (hO : IsOpen O) (hU : U = X ∩ O) :
    IsOpen ((Subtype.val : X → Z) ⁻¹' U) := by
  rw [preimage_val_eq_preimage_val_of_eq_inter hU]
  exact hO.preimage continuous_subtype_val

/-- **Mayer–Vietoris count for one relatively open piece.** Let `X`, `U`, `V` be
subsets of a topological space `Z` with `U = X ∩ O₁` and `V = X ∩ O₂` for open
subsets `O₁` and `O₂` of `Z`, and with `X ⊆ U ∪ V`. If the subspaces `X`, `V` and
`U ∩ V` have curve homology with Euler characteristics `a`, `b` and `c`, then the
subspace `U` has curve homology with Euler characteristic `a + c − b`. -/
theorem HasCurveRatHomology.of_mayerVietoris_complement_subset {X U V O₁ O₂ : Set Z}
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hU : U = X ∩ O₁) (hV : V = X ∩ O₂)
    (hcover : X ⊆ U ∪ V) {a b c : ℤ} (hX : HasCurveRatHomology X a)
    (hVh : HasCurveRatHomology V b) (hUV : HasCurveRatHomology ↥(U ∩ V) c) :
    HasCurveRatHomology U (a + c - b) := by
  have hUX : U ⊆ X := hU ▸ Set.inter_subset_left
  have hVX : V ⊆ X := hV ▸ Set.inter_subset_left
  let U' : Set X := Subtype.val ⁻¹' U
  let V' : Set X := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := Set.eq_univ_of_forall fun x => hcover x.2
  have h := HasCurveRatHomology.of_mayerVietoris_complement U' V'
    (isOpen_preimage_val_of_eq_inter hO₁ hU) (isOpen_preimage_val_of_eq_inter hO₂ hV) hcov hX
    (hVh.of_homeomorph (homeomorphSubtypePreimageVal hVX))
    (hUV.of_homeomorph (homeomorphSubtypePreimageVal (Set.inter_subset_left.trans hUX)))
  exact h.of_homeomorph (homeomorphSubtypePreimageVal hUX).symm

/-- **Mayer–Vietoris count for relatively open pieces.** Let `X`, `U`, `V` be
subsets of a topological space `Z` with `U = X ∩ O₁` and `V = X ∩ O₂` for open
subsets `O₁` and `O₂` of `Z`, and with `X ⊆ U ∪ V`. If the subspaces `U` and `V`
have curve homology with Euler characteristics `a` and `b`, and the subspace
`U ∩ V` has the homology of `k` points, then the subspace `X` has curve homology
with Euler characteristic `a + b − k`. -/
theorem HasCurveRatHomology.mayerVietoris_subset {X U V O₁ O₂ : Set Z}
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hU : U = X ∩ O₁) (hV : V = X ∩ O₂)
    (hcover : X ⊆ U ∪ V) {a b : ℤ} {k : ℕ} (hUh : HasCurveRatHomology U a)
    (hVh : HasCurveRatHomology V b) (hUV : HasDiscreteRatHomology ↥(U ∩ V) k) :
    HasCurveRatHomology X (a + b - k) := by
  have hUX : U ⊆ X := hU ▸ Set.inter_subset_left
  have hVX : V ⊆ X := hV ▸ Set.inter_subset_left
  let U' : Set X := Subtype.val ⁻¹' U
  let V' : Set X := Subtype.val ⁻¹' V
  have hcov : U' ∪ V' = Set.univ := Set.eq_univ_of_forall fun x => hcover x.2
  exact HasCurveRatHomology.mayerVietoris U' V'
    (isOpen_preimage_val_of_eq_inter hO₁ hU) (isOpen_preimage_val_of_eq_inter hO₂ hV) hcov
    (hUh.of_homeomorph (homeomorphSubtypePreimageVal hUX))
    (hVh.of_homeomorph (homeomorphSubtypePreimageVal hVX))
    (hUV.of_homeomorph (homeomorphSubtypePreimageVal (Set.inter_subset_left.trans hUX)))

end AmbientSubsets

end OnLeConjecture.DifferentialTopology
