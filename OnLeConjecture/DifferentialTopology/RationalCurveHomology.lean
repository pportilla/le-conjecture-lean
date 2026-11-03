/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.External.OpenAIMath.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris
public import OnLeConjecture.External.OpenAIMath.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rational homology of spaces with the homology of a graph

We use the rational singular homology of a topological space `X`, written
`ratH X n`; it is the homology of Mathlib's singular chain complex with
coefficients in `ℚ`, as in the vendored rational Mayer–Vietoris sequence.

* `HasDiscreteRatHomology X k`: the rational homology of `X` is that of `k`
  points, namely `H₀` has dimension `k` and all higher groups vanish.
* `HasCurveRatHomology X χ`: `H₀` and `H₁` are finite dimensional, all groups
  in degrees at least two vanish, and `dim H₀ − dim H₁ = χ`.

Both properties are invariant under homotopy equivalence. A finite discrete
space with `k` points has the homology of `k` points. If `X = U ∪ V` with `U`,
`V` open, `U` and `V` have curve homology with Euler characteristics `a` and
`b`, and `U ∩ V` has the homology of `k` points, then `X` has curve homology
with Euler characteristic `a + b − k`. The proof uses the exactness of the
rational Mayer–Vietoris sequence and the rank–nullity theorem.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits DirectSum

namespace OnLeConjecture.DifferentialTopology

open OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

/-- Rational singular homology of a topological space. -/
abbrev ratH (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat.{0} ℚ :=
  (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
    (TopCat.of X)).homology n

theorem ratH_eq_singularHomologyFunctor (X : Type) [TopologicalSpace X] (n : ℕ) :
    ratH X n =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) n).obj
        (ModuleCat.of ℚ ℚ)).obj (TopCat.of X) :=
  rfl

open OAI.AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles in
/-- A homotopy equivalence induces isomorphisms on rational homology. -/
def ratHIsoOfHomotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : ratH X n ≅ ratH Y n :=
  singularHomologyIsoOfHomotopyEquiv
    (ModuleCat.of ℚ ℚ) (X := TopCat.of X) (Y := TopCat.of Y) e n

/-- The rational homology of `X` is that of `k` points. -/
structure HasDiscreteRatHomology (X : Type) [TopologicalSpace X] (k : ℕ) : Prop where
  finite : Module.Finite ℚ (ratH X 0)
  finrank_eq : Module.finrank ℚ (ratH X 0) = k
  isZero : ∀ n, n ≠ 0 → IsZero (ratH X n)

/-- The rational homology of `X` is finite dimensional, concentrated in
degrees zero and one, with Euler characteristic `χ`. -/
structure HasCurveRatHomology (X : Type) [TopologicalSpace X] (χ : ℤ) : Prop where
  finite₀ : Module.Finite ℚ (ratH X 0)
  finite₁ : Module.Finite ℚ (ratH X 1)
  isZero : ∀ n, 2 ≤ n → IsZero (ratH X n)
  euler : (Module.finrank ℚ (ratH X 0) : ℤ) - Module.finrank ℚ (ratH X 1) = χ

section Invariance

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem module_finite_of_iso {M N : ModuleCat.{0} ℚ} (e : M ≅ N) [Module.Finite ℚ N] :
    Module.Finite ℚ M :=
  Module.Finite.equiv e.symm.toLinearEquiv

theorem finrank_eq_of_iso {M N : ModuleCat.{0} ℚ} (e : M ≅ N) :
    Module.finrank ℚ M = Module.finrank ℚ N :=
  e.toLinearEquiv.finrank_eq

theorem HasDiscreteRatHomology.of_homotopyEquiv {k : ℕ} (e : ContinuousMap.HomotopyEquiv X Y)
    (h : HasDiscreteRatHomology Y k) : HasDiscreteRatHomology X k where
  finite := by
    have := h.finite
    exact module_finite_of_iso (ratHIsoOfHomotopyEquiv e 0)
  finrank_eq := by rw [finrank_eq_of_iso (ratHIsoOfHomotopyEquiv e 0), h.finrank_eq]
  isZero n hn := (h.isZero n hn).of_iso (ratHIsoOfHomotopyEquiv e n)

theorem HasCurveRatHomology.of_homotopyEquiv {χ : ℤ} (e : ContinuousMap.HomotopyEquiv X Y)
    (h : HasCurveRatHomology Y χ) : HasCurveRatHomology X χ where
  finite₀ := by
    have := h.finite₀
    exact module_finite_of_iso (ratHIsoOfHomotopyEquiv e 0)
  finite₁ := by
    have := h.finite₁
    exact module_finite_of_iso (ratHIsoOfHomotopyEquiv e 1)
  isZero n hn := (h.isZero n hn).of_iso (ratHIsoOfHomotopyEquiv e n)
  euler := by
    rw [finrank_eq_of_iso (ratHIsoOfHomotopyEquiv e 0),
      finrank_eq_of_iso (ratHIsoOfHomotopyEquiv e 1), h.euler]

theorem HasDiscreteRatHomology.of_homeomorph {k : ℕ} (e : X ≃ₜ Y)
    (h : HasDiscreteRatHomology Y k) : HasDiscreteRatHomology X k :=
  h.of_homotopyEquiv e.toHomotopyEquiv

theorem HasCurveRatHomology.of_homeomorph {χ : ℤ} (e : X ≃ₜ Y)
    (h : HasCurveRatHomology Y χ) : HasCurveRatHomology X χ :=
  h.of_homotopyEquiv e.toHomotopyEquiv

theorem finrank_eq_zero_of_isZero {M : ModuleCat.{0} ℚ} (h : IsZero M) :
    Module.finrank ℚ M = 0 := by
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_zero_of_subsingleton

theorem module_finite_of_isZero {M : ModuleCat.{0} ℚ} (h : IsZero M) : Module.Finite ℚ M := by
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero h
  infer_instance

/-- Homology of `k` points is curve homology with Euler characteristic `k`. -/
theorem HasDiscreteRatHomology.toCurve {k : ℕ} (h : HasDiscreteRatHomology X k) :
    HasCurveRatHomology X k where
  finite₀ := h.finite
  finite₁ := module_finite_of_isZero (h.isZero 1 one_ne_zero)
  isZero n hn := h.isZero n (by omega)
  euler := by
    rw [h.finrank_eq, finrank_eq_zero_of_isZero (h.isZero 1 one_ne_zero)]
    simp

end Invariance

section Discrete

/-- The finite discrete space with `k` points has the rational homology of
`k` points. -/
theorem hasDiscreteRatHomology_fin (k : ℕ) : HasDiscreteRatHomology (Fin k) k := by
  have e₀ : ratH (Fin k) 0 ≅ ModuleCat.of ℚ (⨁ _ : Fin k, ℚ) :=
    AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ) (TopCat.of (Fin k)) ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : Fin k => ModuleCat.of ℚ ℚ)
  have hfin : Module.Finite ℚ (⨁ _ : Fin k, ℚ) :=
    Module.Finite.equiv (DirectSum.linearEquivFunOnFintype ℚ (Fin k) fun _ => ℚ).symm
  refine ⟨?_, ?_, fun n hn => ?_⟩
  · exact Module.Finite.equiv e₀.symm.toLinearEquiv
  · rw [e₀.toLinearEquiv.finrank_eq]
    change Module.finrank ℚ (⨁ _ : Fin k, ℚ) = k
    rw [(DirectSum.linearEquivFunOnFintype ℚ (Fin k) fun _ => ℚ).finrank_eq]
    simp
  · exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℚ) n (ModuleCat.of ℚ ℚ) (TopCat.of (Fin k)) hn

/-- A space homotopy equivalent to `Fin k` has the rational homology of `k`
points. -/
theorem hasDiscreteRatHomology_of_homotopyEquiv_fin {X : Type} [TopologicalSpace X] {k : ℕ}
    (e : ContinuousMap.HomotopyEquiv X (Fin k)) : HasDiscreteRatHomology X k :=
  (hasDiscreteRatHomology_fin k).of_homotopyEquiv e

end Discrete

section LinearAlgebra

variable {A₁ B₁ C₀ A₀ B₀ : Type*}
  [AddCommGroup A₁] [Module ℚ A₁] [AddCommGroup B₁] [Module ℚ B₁]
  [AddCommGroup C₀] [Module ℚ C₀] [AddCommGroup A₀] [Module ℚ A₀]
  [AddCommGroup B₀] [Module ℚ B₀]

/-- Dimension count along an exact sequence
`0 → A₁ → B₁ → C₀ → A₀ → B₀ → 0` of rational vector spaces with `A₁`,
`C₀`, `A₀` finite dimensional. -/
theorem exact_five_finrank (α : A₁ →ₗ[ℚ] B₁) (β : B₁ →ₗ[ℚ] C₀) (γ : C₀ →ₗ[ℚ] A₀)
    (σ : A₀ →ₗ[ℚ] B₀) (hα : Function.Injective α) (hαβ : LinearMap.range α = LinearMap.ker β)
    (hβγ : LinearMap.range β = LinearMap.ker γ) (hγσ : LinearMap.range γ = LinearMap.ker σ)
    (hσ : Function.Surjective σ) [Module.Finite ℚ A₁] [Module.Finite ℚ C₀]
    [Module.Finite ℚ A₀] :
    Module.Finite ℚ B₁ ∧ Module.Finite ℚ B₀ ∧
      (Module.finrank ℚ B₀ : ℤ) - Module.finrank ℚ B₁ =
        (Module.finrank ℚ A₀ : ℤ) - Module.finrank ℚ A₁ - Module.finrank ℚ C₀ := by
  have hB₁ : Module.Finite ℚ B₁ := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker β ?_ ?_⟩
    · exact Module.Finite.iff_fg.mp inferInstance
    · rw [top_inf_eq, ← hαβ, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top).map α
  have hB₀ : Module.Finite ℚ B₀ := Module.Finite.of_surjective σ hσ
  refine ⟨hB₁, hB₀, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker β
  have h2 := LinearMap.finrank_range_add_finrank_ker γ
  have h3 := LinearMap.finrank_range_add_finrank_ker σ
  have hrα : Module.finrank ℚ (LinearMap.range α) = Module.finrank ℚ A₁ :=
    LinearMap.finrank_range_of_inj hα
  rw [← hαβ, hrα] at h1
  rw [← hβγ] at h2
  rw [← hγσ, LinearMap.range_eq_top.mpr hσ, finrank_top] at h3
  omega

end LinearAlgebra

section MayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The rational homology of the subspace `U`, written through `TopCat`. -/
abbrev subRatH (U : Set X) (n : ℕ) : ModuleCat.{0} ℚ := ratH U n

theorem finrank_biprod (M N : ModuleCat.{0} ℚ) [Module.Finite ℚ M] [Module.Finite ℚ N] :
    Module.Finite ℚ ↑(M ⊞ N) ∧
      Module.finrank ℚ ↑(M ⊞ N) = Module.finrank ℚ M + Module.finrank ℚ N := by
  have e := (ModuleCat.biprodIsoProd M N).toLinearEquiv
  refine ⟨Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq]
  exact Module.finrank_prod

theorem isZero_biprod {M N : ModuleCat.{0} ℚ} (hM : IsZero M) (hN : IsZero N) :
    IsZero (M ⊞ N) := by
  refine (IsZero.of_iso ?_ (ModuleCat.biprodIsoProd M N))
  have : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
  have : Subsingleton N := ModuleCat.subsingleton_of_isZero hN
  exact ModuleCat.isZero_of_subsingleton _

/-- **Mayer–Vietoris count.** If `X = U ∪ V` with `U`, `V` open, `U` and `V`
have curve homology with Euler characteristics `a` and `b`, and `U ∩ V` has
the homology of `k` points, then `X` has curve homology with Euler
characteristic `a + b − k`. -/
theorem HasCurveRatHomology.mayerVietoris (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) {a b : ℤ} {k : ℕ} (hUh : HasCurveRatHomology U a)
    (hVh : HasCurveRatHomology V b) (hUV : HasDiscreteRatHomology (U ∩ V : Set X) k) :
    HasCurveRatHomology X (a + b - k) := by
  let T : TopCat.{0} := TopCat.of X
  have hUo : IsOpen (U : Set T) := hU
  have hVo : IsOpen (V : Set T) := hV
  -- the sum maps
  have hfinA : ∀ n, Module.Finite ℚ (ratH U n) → Module.Finite ℚ (ratH V n) →
      Module.Finite ℚ ↑(ratH U n ⊞ ratH V n) ∧
        Module.finrank ℚ ↑(ratH U n ⊞ ratH V n) =
          Module.finrank ℚ (ratH U n) + Module.finrank ℚ (ratH V n) :=
    fun n h₁ h₂ => finrank_biprod _ _
  -- vanishing in degrees at least two
  have hvan : ∀ n, 2 ≤ n → IsZero (ratH X n) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hex := rationalMayerVietoris_exact_ambient T U V hUo hVo hcover m
    have hA : IsZero (ratH U (m + 1) ⊞ ratH V (m + 1)) :=
      isZero_biprod (hUh.isZero _ hn) (hVh.isZero _ hn)
    have hC : IsZero (ratH (U ∩ V : Set X) m) := hUV.isZero m (by omega)
    exact hex.isZero_X₂ (hA.eq_of_src _ _) (hC.eq_of_tgt _ _)
  -- the five term exact sequence in degrees one and zero
  have hfU0 := hUh.finite₀
  have hfU1 := hUh.finite₁
  have hfV0 := hVh.finite₀
  have hfV1 := hVh.finite₁
  have hfC0 := hUV.finite
  obtain ⟨hA1f, hA1r⟩ := hfinA 1 hfU1 hfV1
  obtain ⟨hA0f, hA0r⟩ := hfinA 0 hfU0 hfV0
  have hinj : Function.Injective (rationalMayerVietorisSum T U V 1).hom := by
    rw [← LinearMap.ker_eq_bot, ← (rationalMayerVietoris_exact_middle T U V hUo hVo hcover
      1).moduleCat_range_eq_ker]
    have : Subsingleton (ratH (U ∩ V : Set X) 1) :=
      ModuleCat.subsingleton_of_isZero (hUV.isZero 1 one_ne_zero)
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x 0, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨hB1, hB0, hcount⟩ := exact_five_finrank
    (rationalMayerVietorisSum T U V 1).hom
    (rationalMayerVietorisBoundary T U V hUo hVo hcover 0).hom
    (rationalMayerVietorisInclusion T U V 0).hom
    (rationalMayerVietorisSum T U V 0).hom hinj
    (rationalMayerVietoris_exact_ambient T U V hUo hVo hcover 0).moduleCat_range_eq_ker
    (rationalMayerVietoris_exact_intersection T U V hUo hVo hcover 0).moduleCat_range_eq_ker
    (rationalMayerVietoris_exact_middle T U V hUo hVo hcover 0).moduleCat_range_eq_ker
    (rationalMayerVietorisSum_zero_surjective T U V hUo hVo hcover)
  refine ⟨hB0, hB1, hvan, ?_⟩
  have hk := hUV.finrank_eq
  have ha := hUh.euler
  have hb := hVh.euler
  change (Module.finrank ℚ (ratH X 0) : ℤ) - Module.finrank ℚ (ratH X 1) = _
  rw [hcount, hA0r, hA1r]
  change ((Module.finrank ℚ (ratH U 0) + Module.finrank ℚ (ratH V 0) : ℕ) : ℤ) -
      ((Module.finrank ℚ (ratH U 1) + Module.finrank ℚ (ratH V 1) : ℕ) : ℤ) -
      (Module.finrank ℚ (ratH (U ∩ V : Set X) 0) : ℤ) = _
  rw [hk]
  push_cast
  linarith

end MayerVietoris

end OnLeConjecture.DifferentialTopology
