/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.DeltaCodimension
public import OnLeConjecture.Analytic.PlaneWeierstrassPrimes
public import OnLeConjecture.Analytic.AllOrdersPreparation
public import OnLeConjecture.Analytic.PlaneElimination
public import OnLeConjecture.Analytic.PointBlowupChart
public import OnLeConjecture.Analytic.PullbackEquivalence
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Codimension of a point blowup chart modulo a regular equation

Let `φ_c(u, v) = (v (u + c), v)` be the point blowup chart and let `H` be
regular of order `m > 0` in the first coordinate. The subspace
`φ_c^* ℂ{x, y} + (H)` of `ℂ{u, v}` has codimension `0 + 1 + ⋯ + (m - 1)`.

By Weierstrass preparation, `ℂ{u, v}/(H)` is the polynomial quotient
`ℂ{v}[X]/(P)` for a distinguished polynomial `P` of degree `m`. It is free
over `ℂ{v}` with basis `1, X, …, X^{m-1}`. Division by the first
coordinate shows that the image of `φ_c^*` is the `ℂ{v}`-span of
`(v X)^k` for `k < m`. The quotient is therefore
`⊕_{k < m} ℂ{v}/(v^k)`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open _root_.Polynomial Module

namespace PointedMapGerm

/-- Pullback along a pointed map germ as a complex algebra homomorphism. -/
noncomputable def pullbackAlgHom {n m : ℕ} (φ : PointedMapGerm n m) : Germ m →ₐ[ℂ] Germ n :=
  { φ.pullbackRingHom with commutes' := fun c => φ.pullback_constRingHom c }

@[simp]
theorem pullbackAlgHom_apply {n m : ℕ} (φ : PointedMapGerm n m) (g : Germ m) :
    φ.pullbackAlgHom g = φ.pullbackRingHom g :=
  rfl

end PointedMapGerm

namespace Germ

/-- The tail projection is unchanged by the point blowup chart. -/
theorem hyperplaneTailGerm_comp_pointBlowupChartGerm (c : ℂ) :
    (hyperplaneTailGerm 1).comp (pointBlowupChartGerm c) = hyperplaneTailGerm 1 := by
  rw [hyperplaneTailGerm, pointBlowupChartGerm, PointedMapGerm.comp_ofFunction]
  congr 1
  funext z i
  fin_cases i
  simp [pointBlowupChart]

/-- Germs in the second coordinate are unchanged by the point blowup chart. -/
theorem pointBlowupChartGerm_pullback_hyperplaneExtension (c : ℂ) (r : Germ 1) :
    (pointBlowupChartGerm c).pullbackRingHom (hyperplaneExtension 1 r) =
      hyperplaneExtension 1 r := by
  rw [hyperplaneExtension, ← RingHom.comp_apply, ← PointedMapGerm.pullbackRingHom_comp,
    hyperplaneTailGerm_comp_pointBlowupChartGerm]

theorem hyperplaneExtension_constRingHom (a : ℂ) :
    hyperplaneExtension 1 (constRingHom 1 a) = constRingHom 2 a :=
  (hyperplaneTailGerm 1).pullback_constRingHom a

theorem firstCoordinatePolynomialEvaluation_X :
    firstCoordinatePolynomialEvaluation (X : Polynomial (Germ 1)) = coordinate (0 : Fin 2) := by
  simp [firstCoordinatePolynomialEvaluation]

theorem firstCoordinatePolynomialEvaluation_C (r : Germ 1) :
    firstCoordinatePolynomialEvaluation (C r) = hyperplaneExtension 1 r := by
  simp [firstCoordinatePolynomialEvaluation]

section Weierstrass

variable {d : ℕ} (P : Polynomial (Germ 1)) (hPMonic : P.Monic)
  (hPDegree : P.natDegree = d + 1)
  (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)

/-- The quotient map from plane germs to the polynomial quotient by a
distinguished Weierstrass polynomial. -/
noncomputable def weierstrassQuotientHom : Germ 2 →+* AdjoinRoot P :=
  (distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff).symm.toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span {firstCoordinatePolynomialEvaluation P}))

theorem weierstrassQuotientHom_eval (Q : Polynomial (Germ 1)) :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff (firstCoordinatePolynomialEvaluation Q) =
      AdjoinRoot.mk P Q := by
  apply (distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff).injective
  change distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff
      ((distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff).symm _) =
    distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff
      (Ideal.Quotient.mk (Ideal.span {P}) Q)
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem weierstrassQuotientHom_coordinate_zero :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff (coordinate (0 : Fin 2)) =
      AdjoinRoot.root P := by
  rw [← firstCoordinatePolynomialEvaluation_X, weierstrassQuotientHom_eval]
  rfl

theorem weierstrassQuotientHom_hyperplaneExtension (r : Germ 1) :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff (hyperplaneExtension 1 r) =
      AdjoinRoot.of P r := by
  rw [← firstCoordinatePolynomialEvaluation_C, weierstrassQuotientHom_eval]
  rfl

theorem weierstrassQuotientHom_coordinate_one :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff (coordinate (1 : Fin 2)) =
      AdjoinRoot.of P (coordinate (0 : Fin 1)) := by
  rw [← hyperplaneExtension_coordinate_plane, weierstrassQuotientHom_hyperplaneExtension]

theorem weierstrassQuotientHom_surjective :
    Function.Surjective (weierstrassQuotientHom P hPMonic hPDegree hPCoeff) :=
  (distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff).symm.surjective.comp
    Ideal.Quotient.mk_surjective

theorem weierstrassQuotientHom_eq_zero_iff (g : Germ 2) :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff g = 0 ↔
      g ∈ Ideal.span {firstCoordinatePolynomialEvaluation P} := by
  change (distinguishedWeierstrassQuotientRingEquiv d P hPMonic hPDegree hPCoeff).symm _ = 0 ↔ _
  rw [RingEquiv.map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem weierstrassQuotientHom_constRingHom (a : ℂ) :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff (constRingHom 2 a) =
      algebraMap ℂ (AdjoinRoot P) a := by
  rw [← hyperplaneExtension_constRingHom, weierstrassQuotientHom_hyperplaneExtension]
  rfl

/-- The Weierstrass quotient map as a complex algebra homomorphism. -/
noncomputable def weierstrassQuotientAlgHom : Germ 2 →ₐ[ℂ] AdjoinRoot P :=
  { weierstrassQuotientHom P hPMonic hPDegree hPCoeff with
    commutes' := weierstrassQuotientHom_constRingHom P hPMonic hPDegree hPCoeff }

end Weierstrass

section Codimension

variable (c : ℂ) {d : ℕ} (P : Polynomial (Germ 1)) (hPMonic : P.Monic)
  (hPDegree : P.natDegree = d + 1)
  (hPCoeff : ∀ k, k < d + 1 → P.coeff k ∈ maximalIdeal 1)

/-- The `ℂ{v}`-span of `(v X)^k`, `k < deg P`, in the polynomial quotient
`ℂ{v}[X]/(P)`. -/
noncomputable def chartImageSpan : Submodule (Germ 1) (AdjoinRoot P) :=
  Submodule.span (Germ 1)
    (Set.range fun k : Fin P.natDegree =>
      (AdjoinRoot.of P (coordinate (0 : Fin 1)) * AdjoinRoot.root P) ^ (k : ℕ))

/-- The power basis `1, X, …, X^{deg P - 1}` of `ℂ{v}[X]/(P)`, indexed by
`Fin (deg P)`. -/
noncomputable def weierstrassBasis (hPMonic : P.Monic) :
    Basis (Fin P.natDegree) (Germ 1) (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis' hPMonic).basis

theorem weierstrassBasis_apply (hPMonic : P.Monic) (i : Fin P.natDegree) :
    weierstrassBasis P hPMonic i = AdjoinRoot.root P ^ (i : ℕ) :=
  (congrFun (PowerBasis.coe_basis (AdjoinRoot.powerBasis' hPMonic)) i).trans
    (by rw [AdjoinRoot.powerBasis'_gen])

theorem of_mul_generator_mem_chartImageSpan (k : ℕ) (hk : k < P.natDegree) (a : Germ 1) :
    AdjoinRoot.of P a *
        (AdjoinRoot.of P (coordinate (0 : Fin 1)) * AdjoinRoot.root P) ^ k ∈
      chartImageSpan P := by
  have h := Submodule.smul_mem (chartImageSpan P) a
    (Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩)
  rwa [Algebra.smul_def, AdjoinRoot.algebraMap_eq] at h

include hPMonic in
/-- Multiplication by `v^{deg P}` carries the whole quotient into the span. -/
theorem coordinate_pow_natDegree_mul_mem_chartImageSpan (s : AdjoinRoot P) :
    AdjoinRoot.of P (coordinate (0 : Fin 1)) ^ P.natDegree * s ∈ chartImageSpan P := by
  let B := weierstrassBasis P hPMonic
  rw [← B.sum_repr s, Finset.mul_sum]
  apply Submodule.sum_mem
  intro i _
  have hi : (i : ℕ) < P.natDegree := i.2
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi.le
  have hmem := of_mul_generator_mem_chartImageSpan P i hi
    (B.repr s i * coordinate (0 : Fin 1) ^ j)
  convert hmem using 1
  rw [show AdjoinRoot.of P (coordinate (0 : Fin 1)) ^ P.natDegree =
      AdjoinRoot.of P (coordinate (0 : Fin 1)) ^ ((i : ℕ) + j) from congrArg _ hj,
    weierstrassBasis_apply, Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_mul, map_pow]
  ring

/-- Powers of `v (X + a)` below `deg P` times scalars lie in the span. -/
theorem coordinate_pow_mul_shift_pow_mem_chartImageSpan (k : ℕ) (hk : k < P.natDegree)
    (a b : Germ 1) :
    AdjoinRoot.of P (coordinate (0 : Fin 1)) ^ k *
        (AdjoinRoot.root P + AdjoinRoot.of P a) ^ k * AdjoinRoot.of P b ∈
      chartImageSpan P := by
  rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hjk
  have hmem := of_mul_generator_mem_chartImageSpan P j (lt_of_le_of_lt hjk hk)
    (coordinate (0 : Fin 1) ^ l * a ^ (k - j) * (k.choose j : Germ 1) * b)
  convert hmem using 1
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_natCast, hl]
  ring

/-- The point blowup chart followed by the Weierstrass quotient map. -/
noncomputable def chartWeierstrassHom : Germ 2 →+* AdjoinRoot P :=
  (weierstrassQuotientHom P hPMonic hPDegree hPCoeff).comp
    (pointBlowupChartGerm c).pullbackRingHom

theorem chartWeierstrassHom_coordinate_zero :
    chartWeierstrassHom c P hPMonic hPDegree hPCoeff (coordinate (0 : Fin 2)) =
      AdjoinRoot.of P (coordinate (0 : Fin 1)) *
        (AdjoinRoot.root P + AdjoinRoot.of P (constRingHom 1 c)) := by
  change weierstrassQuotientHom P hPMonic hPDegree hPCoeff
      ((pointBlowupChartGerm c).pullbackRingHom (coordinate (0 : Fin 2))) = _
  rw [pointBlowupChartGerm_pullback_zero, ← hyperplaneExtension_constRingHom, map_mul, map_add,
    weierstrassQuotientHom_coordinate_one, weierstrassQuotientHom_coordinate_zero,
    weierstrassQuotientHom_hyperplaneExtension]

theorem chartWeierstrassHom_hyperplaneExtension (r : Germ 1) :
    chartWeierstrassHom c P hPMonic hPDegree hPCoeff (hyperplaneExtension 1 r) =
      AdjoinRoot.of P r := by
  change weierstrassQuotientHom P hPMonic hPDegree hPCoeff
      ((pointBlowupChartGerm c).pullbackRingHom (hyperplaneExtension 1 r)) = _
  rw [pointBlowupChartGerm_pullback_hyperplaneExtension, weierstrassQuotientHom_hyperplaneExtension]

/-- Every germ pulled back by the chart lands in the span. -/
theorem chartWeierstrassHom_mem_chartImageSpan (g : Germ 2) :
    chartWeierstrassHom c P hPMonic hPDegree hPCoeff g ∈ chartImageSpan P := by
  let T := chartWeierstrassHom c P hPMonic hPDegree hPCoeff
  let n := P.natDegree
  let a : Germ 1 := constRingHom 1 c
  have hT0 : T (coordinate (0 : Fin 2)) =
      AdjoinRoot.of P (coordinate (0 : Fin 1)) * (AdjoinRoot.root P + AdjoinRoot.of P a) :=
    chartWeierstrassHom_coordinate_zero c P hPMonic hPDegree hPCoeff
  have hclaim : ∀ j, j ≤ n → ∀ g : Germ 2,
      T (coordinate (0 : Fin 2)) ^ (n - j) * T g ∈ chartImageSpan P := by
    intro j
    induction j with
    | zero =>
      intro _ g
      rw [Nat.sub_zero, hT0, mul_pow, mul_assoc]
      exact coordinate_pow_natDegree_mul_mem_chartImageSpan P hPMonic _
    | succ j ih =>
      intro hj g
      obtain ⟨⟨q, r⟩, hqr, -⟩ := exists_unique_firstCoordinate_division (n := 1) g
      have hsplit : n - j = n - (j + 1) + 1 := by omega
      have hg : T g = T (coordinate (0 : Fin 2)) * T q + AdjoinRoot.of P r := by
        rw [hqr, map_add, map_mul]
        exact congrArg _ (chartWeierstrassHom_hyperplaneExtension c P hPMonic hPDegree hPCoeff r)
      rw [hg, mul_add]
      apply Submodule.add_mem
      · have h := ih (by omega) q
        rw [hsplit, pow_succ] at h
        rwa [← mul_assoc]
      · rw [hT0, mul_pow]
        exact coordinate_pow_mul_shift_pow_mem_chartImageSpan P (n - (j + 1)) (by omega) a r
  have h := hclaim n le_rfl g
  rwa [Nat.sub_self, pow_zero, one_mul] at h

/-- A germ maps into the span exactly when it lies in the chart image plus
the ideal of the Weierstrass polynomial. -/
theorem weierstrassQuotientHom_mem_chartImageSpan_iff (g : Germ 2) :
    weierstrassQuotientHom P hPMonic hPDegree hPCoeff g ∈ chartImageSpan P ↔
      g ∈ LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap ⊔
        (Ideal.span {firstCoordinatePolynomialEvaluation P}).restrictScalars ℂ := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (Germ 1)).mp hg
    let w : Germ 2 := ∑ k : Fin P.natDegree, hyperplaneExtension 1 (a k) *
      (coordinate (0 : Fin 2) - constRingHom 2 c * coordinate (1 : Fin 2)) ^ (k : ℕ)
    have hw : (pointBlowupChartGerm c).pullbackRingHom w =
        ∑ k : Fin P.natDegree, hyperplaneExtension 1 (a k) *
          (coordinate (1 : Fin 2) * coordinate (0 : Fin 2)) ^ (k : ℕ) := by
      simp only [w, map_sum, map_mul, map_pow, map_sub,
        pointBlowupChartGerm_pullback_hyperplaneExtension, pointBlowupChartGerm_pullback_zero,
        pointBlowupChartGerm_pullback_one, PointedMapGerm.pullback_constRingHom]
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      ring
    have hψw : weierstrassQuotientHom P hPMonic hPDegree hPCoeff
        ((pointBlowupChartGerm c).pullbackRingHom w) =
          weierstrassQuotientHom P hPMonic hPDegree hPCoeff g := by
      rw [hw, map_sum, ← ha]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul, map_pow, map_mul, weierstrassQuotientHom_hyperplaneExtension,
        weierstrassQuotientHom_coordinate_one, weierstrassQuotientHom_coordinate_zero,
        Algebra.smul_def, AdjoinRoot.algebraMap_eq]
    have hker : g - (pointBlowupChartGerm c).pullbackRingHom w ∈
        Ideal.span {firstCoordinatePolynomialEvaluation P} := by
      rw [← weierstrassQuotientHom_eq_zero_iff P hPMonic hPDegree hPCoeff, map_sub, hψw, sub_self]
    rw [Submodule.mem_sup]
    exact ⟨(pointBlowupChartGerm c).pullbackRingHom w, ⟨w, rfl⟩, _, hker, by abel⟩
  · intro hg
    obtain ⟨y, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hg
    rw [map_add]
    apply Submodule.add_mem
    · exact chartWeierstrassHom_mem_chartImageSpan c P hPMonic hPDegree hPCoeff w
    · rw [(weierstrassQuotientHom_eq_zero_iff P hPMonic hPDegree hPCoeff z).mpr hz]
      exact Submodule.zero_mem _

/-- Coefficients in the power basis `1, X, …, X^{deg P - 1}`, the `k`th
one taken modulo `v^k`. -/
noncomputable def chartCoefficientMap :
    AdjoinRoot P →ₗ[Germ 1] ((k : Fin P.natDegree) → Germ 1 ⧸ maximalIdeal 1 ^ (k : ℕ)) :=
  LinearMap.pi fun k => (maximalIdeal 1 ^ (k : ℕ)).mkQ ∘ₗ
    (LinearMap.proj k ∘ₗ (weierstrassBasis P hPMonic).equivFun.toLinearMap)

theorem chartCoefficientMap_apply (s : AdjoinRoot P) (k : Fin P.natDegree) :
    chartCoefficientMap P hPMonic s k =
      Submodule.Quotient.mk ((weierstrassBasis P hPMonic).equivFun s k) :=
  rfl

theorem chartCoefficientMap_surjective : Function.Surjective (chartCoefficientMap P hPMonic) := by
  intro y
  choose a ha using fun k => Submodule.mkQ_surjective _ (y k)
  refine ⟨(weierstrassBasis P hPMonic).equivFun.symm a, ?_⟩
  funext k
  rw [chartCoefficientMap_apply, LinearEquiv.apply_symm_apply]
  exact ha k

theorem ker_chartCoefficientMap :
    LinearMap.ker (chartCoefficientMap P hPMonic) = chartImageSpan P := by
  let B := weierstrassBasis P hPMonic
  apply le_antisymm
  · intro s hs
    have hmem : ∀ k : Fin P.natDegree,
        B.equivFun s k ∈ Ideal.span {coordinate (0 : Fin 1) ^ (k : ℕ)} := by
      intro k
      have h := congrFun (LinearMap.mem_ker.mp hs) k
      rw [chartCoefficientMap_apply] at h
      rw [← maximalIdeal_one_pow_eq_span_coordinate_pow]
      exact (Submodule.Quotient.mk_eq_zero _).mp h
    choose b hb using fun k => Ideal.mem_span_singleton'.mp (hmem k)
    rw [← B.sum_equivFun s]
    apply Submodule.sum_mem
    intro k _
    have h := of_mul_generator_mem_chartImageSpan P k k.2 (b k)
    convert h using 1
    rw [← hb k, weierstrassBasis_apply, Algebra.smul_def,
      AdjoinRoot.algebraMap_eq, map_mul, map_pow]
    ring
  · rw [chartImageSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext j
    have hgen : (AdjoinRoot.of P (coordinate (0 : Fin 1)) * AdjoinRoot.root P) ^ (k : ℕ) =
        (coordinate (0 : Fin 1) ^ (k : ℕ)) • B k := by
      rw [weierstrassBasis_apply, Algebra.smul_def,
        AdjoinRoot.algebraMap_eq, map_pow, mul_pow]
    beta_reduce
    rw [chartCoefficientMap_apply, hgen, map_smul, Pi.smul_apply, Basis.equivFun_apply,
      Basis.repr_self, Finsupp.single_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    split_ifs with h
    · subst h
      rw [smul_eq_mul, mul_one, maximalIdeal_one_pow_eq_span_coordinate_pow]
      exact Ideal.subset_span (Set.mem_singleton _)
    · rw [smul_zero]
      exact Submodule.zero_mem _

include hPMonic hPDegree hPCoeff in
/-- Codimension of the chart image plus a distinguished Weierstrass
polynomial. -/
theorem finiteDimensional_and_finrank_chart_quotient_of_distinguished :
    FiniteDimensional ℂ (Germ 2 ⧸
        (LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap ⊔
          (Ideal.span {firstCoordinatePolynomialEvaluation P}).restrictScalars ℂ)) ∧
      finrank ℂ (Germ 2 ⧸
        (LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap ⊔
          (Ideal.span {firstCoordinatePolynomialEvaluation P}).restrictScalars ℂ)) =
        ∑ k ∈ Finset.range P.natDegree, k := by
  let ψ := (weierstrassQuotientAlgHom P hPMonic hPDegree hPCoeff).toLinearMap
  let N := (chartImageSpan P).restrictScalars ℂ
  let Λ : Germ 2 →ₗ[ℂ] AdjoinRoot P ⧸ N := N.mkQ ∘ₗ ψ
  have hΛsurj : Function.Surjective Λ :=
    (Submodule.mkQ_surjective N).comp (weierstrassQuotientHom_surjective P hPMonic hPDegree hPCoeff)
  have hΛker : LinearMap.ker Λ =
      LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap ⊔
        (Ideal.span {firstCoordinatePolynomialEvaluation P}).restrictScalars ℂ := by
    ext g
    rw [LinearMap.mem_ker]
    change N.mkQ (ψ g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]
    exact weierstrassQuotientHom_mem_chartImageSpan_iff c P hPMonic hPDegree hPCoeff g
  let Ξ := (Submodule.quotEquivOfEq _ _ (ker_chartCoefficientMap P hPMonic).symm).trans
    ((chartCoefficientMap P hPMonic).quotKerEquivOfSurjective
      (chartCoefficientMap_surjective P hPMonic))
  let e := (Submodule.quotEquivOfEq _ _ hΛker.symm).trans ((Λ.quotKerEquivOfSurjective hΛsurj).trans
    ((Submodule.Quotient.restrictScalarsEquiv ℂ (chartImageSpan P)).trans (Ξ.restrictScalars ℂ)))
  have hfin : ∀ k : Fin P.natDegree, Module.Finite ℂ (Germ 1 ⧸ maximalIdeal 1 ^ (k : ℕ)) :=
    fun k => quotient_moduleFinite_of_maximalIdeal_pow_le _ le_rfl
  refine ⟨e.symm.finiteDimensional, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, ← Fin.sum_univ_eq_sum_range (fun k => k)]
  apply Finset.sum_congr rfl
  intro k _
  exact quotient_maximalIdeal_one_pow_finrank k

end Codimension

/-- Let `H` be regular of order `m > 0` in the first coordinate. The
quotient of `ℂ{u, v}` by the image of the point blowup chart plus the ideal
`(H)` has complex dimension `0 + 1 + ⋯ + (m - 1)`. -/
theorem finiteDimensional_and_finrank_pointBlowupChart_quotient (c : ℂ) (m : ℕ) (hm : 0 < m)
    (H : Germ 2) (hH : IsRegularInFirstCoordinateOfOrder H m) :
    FiniteDimensional ℂ (Germ 2 ⧸
        (LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap ⊔
          (Ideal.span {H}).restrictScalars ℂ)) ∧
      finrank ℂ (Germ 2 ⧸
        (LinearMap.range (pointBlowupChartGerm c).pullbackAlgHom.toLinearMap ⊔
          (Ideal.span {H}).restrictScalars ℂ)) = ∑ k ∈ Finset.range m, k := by
  obtain ⟨P, u, hPMonic, hPDegree, hPCoeff, hu, hHP⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos hm hH
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hspan : Ideal.span {H} = Ideal.span {firstCoordinatePolynomialEvaluation P} := by
    rw [hHP, Ideal.span_singleton_mul_right_unit hu]
  rw [hspan]
  have h := finiteDimensional_and_finrank_chart_quotient_of_distinguished c P hPMonic hPDegree
    hPCoeff
  rwa [hPDegree] at h

end Germ

end OnLeConjecture.Analytic
