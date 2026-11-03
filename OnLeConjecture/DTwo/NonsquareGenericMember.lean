/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericPointBasisOpenChoice
public import OnLeConjecture.DTwo.NonsquareQuadraticLinearNormalization

/-!
# Generic members with a nonzero scalar node jet

After source normalization the root generators have scalar multiples of
the same node jet. The recorded root order proves that their coefficient
linear form is nonzero. Exact order at every center and a nonzero node
coefficient can consequently be imposed in a prescribed nonempty open set.
-/

public section

namespace OnLeConjecture.DTwo

open Analytic Analytic.Germ

@[expose] noncomputable def scalarJetCoefficient {ι : Type*} [Fintype ι]
    (a : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun q := ∑ i, q i * a i
  map_add' q r := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' z q := by simp [Pi.smul_apply, smul_eq_mul, ← mul_assoc, Finset.mul_sum]

theorem scalarJetCoefficient_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℂ) (i : ι) : scalarJetCoefficient a (Pi.single i 1) = a i := by
  simp [scalarJetCoefficient, Pi.single_apply]

theorem linearCombination_scalar_jet_tail {ι : Type*} [Fintype ι]
    (F : ι → Germ 2) (a : ι → ℂ) (P : Germ 2) (D : ℕ)
    (htail : ∀ i, F i - constRingHom 2 (a i) * P ∈ maximalIdeal 2 ^ D)
    (q : ι → ℂ) :
    germLinearCombination F q - constRingHom 2 (scalarJetCoefficient a q) * P ∈
      maximalIdeal 2 ^ D := by
  have hh := ((maximalIdeal 2 ^ D).restrictScalars ℂ).sum_mem
    (fun i (_ : i ∈ Finset.univ) =>
      ((maximalIdeal 2 ^ D).restrictScalars ℂ).smul_mem (q i) (htail i))
  change (∑ i, q i • (F i - a i • P)) ∈ maximalIdeal 2 ^ D at hh
  simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul] at hh
  exact hh

theorem scalar_jet_relative_member_tail
    (F v P : Germ 2) (a b : ℂ) (ha : a ≠ 0) (D : ℕ)
    (hF : F - constRingHom 2 b * P ∈ maximalIdeal 2 ^ D)
    (hv : v - constRingHom 2 a * P ∈ maximalIdeal 2 ^ D) :
    F - constRingHom 2 (b / a) * v ∈ maximalIdeal 2 ^ D := by
  have hcoeff : constRingHom 2 (b / a) * constRingHom 2 a = constRingHom 2 b := by
    rw [← map_mul, div_mul_cancel₀ b ha]
  have hh := (maximalIdeal 2 ^ D).sub_mem hF
    ((maximalIdeal 2 ^ D).mul_mem_left (constRingHom 2 (b / a)) hv)
  simpa only [mul_sub, ← mul_assoc, hcoeff, sub_sub_sub_cancel_right] using hh

theorem root_scalarJetCoefficient_ne_zero
    {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*} [Fintype ι]
    (d : WeakTransformIdealData c ι) (hroot : c.multiplicity c.root = 2)
    (a : ι → ℂ) (P : Germ 2)
    (htail : ∀ i, d.generators c.root i - constRingHom 2 (a i) * P ∈
      maximalIdeal 2 ^ 3) : scalarJetCoefficient a ≠ 0 := by
  classical
  intro hz
  have ha (i : ι) : a i = 0 := by
    rw [← scalarJetCoefficient_single a i, hz]
    rfl
  have hgens (i : ι) : d.generators c.root i ∈ maximalIdeal 2 ^ 3 := by
    simpa only [ha, map_zero, zero_mul, sub_zero] using htail i
  have hle : Ideal.span (Set.range (d.generators c.root)) ≤ maximalIdeal 2 ^ 3 := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hgens i
  have hbad := hle (d.generic_member_mem c.root)
  exact c.germ_not_mem_succ c.root (by simpa only [hroot] using hbad)

theorem exists_scalar_node_point_basis_member_mem_open
    {N : ℕ} {c : AnalyticPointBasis N} (d : WeakTransformIdealData c (Fin 3))
    (hroot : c.multiplicity c.root = 2) (a : Fin 3 → ℂ)
    (htail : ∀ i, d.generators c.root i - constRingHom 2 (a i) *
      coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, scalarJetCoefficient a q ≠ 0 ∧
      ∃ hq : ∀ p, germLinearCombination (d.generators p) q ∈
          maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1),
        let c' := d.pointBasisOfLinearCombination q hq
        c'.germ c'.root - constRingHom 2 (scalarJetCoefficient a q) *
          coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈ maximalIdeal 2 ^ 3 := by
  have hlinear := root_scalarJetCoefficient_ne_zero d hroot a
    (coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ)) htail
  obtain ⟨q, hqU, hq, hnonzero⟩ :=
    d.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun _ : Fin 1 => scalarJetCoefficient a) (fun _ => hlinear) U hU hUne
  exact ⟨q, hqU, hnonzero 0, hq,
    linearCombination_scalar_jet_tail (d.generators c.root) a _ 3 htail q⟩

end OnLeConjecture.DTwo
