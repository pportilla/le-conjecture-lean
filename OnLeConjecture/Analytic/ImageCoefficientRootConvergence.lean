/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.MonicRootConvergence
public import OnLeConjecture.Analytic.PlanePointedPrimitiveElement
public import OnLeConjecture.Analytic.WeightedMonomialDivision

/-!
# Target representatives and convergence of roots

A finite list of elements of the image maximal ideal can be represented by
target functions that are analytic and vanish at the origin. Along every
target path that tends to the origin, roots of the associated monic relation
tend to zero.
-/

public section

open Filter Set
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Elements of the image maximal ideal have target representatives that
vanish at the origin. These representatives give a uniform convergence
statement for every choice of roots of the associated monic relation. -/
theorem exists_target_representatives_with_monic_root_convergence
    {n m d : ℕ} (f : PointedMapGerm n m)
    (coefficient : Fin d → f.ImageRing)
    (hcoefficient : ∀ i, coefficient i ∈ f.imageMaximalIdeal) :
    ∃ (C : Fin d → Source m → ℂ)
        (hC : ∀ i, AnalyticAt ℂ (C i) 0),
      (∀ i, C i 0 = 0) ∧
      (∀ i, coefficient i =
        f.pullbackToImageRing (Germ.ofFunction (C i) (hC i))) ∧
      ∀ {P : Type*} {l : Filter P} (u : P → Source m)
          (_hu : Tendsto u l (nhds 0)) (root : P → ℂ),
        (∀ᶠ p in l,
          root p ^ d +
            ∑ i : Fin d, C i (u p) * root p ^ (i : ℕ) = 0) →
        0 < d → Tendsto root l (nhds 0) := by
  choose q hq using fun i =>
    f.pullbackToImageRing_surjective (coefficient i)
  choose C hC hqC using fun i => Germ.exists_ofFunction (q i)
  have hCZero : ∀ i, C i 0 = 0 := by
    intro i
    have hvalue : f.imageValueRingHom (coefficient i) = 0 :=
      (f.mem_imageMaximalIdeal_iff).mp (hcoefficient i)
    rw [← hq i, f.imageValueRingHom_pullback, hqC i,
      Germ.valueRingHom_ofFunction] at hvalue
    exact hvalue
  refine ⟨C, hC, hCZero, ?_, ?_⟩
  · intro i
    exact (hq i).symm.trans
      (congrArg f.pullbackToImageRing (hqC i))
  · intro P l u hu root hroot hd
    apply tendsto_zero_of_monic_power_relation hd
      (fun i p => C i (u p)) root
    · intro i
      have hi := (hC i).continuousAt.tendsto.comp hu
      simpa only [Function.comp_def, hCZero i] using hi
    · exact hroot

set_option maxHeartbeats 400000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- A finite nonbirational plane map has a pointed primitive element and a
monic relation for a power of that element. The target representatives of all
lower coefficients vanish at the origin. Every choice of roots of the
specialized relation tends to zero along a target path to the origin. -/
theorem exists_pointed_primitive_relation_with_root_convergence
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (hnot : ¬ f.IsBirationalAtOrigin) :
    let _ : Algebra (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
    ∃ (b : Germ 2) (N : ℕ) (p : Polynomial f.ImageRing)
        (C : Fin p.natDegree → Source m → ℂ)
        (hC : ∀ i, AnalyticAt ℂ (C i) 0),
      b ∈ Germ.maximalIdeal 2 ∧
      b ^ N ∈ f.1.coordinateIdeal ∧
      IsIntegral f.ImageRing b ∧
      let beta := algebraMap (Germ 2) (FractionRing (Germ 2)) b
      IntermediateField.adjoin (FractionRing f.ImageRing) {beta} = ⊤ ∧
      (∃ sigma tau : Field.Emb (FractionRing f.ImageRing)
          (FractionRing (Germ 2)), sigma beta ≠ tau beta) ∧
      p.Monic ∧ Polynomial.aeval (b ^ N) p = 0 ∧
      0 < p.natDegree ∧
      (∀ i, C i 0 = 0) ∧
      (∀ i : Fin p.natDegree, p.coeff i =
        f.pullbackToImageRing (Germ.ofFunction (C i) (hC i))) ∧
      ∀ {P : Type*} {l : Filter P} (u : P → Source m)
          (_hu : Tendsto u l (nhds 0)) (root : P → ℂ),
        (∀ᶠ parameter in l,
          root parameter ^ p.natDegree +
            ∑ i : Fin p.natDegree,
              C i (u parameter) * root parameter ^ (i : ℕ) = 0) →
        Tendsto root l (nhds 0) := by
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  obtain ⟨b, N, hbMaximal, hpower, hbIntegral, hprimitive,
    sigma, tau, hvalues⟩ :=
    f.exists_pointed_primitive_with_coordinate_power_of_finite_of_not_birational
      hfinite hnot
  obtain ⟨p, hpMonic, hpEval, hpCoefficient⟩ :=
    f.exists_monic_relation_with_vanishing_coefficients_of_pow_mem_coordinateIdeal
      hfinite hpower
  have hpDegree : 0 < p.natDegree := by
    rw [hpMonic.natDegree_pos]
    intro hpOne
    rw [hpOne] at hpEval
    have hone : (1 : Germ 2) = 0 := by
      simpa only [map_one] using hpEval
    exact one_ne_zero hone
  obtain ⟨C, hC, hCZero, hCRepresentative, hrootConvergence⟩ :=
    f.exists_target_representatives_with_monic_root_convergence
      (fun i : Fin p.natDegree => p.coeff i)
      (fun i => hpCoefficient i (Nat.ne_of_lt i.isLt))
  exact ⟨b, N, p, C, hC, hbMaximal, hpower, hbIntegral,
    hprimitive, ⟨sigma, tau, hvalues⟩, hpMonic, hpEval, hpDegree,
    hCZero, hCRepresentative, fun u hu root hroot =>
      hrootConvergence u hu root hroot hpDegree⟩

end PointedMapGerm

end OnLeConjecture.Analytic
