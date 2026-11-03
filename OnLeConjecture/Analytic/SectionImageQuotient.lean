/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SectionSpecializationCore
public import OnLeConjecture.Analytic.MonicTriangularFinite
public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion
public import OnLeConjecture.Analytic.ThirdCoordinateSubtraction
public import OnLeConjecture.Analytic.ParametricGermDivision
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The quotient of the source ring by the image ring

Let `g : (ℂ², 0) → (ℂ³, 0)` be locally injective, let `A` be its analytic
image ring and `B` the source ring, and regard `B` as an algebra over the
one-variable ring `R = ℂ{t}` through `t ↦ v = g₀`. The image ring is an
`R`-submodule of `B`.

When `v` is reduced and meets `g₂` finitely, the quotient `M = B / A` is a
finite free `R`-module whose rank is `dim_ℂ B / (A + v B)`.

Finiteness follows because `M` is a quotient of `B / c B` for a conductor
element `c` meeting `v` finitely, and `B` is finite over the image ring of
the finite map `(c, v)`. Torsion-freeness is the division property of the
section coordinate modulo the image ring. The rank is computed by lifting an
`R`-basis of `M` to `B`.
-/

@[expose] public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- The projection of three-space onto its first coordinate. -/
noncomputable def firstCoordinateGerm : PointedMapGerm 3 1 :=
  PointedMapGerm.ofFunction (fun x _ => x 0)
    (analyticAt_pi_iff.mpr fun _ =>
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 0).analyticAt 0)
    rfl

theorem firstCoordinateGerm_component :
    firstCoordinateGerm.1.component 0 = coordinate (0 : Fin 3) := by
  apply Subtype.ext
  rw [firstCoordinateGerm, PointedMapGerm.ofFunction, MapGerm.component_ofFunction]
  rfl

namespace PointedMapGerm

/-- The parameter homomorphism `φ ↦ φ ∘ g₀` from the one-variable ring. -/
noncomputable def sectionParameterHom (g : PointedMapGerm 2 3) : Germ 1 →+* Germ 2 :=
  (firstCoordinateGerm.comp g).pullbackRingHom

theorem sectionParameterHom_eq (g : PointedMapGerm 2 3) (r : Germ 1) :
    g.sectionParameterHom r = g.pullbackRingHom (firstCoordinateGerm.pullbackRingHom r) := by
  rw [sectionParameterHom, pullbackRingHom_comp]
  rfl

theorem sectionParameterHom_mem (g : PointedMapGerm 2 3) (r : Germ 1) :
    g.sectionParameterHom r ∈ g.ImageRing :=
  ⟨_, (g.sectionParameterHom_eq r).symm⟩

theorem sectionParameterHom_coordinate (g : PointedMapGerm 2 3) :
    g.sectionParameterHom (coordinate (0 : Fin 1)) = g.1.component 0 := by
  rw [sectionParameterHom_eq, pullback_coordinate, firstCoordinateGerm_component,
    pullback_coordinate]

theorem sectionParameterHom_const (g : PointedMapGerm 2 3) (c : ℂ) :
    g.sectionParameterHom (constRingHom 1 c) = constRingHom 2 c := by
  rw [sectionParameterHom, pullback_constRingHom]

end PointedMapGerm

/-- Every one-variable germ is its value plus a multiple of the coordinate. -/
theorem Germ.exists_eq_const_add_coordinate_mul (r : Germ 1) :
    ∃ r' : Germ 1, r = constRingHom 1 (valueRingHom 1 r) + coordinate (0 : Fin 1) * r' := by
  have hmem : r - constRingHom 1 (valueRingHom 1 r) ∈ maximalIdeal 1 := by
    rw [mem_maximalIdeal_iff, map_sub, valueRingHom_const, sub_self]
  rw [maximalIdeal_one_eq_span_coordinate, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r', hr'⟩ := hmem
  exact ⟨r', by linear_combination -hr'⟩

namespace SectionImageFactorization

variable {g : PointedMapGerm 2 3} (D : SectionImageFactorization g)

include D in
/-- **The quotient by the image ring is free over the section parameter.**
Regard the source ring as an algebra over `ℂ{t}` through `t ↦ g₀`. If `g` is
locally injective, `g₀` is reduced, and `g₀` meets `g₂` finitely, then the
image ring is a submodule `A`, the quotient `B / A` is a finite free module,
and its rank is `dim_ℂ B / (A + g₀ B)`. -/
theorem imageQuotient_finite_free (hg : g.HasInjectiveRepresentative)
    (haxis : HasFiniteIntersection (g.1.component 0) (g.1.component 2)) :
    letI : Algebra (Germ 1) (Germ 2) := g.sectionParameterHom.toAlgebra
    ∃ A : Submodule (Germ 1) (Germ 2), (A : Set (Germ 2)) = g.ImageRing ∧
      Module.Finite (Germ 1) (Germ 2 ⧸ A) ∧ Module.Free (Germ 1) (Germ 2 ⧸ A) ∧
      Module.finrank (Germ 1) (Germ 2 ⧸ A) =
        Module.finrank ℂ (Germ 2 ⧸ (LinearMap.range g.pullbackAlgHom.toLinearMap ⊔
          (Ideal.span {g.1.component 0}).restrictScalars ℂ)) := by
  classical
  let : Algebra (Germ 1) (Germ 2) := g.sectionParameterHom.toAlgebra
  set ψ := g.sectionParameterHom with hψ
  set v := g.1.component 0 with hv
  have hsmul (r : Germ 1) (b : Germ 2) : r • b = ψ r * b := Algebra.smul_def r b
  let A : Submodule (Germ 1) (Germ 2) :=
    { carrier := g.ImageRing
      add_mem' := fun ha hb => g.ImageRing.add_mem ha hb
      zero_mem' := g.ImageRing.zero_mem
      smul_mem' := fun r a ha => by
        rw [hsmul]
        exact g.ImageRing.mul_mem (g.sectionParameterHom_mem r) ha }
  have hAmem (b : Germ 2) : b ∈ A ↔ b ∈ g.ImageRing := Iff.rfl
  -- the conductor element and the division property
  have hcomp (j : Fin 3) : g.1.component j ∈ maximalIdeal 2 := by
    rw [← PointedMapGerm.pullback_coordinate]
    exact g.pullback_mem_maximalIdeal (coordinate_mem_maximalIdeal j)
  have hsq := D.squarefree_component_zero
  obtain ⟨hpolar, -, -⟩ := exists_polar_intersection_identity (g.1.component 0)
    (g.1.component 2) (hcomp 0) (hcomp 2) hsq haxis
  have hJ : HasFiniteIntersection v (jacobian v (g.1.component 2)) := hpolar
  have hf := g.injective_isFiniteAtOrigin_two hg
  obtain ⟨N, hN⟩ := g.coordinateMinorIdeal_le_radical_imageConductor hf hg
    (g.coordinate_jacobian_mem_coordinateMinorIdeal 0 2)
  set c := jacobian v (g.1.component 2) ^ N with hcdef
  have hvc : HasFiniteIntersection v c := hasFiniteIntersection_pow_right hJ N
  obtain ⟨Φ, -, -, hker⟩ := g.exists_irreducible_generator_of_finite hf
  have hdiv (b : Germ 2) (hb : v * b ∈ g.ImageRing) : b ∈ g.ImageRing :=
    D.mem_imageRing_of_component_zero_mul_mem hg Φ hker c hN hvc b hb
  have hdivpow (k : ℕ) (b : Germ 2) (hb : v ^ k * b ∈ g.ImageRing) : b ∈ g.ImageRing := by
    induction k generalizing b with
    | zero => simpa using hb
    | succ k ih =>
        apply ih
        apply hdiv
        rw [← mul_assoc, ← pow_succ']
        exact hb
  -- torsion-freeness
  have htf : Module.IsTorsionFree (Germ 1) (Germ 2 ⧸ A) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective A m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hsmul] at hrm
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨k, u, hu, hru⟩ := exists_eq_coordinate_pow_mul_unit hr
    have hψr : ψ r = v ^ k * ψ u := by
      rw [hru, map_mul, map_pow, g.sectionParameterHom_coordinate]
    have hinv : ψ u * ψ (hu.unit⁻¹ : (Germ 1)ˣ) = 1 := by
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    apply hdivpow k
    have hprod := g.ImageRing.mul_mem (g.sectionParameterHom_mem (hu.unit⁻¹ : (Germ 1)ˣ)) hrm
    have heq : ψ (hu.unit⁻¹ : (Germ 1)ˣ) * (ψ r * b) = v ^ k * b := by
      rw [hψr]
      linear_combination (v ^ k * b) * hinv
    rwa [heq] at hprod
  -- finiteness through the finite map `(c, v)`
  have hfin : Module.Finite (Germ 1) (Germ 2 ⧸ A) := by
    by_cases hcm : c ∈ maximalIdeal 2
    · obtain ⟨C, hC, hcC⟩ := exists_analyticRepresentative_allOrders c
      obtain ⟨V, hV, hvV⟩ := exists_analyticRepresentative_allOrders v
      have hC0 : C 0 = 0 := by
        rw [hcC, mem_maximalIdeal_iff, valueRingHom_ofFunction] at hcm
        exact hcm
      have hV0 : V 0 = 0 := by
        have h := hcomp 0
        rw [← hv, hvV, mem_maximalIdeal_iff, valueRingHom_ofFunction] at h
        exact h
      let Ψf : Source 2 → Source 2 := fun y => ![C y, V y]
      have hΨf : AnalyticAt ℂ Ψf 0 := by
        apply analyticAt_pi_iff.mpr
        intro i
        fin_cases i
        · exact hC
        · exact hV
      have hΨ0 : Ψf 0 = 0 := by
        funext i
        fin_cases i
        · exact hC0
        · exact hV0
      let Ψ := PointedMapGerm.ofFunction Ψf hΨf hΨ0
      have hΨc : Ψ.1.component 0 = c := by
        rw [hcC]
        apply Subtype.ext
        exact MapGerm.component_ofFunction Ψf hΨf 0
      have hΨv : Ψ.1.component 1 = v := by
        rw [hvV]
        apply Subtype.ext
        exact MapGerm.component_ofFunction Ψf hΨf 1
      have hΨfiber : Ψ.HasFiniteCoordinateFiber := by
        change Module.Finite ℂ (Germ 2 ⧸ Ψ.1.coordinateIdeal)
        have hideal : Ψ.1.coordinateIdeal = pairIdeal c v := by
          apply le_antisymm
          · rw [MapGerm.coordinateIdeal_le]
            intro i
            fin_cases i
            · change Ψ.1.component 0 ∈ _
              rw [hΨc]
              exact Ideal.subset_span (by simp)
            · change Ψ.1.component 1 ∈ _
              rw [hΨv]
              exact Ideal.subset_span (by simp)
          · rw [pairIdeal_eq_span, Ideal.span_le]
            intro z hz
            rcases hz with rfl | rfl
            · rw [← hΨc]
              exact Ψ.1.component_mem_coordinateIdeal 0
            · rw [← hΨv]
              exact Ψ.1.component_mem_coordinateIdeal 1
        rw [hideal]
        exact (hasFiniteIntersection_comm _ _).mp hvc
      have hΨfin : Ψ.IsFiniteAtOrigin :=
        PointedMapGerm.finiteFiberCriterionAtOrigin_two 2 Ψ hΨfiber
      have htail : (hyperplaneTailGerm 1).comp Ψ = firstCoordinateGerm.comp g := by
        apply PointedMapGerm.ext_components
        intro i
        obtain rfl : i = 0 := Subsingleton.elim i 0
        rw [PointedMapGerm.component_comp_eq_pullback, PointedMapGerm.component_comp_eq_pullback,
          firstCoordinateGerm_component, PointedMapGerm.pullback_coordinate,
          ← PointedMapGerm.pullback_coordinate (hyperplaneTailGerm 1)]
        change Ψ.pullbackRingHom (hyperplaneExtension 1 (coordinate (0 : Fin 1))) = _
        rw [hyperplaneExtension_coordinate, PointedMapGerm.pullback_coordinate]
        exact hΨv
      have hrel (φ : Germ 2) : ∃ q : Germ 2,
          Ψ.pullbackRingHom φ = ψ (hyperplaneRestriction 1 φ) + c * q := by
        obtain ⟨q, hq⟩ := exists_eq_hyperplaneExtension_add_coordinate_mul φ
        refine ⟨Ψ.pullbackRingHom q, ?_⟩
        conv_lhs => rw [hq]
        rw [map_add, map_mul, PointedMapGerm.pullback_coordinate, hΨc]
        congr 1
        rw [hψ, PointedMapGerm.sectionParameterHom, ← htail, PointedMapGerm.pullbackRingHom_comp]
        rfl
      have : Module.Finite Ψ.ImageRing (Germ 2) := hΨfin
      obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Ψ.ImageRing) (M := Germ 2)
      constructor
      rw [Submodule.fg_def]
      refine ⟨(Submodule.Quotient.mk (p := A)) '' (S : Set (Germ 2)), S.finite_toSet.image _, ?_⟩
      rw [eq_top_iff]
      rintro m -
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective A m
      have hb : b ∈ Submodule.span Ψ.ImageRing (S : Set (Germ 2)) := by
        rw [hS]
        trivial
      induction hb using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
          rw [Submodule.Quotient.mk_add]
          exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
          obtain ⟨φ, hφ⟩ := a.2
          obtain ⟨q, hq⟩ := hrel φ
          have hax : a • x = (hyperplaneRestriction 1 φ) • x + c * q * x := by
            rw [Subring.smul_def, smul_eq_mul, hsmul, ← hφ, hq]
            ring
          have hcA : c * q * x ∈ A := by
            rw [mul_assoc]
            exact hN (q * x)
          rw [hax, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero A).mpr hcA, add_zero,
            Submodule.Quotient.mk_smul]
          exact Submodule.smul_mem _ _ hx
    · have hcu : IsUnit c := by
        rw [mem_maximalIdeal_iff] at hcm
        exact isUnit_of_valueRingHom_ne_zero hcm
      have hsub : Subsingleton (Germ 2 ⧸ A) := by
        rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
        intro b _
        have h := hN (hcu.unit⁻¹ * b)
        rwa [← mul_assoc, IsUnit.mul_val_inv, one_mul] at h
      infer_instance
  have hfree : Module.Free (Germ 1) (Germ 2 ⧸ A) := Module.free_of_finite_type_torsion_free'
  refine ⟨A, rfl, hfin, hfree, ?_⟩
  -- the rank
  set L : Submodule ℂ (Germ 2) := LinearMap.range g.pullbackAlgHom.toLinearMap ⊔
    (Ideal.span {v}).restrictScalars ℂ with hL
  have hLmem (x : Germ 2) (a : Germ 2) (ha : a ∈ g.ImageRing) (y : Germ 2)
      (hx : x = a + v * y) : x ∈ L := by
    rw [hx]
    apply Submodule.add_mem_sup
    · obtain ⟨φ, hφ⟩ := ha
      exact ⟨φ, hφ⟩
    · rw [Submodule.restrictScalars_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hLmem' (x : Germ 2) (hx : x ∈ L) : ∃ a ∈ g.ImageRing, ∃ y, x = a + v * y := by
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨φ, rfl⟩ := ha
    rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton'] at hw
    obtain ⟨y, rfl⟩ := hw
    exact ⟨_, ⟨φ, rfl⟩, y, by rw [mul_comm]; rfl⟩
  let ι := Module.Free.ChooseBasisIndex (Germ 1) (Germ 2 ⧸ A)
  let b : Module.Basis ι (Germ 1) (Germ 2 ⧸ A) := Module.Free.chooseBasis (Germ 1) (Germ 2 ⧸ A)
  choose β hβ using fun i => Submodule.Quotient.mk_surjective A (b i)
  let f : ι → Germ 2 ⧸ L := fun i => L.mkQ (β i)
  have hmkconst (κ : ℂ) (x : Germ 2) :
      (Submodule.Quotient.mk (κ • x) : Germ 2 ⧸ A) =
        constRingHom 1 κ • (Submodule.Quotient.mk x : Germ 2 ⧸ A) := by
    rw [← Submodule.Quotient.mk_smul, hsmul, g.sectionParameterHom_const]
    rfl
  have hψρ (ρ ρ' : Germ 1)
      (hρ' : ρ = constRingHom 1 (valueRingHom 1 ρ) + coordinate (0 : Fin 1) * ρ') :
      ψ ρ = constRingHom 2 (valueRingHom 1 ρ) + v * ψ ρ' := by
    conv_lhs => rw [hρ']
    rw [map_add, map_mul, g.sectionParameterHom_const, g.sectionParameterHom_coordinate]
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rintro q -
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L q
    have hexp := b.sum_repr (Submodule.Quotient.mk x)
    set ρ := b.repr (Submodule.Quotient.mk x) with hρ
    choose ρ' hρ' using fun i => Germ.exists_eq_const_add_coordinate_mul (ρ i)
    have hdiff : x - ∑ i, ψ (ρ i) * β i ∈ A := by
      rw [← Submodule.Quotient.eq, ← A.mkQ_apply (∑ i, ψ (ρ i) * β i), map_sum]
      conv_lhs => rw [← hexp]
      apply Finset.sum_congr rfl
      intro i _
      rw [A.mkQ_apply, ← hβ i, ← Submodule.Quotient.mk_smul, hsmul]
    have hxL : x - ∑ i, valueRingHom 1 (ρ i) • β i ∈ L := by
      apply hLmem _ (x - ∑ i, ψ (ρ i) * β i) hdiff (∑ i, ψ (ρ' i) * β i)
      have hsm (i : ι) : valueRingHom 1 (ρ i) • β i =
          constRingHom 2 (valueRingHom 1 (ρ i)) * β i := rfl
      simp only [hsm, fun i => hψρ (ρ i) (ρ' i) (hρ' i), add_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
      ring_nf
    have hq : (Submodule.Quotient.mk x : Germ 2 ⧸ L) = ∑ i, valueRingHom 1 (ρ i) • f i := by
      have h := (Submodule.Quotient.eq L).mpr hxL
      rw [h, ← L.mkQ_apply, map_sum]
      simp only [map_smul]
      rfl
    rw [hq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hli : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro κ hκ i
    have hmem : ∑ j, κ j • β j ∈ L := by
      rw [← Submodule.Quotient.mk_eq_zero, ← L.mkQ_apply, map_sum]
      simpa only [map_smul] using hκ
    obtain ⟨a, ha, y, hy⟩ := hLmem' _ hmem
    have hleft : (Submodule.Quotient.mk (∑ j, κ j • β j) : Germ 2 ⧸ A) =
        ∑ j, constRingHom 1 (κ j) • b j := by
      rw [← A.mkQ_apply, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [A.mkQ_apply, hmkconst, hβ j]
    have hright : (Submodule.Quotient.mk (∑ j, κ j • β j) : Germ 2 ⧸ A) =
        ∑ j, (coordinate (0 : Fin 1) * b.repr (Submodule.Quotient.mk y) j) • b j := by
      rw [hy, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero A).mpr ha, zero_add]
      have hvy : v * y = coordinate (0 : Fin 1) • y := by
        rw [hsmul, g.sectionParameterHom_coordinate]
      rw [hvy, Submodule.Quotient.mk_smul]
      conv_lhs => rw [← b.sum_repr (Submodule.Quotient.mk y)]
      rw [Finset.smul_sum]
      simp only [smul_smul]
    have hcoef := (Fintype.linearIndependent_iffₛ.mp b.linearIndependent)
      (fun j => constRingHom 1 (κ j))
      (fun j => coordinate (0 : Fin 1) * b.repr (Submodule.Quotient.mk y) j)
      (hleft.symm.trans hright) i
    have hval := congrArg (valueRingHom 1) hcoef
    rw [valueRingHom_const, map_mul, valueRingHom_coordinate, zero_mul] at hval
    exact hval
  let bL : Module.Basis ι ℂ (Germ 2 ⧸ L) := Module.Basis.mk hli hspan
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis bL]

end SectionImageFactorization

end OnLeConjecture.Analytic
