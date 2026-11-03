/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.JacobianPullback
public import OnLeConjecture.PlaneCurve.Intersection

/-!
# Milnor numbers and polar intersections of plane curve germs

This file defines the Jacobian ideal of a plane analytic germ, isolated
critical points, and the Milnor number. It also defines the polar ideal and
its intersection multiplicity and proves reductions for the two coordinate
parameters.
-/

public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic

/-- A plane analytic function germ is critical at the origin when its
differential at the origin vanishes. -/
@[expose] def IsCriticalAtOrigin (g : Germ 2) : Prop :=
  Germ.differential g = 0

/-- The Jacobian ideal of a plane analytic function germ. -/
@[expose] noncomputable def jacobianIdeal (g : Germ 2) : Ideal (Germ 2) :=
  pairIdeal (Germ.partialDerivative (0 : Fin 2) g)
    (Germ.partialDerivative (1 : Fin 2) g)

theorem jacobianIdeal_eq_pairIdeal (g : Germ 2) :
    jacobianIdeal g =
      pairIdeal (Germ.partialDerivative (0 : Fin 2) g)
        (Germ.partialDerivative (1 : Fin 2) g) :=
  rfl

/-- The Jacobian algebra has finite complex dimension. -/
@[expose] def HasFiniteJacobianAlgebra (g : Germ 2) : Prop :=
  Module.Finite ℂ (Germ 2 ⧸ jacobianIdeal g)

/-- A plane analytic germ has an isolated critical point at the origin when
the origin is critical and its Jacobian algebra has finite dimension. -/
@[expose] def HasIsolatedCriticalPoint (g : Germ 2) : Prop :=
  IsCriticalAtOrigin g ∧ HasFiniteJacobianAlgebra g

/-- The Milnor number is the complex dimension of the Jacobian algebra. -/
@[expose] noncomputable def milnorNumber (g : Germ 2)
    (h : HasIsolatedCriticalPoint g) : ℕ := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ jacobianIdeal g) := h.2
  exact Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal g)

/-- The polar ideal of `g` with parameter `u`. -/
@[expose] noncomputable def polarIdeal (g u : Germ 2) : Ideal (Germ 2) :=
  pairIdeal g (Germ.jacobian g u)

theorem polarIdeal_eq_pairIdeal (g u : Germ 2) :
    polarIdeal g u = pairIdeal g (Germ.jacobian g u) :=
  rfl

/-- The polar intersection of `g` with respect to `u` is finite when its
local intersection algebra has finite complex dimension. -/
@[expose] def HasFinitePolarIntersection (g u : Germ 2) : Prop :=
  Module.Finite ℂ (Germ 2 ⧸ polarIdeal g u)

/-- The intersection multiplicity of a germ with its polar curve. -/
@[expose] noncomputable def polarIntersectionMultiplicity (g u : Germ 2)
    (h : HasFinitePolarIntersection g u) : ℕ := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ polarIdeal g u) := h
  exact Module.finrank ℂ (Germ 2 ⧸ polarIdeal g u)

theorem isCriticalAtOrigin_iff_partialDerivative_mem_maximalIdeal
    (g : Germ 2) :
    IsCriticalAtOrigin g ↔
      ∀ i : Fin 2,
        Germ.partialDerivative i g ∈ Germ.maximalIdeal 2 := by
  constructor
  · intro h i
    change Germ.differential g = 0 at h
    rw [Germ.mem_maximalIdeal_iff,
      Germ.valueRingHom_partialDerivative]
    simp [h]
  · intro h
    rw [IsCriticalAtOrigin]
    have hzero (i : Fin 2) :
        Germ.differential g (Germ.coordinateVector i) = 0 := by
      have hi := Germ.mem_maximalIdeal_iff.mp (h i)
      rwa [Germ.valueRingHom_partialDerivative] at hi
    apply ContinuousLinearMap.ext
    intro v
    have hv :
        v = v 0 • Germ.coordinateVector (0 : Fin 2) +
          v 1 • Germ.coordinateVector (1 : Fin 2) := by
      ext i
      fin_cases i
      · simp [Germ.coordinateVector_apply]
      · simp [Germ.coordinateVector_apply]
    rw [hv]
    simp [hzero]

theorem isCriticalAtOrigin_iff_partialDerivatives_mem_maximalIdeal
    (g : Germ 2) :
    IsCriticalAtOrigin g ↔
      Germ.partialDerivative (0 : Fin 2) g ∈ Germ.maximalIdeal 2 ∧
        Germ.partialDerivative (1 : Fin 2) g ∈ Germ.maximalIdeal 2 := by
  rw [isCriticalAtOrigin_iff_partialDerivative_mem_maximalIdeal,
    Fin.forall_fin_two]

theorem hasFiniteJacobianAlgebra_iff_hasFiniteIntersection
    (g : Germ 2) :
    HasFiniteJacobianAlgebra g ↔
      HasFiniteIntersection
        (Germ.partialDerivative (0 : Fin 2) g)
        (Germ.partialDerivative (1 : Fin 2) g) := by
  rfl

theorem hasFiniteJacobianAlgebra_iff_exists_maximalIdeal_pow_le
    (g : Germ 2) :
    HasFiniteJacobianAlgebra g ↔
      ∃ N : ℕ, Germ.maximalIdeal 2 ^ N ≤ jacobianIdeal g := by
  rw [hasFiniteJacobianAlgebra_iff_hasFiniteIntersection,
    hasFiniteIntersection_iff_exists_maximalIdeal_pow_le,
    jacobianIdeal_eq_pairIdeal]

theorem HasIsolatedCriticalPoint.isCriticalAtOrigin {g : Germ 2}
    (h : HasIsolatedCriticalPoint g) : IsCriticalAtOrigin g :=
  h.1

theorem HasIsolatedCriticalPoint.hasFiniteJacobianAlgebra {g : Germ 2}
    (h : HasIsolatedCriticalPoint g) : HasFiniteJacobianAlgebra g :=
  h.2

theorem HasIsolatedCriticalPoint.hasFiniteIntersection {g : Germ 2}
    (h : HasIsolatedCriticalPoint g) :
    HasFiniteIntersection
      (Germ.partialDerivative (0 : Fin 2) g)
      (Germ.partialDerivative (1 : Fin 2) g) :=
  (hasFiniteJacobianAlgebra_iff_hasFiniteIntersection g).mp h.2

theorem HasIsolatedCriticalPoint.partialDerivative_mem_maximalIdeal
    {g : Germ 2} (h : HasIsolatedCriticalPoint g) (i : Fin 2) :
    Germ.partialDerivative i g ∈ Germ.maximalIdeal 2 :=
  (isCriticalAtOrigin_iff_partialDerivative_mem_maximalIdeal g).mp h.1 i

theorem HasIsolatedCriticalPoint.radical_jacobianIdeal_eq_maximalIdeal
    {g : Germ 2} (h : HasIsolatedCriticalPoint g) :
    (jacobianIdeal g).radical = Germ.maximalIdeal 2 := by
  rw [jacobianIdeal_eq_pairIdeal]
  exact
    (hasFiniteIntersection_iff_radical_pairIdeal_eq_maximalIdeal
      (h.partialDerivative_mem_maximalIdeal 0)
      (h.partialDerivative_mem_maximalIdeal 1)).mp
        h.hasFiniteIntersection

theorem hasIsolatedCriticalPoint_iff_radical_jacobianIdeal_eq_maximalIdeal
    (g : Germ 2) :
    HasIsolatedCriticalPoint g ↔
      (jacobianIdeal g).radical = Germ.maximalIdeal 2 := by
  constructor
  · exact HasIsolatedCriticalPoint.radical_jacobianIdeal_eq_maximalIdeal
  · intro hradical
    have hzero :
        Germ.partialDerivative (0 : Fin 2) g ∈ jacobianIdeal g := by
      rw [jacobianIdeal, pairIdeal]
      exact Ideal.subset_span (Set.mem_insert _ _)
    have hone :
        Germ.partialDerivative (1 : Fin 2) g ∈ jacobianIdeal g := by
      rw [jacobianIdeal, pairIdeal]
      exact Ideal.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hzeroMax :
        Germ.partialDerivative (0 : Fin 2) g ∈ Germ.maximalIdeal 2 := by
      rw [← hradical]
      exact Ideal.le_radical hzero
    have honeMax :
        Germ.partialDerivative (1 : Fin 2) g ∈ Germ.maximalIdeal 2 := by
      rw [← hradical]
      exact Ideal.le_radical hone
    refine ⟨(isCriticalAtOrigin_iff_partialDerivatives_mem_maximalIdeal g).mpr
      ⟨hzeroMax, honeMax⟩, ?_⟩
    rw [hasFiniteJacobianAlgebra_iff_hasFiniteIntersection]
    apply (hasFiniteIntersection_iff_radical_pairIdeal_eq_maximalIdeal
      hzeroMax honeMax).mpr
    rwa [← jacobianIdeal_eq_pairIdeal]

theorem milnorNumber_eq_finrank (g : Germ 2)
    (h : HasIsolatedCriticalPoint g) :
    milnorNumber g h = Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal g) := by
  rfl

theorem milnorNumber_eq_intersectionMultiplicity (g : Germ 2)
    (h : HasIsolatedCriticalPoint g) :
    milnorNumber g h =
      intersectionMultiplicity
        (Germ.partialDerivative (0 : Fin 2) g)
        (Germ.partialDerivative (1 : Fin 2) g)
        h.hasFiniteIntersection := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ jacobianIdeal g) := h.2
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ pairIdeal
        (Germ.partialDerivative (0 : Fin 2) g)
        (Germ.partialDerivative (1 : Fin 2) g)) :=
    h.hasFiniteIntersection
  change Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal g) =
    Module.finrank ℂ
      (Germ 2 ⧸ pairIdeal
        (Germ.partialDerivative (0 : Fin 2) g)
        (Germ.partialDerivative (1 : Fin 2) g))
  rw [jacobianIdeal_eq_pairIdeal]

theorem milnorNumber_pos (g : Germ 2)
    (h : HasIsolatedCriticalPoint g) :
    0 < milnorNumber g h := by
  rw [milnorNumber_eq_intersectionMultiplicity]
  exact intersectionMultiplicity_pos
    (h.partialDerivative_mem_maximalIdeal 0)
    (h.partialDerivative_mem_maximalIdeal 1)
    h.hasFiniteIntersection

theorem pairIdeal_neg_right (g h : Germ 2) :
    pairIdeal g (-h) = pairIdeal g h := by
  rw [pairIdeal, pairIdeal, Ideal.span_pair_neg]

theorem pairIdeal_mul_unit_right (g h a : Germ 2)
    (ha : IsUnit a) :
    pairIdeal g (h * a) = pairIdeal g h := by
  rw [pairIdeal, pairIdeal, Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit ha]

/-- An invertible change of two generators preserves their pair ideal. -/
theorem pairIdeal_linear_change (x y a b c d : Germ 2)
    (hdet : IsUnit (a * d - b * c)) :
    pairIdeal (x * a + y * c) (x * b + y * d) =
      pairIdeal x y := by
  rcases isUnit_iff_exists_inv.mp hdet with ⟨r, hr⟩
  apply le_antisymm
  · rw [pairIdeal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact Ideal.mem_span_pair.mpr ⟨a, c, by ring⟩
    · rw [hz]
      exact Ideal.mem_span_pair.mpr ⟨b, d, by ring⟩
  · rw [pairIdeal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      apply Ideal.mem_span_pair.mpr
      refine ⟨d * r, -c * r, ?_⟩
      calc
        (d * r) * (x * a + y * c) +
              (-c * r) * (x * b + y * d) =
            x * ((a * d - b * c) * r) := by ring
        _ = x := by rw [hr, mul_one]
    · rw [hz]
      apply Ideal.mem_span_pair.mpr
      refine ⟨-b * r, a * r, ?_⟩
      calc
        (-b * r) * (x * a + y * c) +
              (a * r) * (x * b + y * d) =
            y * ((a * d - b * c) * r) := by ring
        _ = y := by rw [hr, mul_one]

theorem hasFiniteIntersection_neg_right_iff (g h : Germ 2) :
    HasFiniteIntersection g (-h) ↔ HasFiniteIntersection g h := by
  rw [HasFiniteIntersection, HasFiniteIntersection,
    pairIdeal_neg_right]

theorem intersectionMultiplicity_neg_right (g h : Germ 2)
    (hfinite : HasFiniteIntersection g h) :
    intersectionMultiplicity g (-h)
        ((hasFiniteIntersection_neg_right_iff g h).mpr hfinite) =
      intersectionMultiplicity g h hfinite := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ pairIdeal g (-h)) :=
    (hasFiniteIntersection_neg_right_iff g h).mpr hfinite
  let _ : Module.Finite ℂ (Germ 2 ⧸ pairIdeal g h) := hfinite
  change Module.finrank ℂ (Germ 2 ⧸ pairIdeal g (-h)) =
    Module.finrank ℂ (Germ 2 ⧸ pairIdeal g h)
  rw [pairIdeal_neg_right]

theorem isCriticalAtOrigin_pullback_iff
    (e : PointedEquivGerm 2) (g : Germ 2) :
    IsCriticalAtOrigin (e.pullbackAlgEquiv g) ↔
      IsCriticalAtOrigin g := by
  change
    Germ.differential (Germ.compPointed g e.forward) = 0 ↔
      Germ.differential g = 0
  rw [Germ.differential_compPointed]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg
      (fun L : Source 2 →L[ℂ] ℂ =>
        L (e.inverse.differential v)) h
    have hinverse := congrArg
      (fun L : Source 2 →L[ℂ] Source 2 => L v)
      e.differential_forward_inverse
    change e.forward.differential (e.inverse.differential v) = v at hinverse
    change Germ.differential g
      (e.forward.differential (e.inverse.differential v)) = 0 at hv
    rwa [hinverse] at hv
  · intro h
    rw [h]
    rfl

/-- Pullback by a source equivalence carries the Jacobian ideal to the
Jacobian ideal of the pulled back germ. -/
theorem map_jacobianIdeal_pullbackAlgEquiv
    (e : PointedEquivGerm 2) (g : Germ 2) :
    Ideal.map e.pullbackAlgEquiv.toRingEquiv.toRingHom
        (jacobianIdeal g) =
      jacobianIdeal (e.pullbackAlgEquiv g) := by
  rw [jacobianIdeal, map_pairIdeal_pullbackAlgEquiv, jacobianIdeal]
  change
    pairIdeal
        (Germ.compPointed (Germ.partialDerivative (0 : Fin 2) g)
          e.forward)
        (Germ.compPointed (Germ.partialDerivative (1 : Fin 2) g)
          e.forward) =
      pairIdeal
        (Germ.partialDerivative (0 : Fin 2)
          (Germ.compPointed g e.forward))
        (Germ.partialDerivative (1 : Fin 2)
          (Germ.compPointed g e.forward))
  rw [Germ.partialDerivative_compPointed,
    Germ.partialDerivative_compPointed]
  symm
  exact pairIdeal_linear_change _ _ _ _ _ _
    (Germ.PointedEquivGerm.coordinateJacobian_isUnit e)

theorem hasFiniteJacobianAlgebra_pullback_iff
    (e : PointedEquivGerm 2) (g : Germ 2) :
    HasFiniteJacobianAlgebra (e.pullbackAlgEquiv g) ↔
      HasFiniteJacobianAlgebra g := by
  let quotientEquiv : (Germ 2 ⧸ jacobianIdeal g) ≃ₐ[ℂ]
      Germ 2 ⧸ jacobianIdeal (e.pullbackAlgEquiv g) :=
    Ideal.quotientEquivAlg (jacobianIdeal g)
      (jacobianIdeal (e.pullbackAlgEquiv g))
      e.pullbackAlgEquiv
      (map_jacobianIdeal_pullbackAlgEquiv e g).symm
  constructor
  · intro h
    let _ : Module.Finite ℂ
        (Germ 2 ⧸ jacobianIdeal (e.pullbackAlgEquiv g)) := h
    exact Module.Finite.equiv quotientEquiv.symm.toLinearEquiv
  · intro h
    let _ : Module.Finite ℂ (Germ 2 ⧸ jacobianIdeal g) := h
    exact Module.Finite.equiv quotientEquiv.toLinearEquiv

theorem HasIsolatedCriticalPoint.pullback
    (e : PointedEquivGerm 2) {g : Germ 2}
    (h : HasIsolatedCriticalPoint g) :
    HasIsolatedCriticalPoint (e.pullbackAlgEquiv g) := by
  exact ⟨(isCriticalAtOrigin_pullback_iff e g).mpr h.1,
    (hasFiniteJacobianAlgebra_pullback_iff e g).mpr h.2⟩

theorem hasIsolatedCriticalPoint_pullback_iff
    (e : PointedEquivGerm 2) (g : Germ 2) :
    HasIsolatedCriticalPoint (e.pullbackAlgEquiv g) ↔
      HasIsolatedCriticalPoint g := by
  rw [HasIsolatedCriticalPoint, HasIsolatedCriticalPoint,
    isCriticalAtOrigin_pullback_iff,
    hasFiniteJacobianAlgebra_pullback_iff]

/-- Analytic source coordinate changes preserve the Milnor number. -/
theorem milnorNumber_pullback (e : PointedEquivGerm 2)
    (g : Germ 2) (h : HasIsolatedCriticalPoint g) :
    milnorNumber g h =
      milnorNumber (e.pullbackAlgEquiv g) (h.pullback e) := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ jacobianIdeal g) := h.2
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ jacobianIdeal (e.pullbackAlgEquiv g)) :=
    (h.pullback e).2
  change Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal g) =
    Module.finrank ℂ
      (Germ 2 ⧸ jacobianIdeal (e.pullbackAlgEquiv g))
  exact Germ.quotient_finrank_eq_of_map_eq
    (jacobianIdeal g) (jacobianIdeal (e.pullbackAlgEquiv g))
    e.pullbackAlgEquiv (map_jacobianIdeal_pullbackAlgEquiv e g)

theorem hasFinitePolarIntersection_iff_hasFiniteIntersection
    (g u : Germ 2) :
    HasFinitePolarIntersection g u ↔
      HasFiniteIntersection g (Germ.jacobian g u) := by
  rfl

theorem polarIntersectionMultiplicity_eq_intersectionMultiplicity
    (g u : Germ 2) (h : HasFinitePolarIntersection g u) :
    polarIntersectionMultiplicity g u h =
      intersectionMultiplicity g (Germ.jacobian g u)
        ((hasFinitePolarIntersection_iff_hasFiniteIntersection g u).mp h) := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ polarIdeal g u) := h
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ pairIdeal g (Germ.jacobian g u)) :=
    (hasFinitePolarIntersection_iff_hasFiniteIntersection g u).mp h
  change Module.finrank ℂ (Germ 2 ⧸ polarIdeal g u) =
    Module.finrank ℂ
      (Germ 2 ⧸ pairIdeal g (Germ.jacobian g u))
  rw [polarIdeal_eq_pairIdeal]

/-- Pullback by a source equivalence carries a polar ideal to the polar ideal
of the two pulled back germs. -/
theorem map_polarIdeal_pullbackAlgEquiv
    (e : PointedEquivGerm 2) (g u : Germ 2) :
    Ideal.map e.pullbackAlgEquiv.toRingEquiv.toRingHom (polarIdeal g u) =
      polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u) := by
  rw [polarIdeal, map_pairIdeal_pullbackAlgEquiv, polarIdeal]
  change
    pairIdeal (Germ.compPointed g e.forward)
        (Germ.compPointed (Germ.jacobian g u) e.forward) =
      pairIdeal (Germ.compPointed g e.forward)
        (Germ.jacobian (Germ.compPointed g e.forward)
          (Germ.compPointed u e.forward))
  rw [Germ.jacobian_compPointed]
  exact (pairIdeal_mul_unit_right _ _ _
    (Germ.PointedEquivGerm.coordinateJacobian_isUnit e)).symm

theorem hasFinitePolarIntersection_pullback_iff
    (e : PointedEquivGerm 2) (g u : Germ 2) :
    HasFinitePolarIntersection
        (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u) ↔
      HasFinitePolarIntersection g u := by
  let quotientEquiv : (Germ 2 ⧸ polarIdeal g u) ≃ₐ[ℂ]
      Germ 2 ⧸
        polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u) :=
    Ideal.quotientEquivAlg (polarIdeal g u)
      (polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u))
      e.pullbackAlgEquiv
      (map_polarIdeal_pullbackAlgEquiv e g u).symm
  constructor
  · intro h
    let _ : Module.Finite ℂ
        (Germ 2 ⧸
          polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u)) := h
    exact Module.Finite.equiv quotientEquiv.symm.toLinearEquiv
  · intro h
    let _ : Module.Finite ℂ (Germ 2 ⧸ polarIdeal g u) := h
    exact Module.Finite.equiv quotientEquiv.toLinearEquiv

theorem HasFinitePolarIntersection.pullback
    (e : PointedEquivGerm 2) {g u : Germ 2}
    (h : HasFinitePolarIntersection g u) :
    HasFinitePolarIntersection
      (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u) :=
  (hasFinitePolarIntersection_pullback_iff e g u).mpr h

/-- Analytic source coordinate changes preserve polar intersection
multiplicity. -/
theorem polarIntersectionMultiplicity_pullback
    (e : PointedEquivGerm 2) (g u : Germ 2)
    (h : HasFinitePolarIntersection g u) :
    polarIntersectionMultiplicity g u h =
      polarIntersectionMultiplicity
        (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u)
        (h.pullback e) := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ polarIdeal g u) := h
  let _ : Module.Finite ℂ
      (Germ 2 ⧸
        polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u)) :=
    h.pullback e
  change Module.finrank ℂ (Germ 2 ⧸ polarIdeal g u) =
    Module.finrank ℂ
      (Germ 2 ⧸
        polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u))
  exact Germ.quotient_finrank_eq_of_map_eq
    (polarIdeal g u)
    (polarIdeal (e.pullbackAlgEquiv g) (e.pullbackAlgEquiv u))
    e.pullbackAlgEquiv (map_polarIdeal_pullbackAlgEquiv e g u)

theorem jacobian_mem_maximalIdeal_of_isCriticalAtOrigin
    {g : Germ 2} (h : IsCriticalAtOrigin g) (u : Germ 2) :
    Germ.jacobian g u ∈ Germ.maximalIdeal 2 := by
  change Germ.differential g = 0 at h
  rw [Germ.mem_maximalIdeal_iff, Germ.jacobian_eq]
  simp only [map_sub, map_mul,
    Germ.valueRingHom_partialDerivative]
  simp [h]

theorem polarIntersectionMultiplicity_pos {g u : Germ 2}
    (hg : g ∈ Germ.maximalIdeal 2) (hcritical : IsCriticalAtOrigin g)
    (hfinite : HasFinitePolarIntersection g u) :
    0 < polarIntersectionMultiplicity g u hfinite := by
  rw [polarIntersectionMultiplicity_eq_intersectionMultiplicity]
  exact intersectionMultiplicity_pos hg
    (jacobian_mem_maximalIdeal_of_isCriticalAtOrigin hcritical u)
    ((hasFinitePolarIntersection_iff_hasFiniteIntersection g u).mp hfinite)

theorem jacobian_coordinate_zero_left (g : Germ 2) :
    Germ.jacobian (Germ.coordinate (0 : Fin 2)) g =
      Germ.partialDerivative (1 : Fin 2) g := by
  rw [Germ.jacobian_swap, Germ.jacobian_coordinate_zero_right]
  ring

theorem jacobian_coordinate_one_left (g : Germ 2) :
    Germ.jacobian (Germ.coordinate (1 : Fin 2)) g =
      -Germ.partialDerivative (0 : Fin 2) g := by
  rw [Germ.jacobian_swap, Germ.jacobian_coordinate_one_right]

theorem polarIdeal_coordinate_zero (g : Germ 2) :
    polarIdeal g (Germ.coordinate (0 : Fin 2)) =
      pairIdeal g (Germ.partialDerivative (1 : Fin 2) g) := by
  rw [polarIdeal, Germ.jacobian_coordinate_zero_right,
    pairIdeal_neg_right]

theorem polarIdeal_coordinate_one (g : Germ 2) :
    polarIdeal g (Germ.coordinate (1 : Fin 2)) =
      pairIdeal g (Germ.partialDerivative (0 : Fin 2) g) := by
  rw [polarIdeal, Germ.jacobian_coordinate_one_right]

theorem hasFinitePolarIntersection_coordinate_zero_iff (g : Germ 2) :
    HasFinitePolarIntersection g (Germ.coordinate (0 : Fin 2)) ↔
      HasFiniteIntersection g
        (Germ.partialDerivative (1 : Fin 2) g) := by
  rw [HasFinitePolarIntersection, HasFiniteIntersection,
    polarIdeal_coordinate_zero]

theorem hasFinitePolarIntersection_coordinate_one_iff (g : Germ 2) :
    HasFinitePolarIntersection g (Germ.coordinate (1 : Fin 2)) ↔
      HasFiniteIntersection g
        (Germ.partialDerivative (0 : Fin 2) g) := by
  rw [HasFinitePolarIntersection, HasFiniteIntersection,
    polarIdeal_coordinate_one]

theorem polarIntersectionMultiplicity_coordinate_zero (g : Germ 2)
    (h : HasFinitePolarIntersection g
      (Germ.coordinate (0 : Fin 2))) :
    polarIntersectionMultiplicity g
        (Germ.coordinate (0 : Fin 2)) h =
      intersectionMultiplicity g
        (Germ.partialDerivative (1 : Fin 2) g)
        ((hasFinitePolarIntersection_coordinate_zero_iff g).mp h) := by
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ polarIdeal g (Germ.coordinate (0 : Fin 2))) := h
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ pairIdeal g
        (Germ.partialDerivative (1 : Fin 2) g)) :=
    (hasFinitePolarIntersection_coordinate_zero_iff g).mp h
  change Module.finrank ℂ
      (Germ 2 ⧸ polarIdeal g (Germ.coordinate (0 : Fin 2))) =
    Module.finrank ℂ
      (Germ 2 ⧸ pairIdeal g
        (Germ.partialDerivative (1 : Fin 2) g))
  rw [polarIdeal_coordinate_zero]

theorem polarIntersectionMultiplicity_coordinate_one (g : Germ 2)
    (h : HasFinitePolarIntersection g
      (Germ.coordinate (1 : Fin 2))) :
    polarIntersectionMultiplicity g
        (Germ.coordinate (1 : Fin 2)) h =
      intersectionMultiplicity g
        (Germ.partialDerivative (0 : Fin 2) g)
        ((hasFinitePolarIntersection_coordinate_one_iff g).mp h) := by
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ polarIdeal g (Germ.coordinate (1 : Fin 2))) := h
  let _ : Module.Finite ℂ
      (Germ 2 ⧸ pairIdeal g
        (Germ.partialDerivative (0 : Fin 2) g)) :=
    (hasFinitePolarIntersection_coordinate_one_iff g).mp h
  change Module.finrank ℂ
      (Germ 2 ⧸ polarIdeal g (Germ.coordinate (1 : Fin 2))) =
    Module.finrank ℂ
      (Germ 2 ⧸ pairIdeal g
        (Germ.partialDerivative (0 : Fin 2) g))
  rw [polarIdeal_coordinate_one]

theorem jacobian_add_right (g u v : Germ 2) :
    Germ.jacobian g (u + v) =
      Germ.jacobian g u + Germ.jacobian g v := by
  simp only [Germ.jacobian_eq, Germ.partialDerivative_add]
  ring

theorem jacobian_mul_right (g u v : Germ 2) :
    Germ.jacobian g (u * v) =
      u * Germ.jacobian g v + v * Germ.jacobian g u := by
  simp only [Germ.jacobian_eq, Germ.partialDerivative_mul]
  ring

theorem jacobian_mul_self_right (g q : Germ 2) :
    Germ.jacobian g (q * g) = g * Germ.jacobian g q := by
  rw [jacobian_mul_right, Germ.jacobian_self]
  ring

theorem jacobian_add_mul_self_right (g u q : Germ 2) :
    Germ.jacobian g (u + q * g) =
      Germ.jacobian g u + g * Germ.jacobian g q := by
  rw [jacobian_add_right, jacobian_mul_self_right]

/-- Adding a multiple of the curve equation to the parameter preserves the
polar ideal. -/
theorem polarIdeal_add_mul_self_right (g u q : Germ 2) :
    polarIdeal g (u + q * g) = polarIdeal g u := by
  rw [polarIdeal, polarIdeal, jacobian_add_mul_self_right,
    pairIdeal, pairIdeal]
  exact Ideal.span_pair_add_left_mul _ _ _

theorem hasFinitePolarIntersection_add_mul_self_right_iff
    (g u q : Germ 2) :
    HasFinitePolarIntersection g (u + q * g) ↔
      HasFinitePolarIntersection g u := by
  rw [HasFinitePolarIntersection, HasFinitePolarIntersection,
    polarIdeal_add_mul_self_right]

theorem polarIntersectionMultiplicity_add_mul_self_right
    (g u q : Germ 2) (h : HasFinitePolarIntersection g u) :
    polarIntersectionMultiplicity g (u + q * g)
        ((hasFinitePolarIntersection_add_mul_self_right_iff g u q).mpr h) =
      polarIntersectionMultiplicity g u h := by
  let _ : Module.Finite ℂ (Germ 2 ⧸ polarIdeal g (u + q * g)) :=
    (hasFinitePolarIntersection_add_mul_self_right_iff g u q).mpr h
  let _ : Module.Finite ℂ (Germ 2 ⧸ polarIdeal g u) := h
  change Module.finrank ℂ (Germ 2 ⧸ polarIdeal g (u + q * g)) =
    Module.finrank ℂ (Germ 2 ⧸ polarIdeal g u)
  rw [polarIdeal_add_mul_self_right]

end OnLeConjecture.PlaneCurve
