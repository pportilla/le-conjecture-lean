/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.PlaneCurve.AnalyticBranchCount
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Analytic coordinate invariance of branch count

An analytic source equivalence induces a bijection of irreducible
associate classes dividing an equation. It therefore preserves the
number of analytic branches.
-/

public section

namespace OnLeConjecture.PlaneCurve

open Analytic UniqueFactorizationMonoid

private noncomputable def branchAssociatesEquiv (e : Germ 2 ≃+* Germ 2) :
    Associates (Germ 2) ≃* Associates (Germ 2) where
  toEquiv := Quotient.congr e.toEquiv (by
    intro f g
    change Associated f g ↔ Associated (e f) (e g)
    constructor
    · exact fun h ↦ h.map e.toMonoidHom
    · intro h
      have hi := h.map e.symm.toMonoidHom
      change Associated (e.symm (e f)) (e.symm (e g)) at hi
      simpa only [RingEquiv.symm_apply_apply] using hi)
  map_mul' := by
    rintro ⟨f⟩ ⟨g⟩
    change Associates.mk (e (f * g)) = Associates.mk (e f * e g)
    rw [map_mul]

/-- Ring equivalences preserve the number of distinct irreducible
analytic factors, including the zero and unit cases. -/
theorem irreducibleBranchCount_ringEquiv (e : Germ 2 ≃+* Germ 2) (f : Germ 2) :
    irreducibleBranchCount f = irreducibleBranchCount (e f) := by
  classical
  let E := branchAssociatesEquiv e
  have he : ∀ z, normalize (E z) = E (normalize z) := by
    intro z
    simp only [normalize_eq]
  let factors : {z // z ∈ (normalizedFactors (Associates.mk f)).toFinset} ≃
      {z // z ∈ (normalizedFactors (E (Associates.mk f))).toFinset} := by
    simpa only [Multiset.mem_toFinset] using normalizedFactorsEquiv (f := E) he (Associates.mk f)
  have hcard := Fintype.card_congr factors
  have hE : E (Associates.mk f) = Associates.mk (e f) := by rfl
  simpa only [Fintype.card_coe, hE, irreducibleBranchCount] using hcard

/-- Pullback by an actual analytic source equivalence preserves branch
count. -/
theorem irreducibleBranchCount_pullback (e : PointedEquivGerm 2) (f : Germ 2) :
    irreducibleBranchCount f = irreducibleBranchCount (e.forward.pullbackRingHom f) :=
  irreducibleBranchCount_ringEquiv e.pullbackRingEquiv f

/-- An irreducible analytic equation has one branch. -/
theorem irreducibleBranchCount_eq_one_of_irreducible (f : Germ 2) (hf : Irreducible f) :
    irreducibleBranchCount f = 1 := by
  classical
  rw [irreducibleBranchCount, normalizedFactors_irreducible (Associates.irreducible_mk.mpr hf)]
  simp

end OnLeConjecture.PlaneCurve
