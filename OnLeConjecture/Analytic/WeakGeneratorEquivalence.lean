/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveWeakIdealFiniteColength

/-!
# Source equivalence and a common unit for weak generator families

The relation retains an identity for every generator, not merely an
equality of generated ideals. Analytic projective blowup lifts preserve
this relation, with the corresponding old projective point constructed
from the new one.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The same analytic source equivalence and common unit act on every
member of the specified generator family. -/
@[expose] def WeakGeneratorEquivalence {ι : Type*} (F G : ι → Germ 2) : Prop :=
  ∃ (e : PointedEquivGerm 2) (U : Germ 2), IsUnit U ∧
    ∀ i, G i = U * e.forward.pullbackRingHom (F i)

namespace WeakGeneratorEquivalence

variable {ι : Type*} {F G H : ι → Germ 2}

theorem refl (F : ι → Germ 2) : WeakGeneratorEquivalence F F := by
  refine ⟨PointedEquivGerm.identity 2, 1, isUnit_one, ?_⟩
  intro i
  rw [one_mul, PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity]
  rfl

theorem of_pullback (F : ι → Germ 2) (e : PointedEquivGerm 2) :
    WeakGeneratorEquivalence F (fun i => e.forward.pullbackRingHom (F i)) :=
  ⟨e, 1, isUnit_one, fun _ => (one_mul _).symm⟩

theorem symm (h : WeakGeneratorEquivalence F G) : WeakGeneratorEquivalence G F := by
  obtain ⟨e, U, ⟨u, rfl⟩, hG⟩ := h
  refine ⟨e.symm, e.inverse.pullbackRingHom (↑(u⁻¹) : Germ 2),
    (Units.isUnit u⁻¹).map e.inverse.pullbackRingHom, ?_⟩
  intro i
  change F i = e.inverse.pullbackRingHom (↑(u⁻¹) : Germ 2) *
    e.inverse.pullbackRingHom (G i)
  rw [← map_mul, hG, ← mul_assoc, Units.inv_mul, one_mul]
  change F i = e.pullbackAlgEquiv.symm (e.pullbackAlgEquiv (F i))
  exact (e.pullbackAlgEquiv.symm_apply_apply _).symm

theorem trans (hFG : WeakGeneratorEquivalence F G) (hGH : WeakGeneratorEquivalence G H) :
    WeakGeneratorEquivalence F H := by
  obtain ⟨e, U, hU, hG⟩ := hFG
  obtain ⟨d, V, hV, hH⟩ := hGH
  refine ⟨e.comp d, V * d.forward.pullbackRingHom U,
    hV.mul (hU.map d.forward.pullbackRingHom), ?_⟩
  intro i
  change H i = (V * d.forward.pullbackRingHom U) *
    (e.forward.comp d.forward).pullbackRingHom (F i)
  rw [hH, hG, map_mul, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
  ring

theorem mem_pow_iff (h : WeakGeneratorEquivalence F G) (i : ι) (k : ℕ) :
    G i ∈ maximalIdeal 2 ^ k ↔ F i ∈ maximalIdeal 2 ^ k := by
  obtain ⟨e, U, hU, hG⟩ := h
  rw [hG, Ideal.unit_mul_mem_iff_mem _ hU, e.pullback_mem_maximalIdeal_pow_iff]

theorem finite_colength (h : WeakGeneratorEquivalence F G)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range G)) := by
  obtain ⟨e, U, hU, hG⟩ := h
  have hfun : G = fun i => U * e.forward.pullbackRingHom (F i) := funext hG
  rw [hfun, span_range_unit_mul U hU]
  exact pullback_generatorIdeal_quotient_moduleFinite e F hfinite

/-- Every chart of the changed family corresponds to a projective chart
of the original family, with exact common-unit identities for its weak
generators. The old chart and the analytic equivalence are constructed. -/
theorem exists_projective_weak_equivalence
    (h : WeakGeneratorEquivalence F G) (m : ℕ)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m)
    (hG : ∀ i, G i ∈ maximalIdeal 2 ^ m) (s : Option ℂ) :
    ∃ t : Option ℂ, WeakGeneratorEquivalence
      (projectiveWeakGenerators m F hF t) (projectiveWeakGenerators m G hG s) := by
  obtain ⟨e, U, hU, hGF⟩ := h
  let e' := e.comp (projectiveChartSource s)
  obtain ⟨t, E, V, hV, _hEy, _hcomm, hweak, _hideal, _horder⟩ :=
    exists_twoChart_weakIdeal_equivalence e' (projectiveChartCenter s) m F hF
  let B := (projectiveChartSource s).forward.comp
    (pointBlowupChartGerm (projectiveChartCenter s))
  refine ⟨t, E, B.pullbackRingHom U * V ^ m,
    (hU.map B.pullbackRingHom).mul (hV.pow m), ?_⟩
  intro i
  have hpull : (projectiveChartSource s).forward.pullbackRingHom
      (e.forward.pullbackRingHom (F i)) = e'.forward.pullbackRingHom (F i) := by
    change _ = (e.forward.comp (projectiveChartSource s).forward).pullbackRingHom (F i)
    rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
  apply pointBlowupTransform_unique (projectiveChartCenter s) m
    ((projectiveChartSource s).forward.pullbackRingHom (G i))
    (projectiveWeakGenerators m G hG s i) _
    (pointBlowupTransform_factor (projectiveChartCenter s) m _ _)
  rw [hGF, map_mul, hpull, map_mul,
    pointBlowupTransform_factor (projectiveChartCenter s) m _
      (e'.forward.pullback_mem_maximalIdeal_pow (hF i)), hweak]
  change (pointBlowupChartGerm (projectiveChartCenter s)).pullbackRingHom
      ((projectiveChartSource s).forward.pullbackRingHom U) *
      (coordinate (1 : Fin 2) ^ m * (V ^ m *
        E.forward.pullbackRingHom (projectiveWeakGenerators m F hF t i))) =
    coordinate (1 : Fin 2) ^ m *
      ((B.pullbackRingHom U * V ^ m) *
        E.forward.pullbackRingHom (projectiveWeakGenerators m F hF t i))
  dsimp only [B]
  rw [PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
  ring

end WeakGeneratorEquivalence

end OnLeConjecture.Analytic
