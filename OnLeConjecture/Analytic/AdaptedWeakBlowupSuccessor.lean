/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakBlowupTermination
public import OnLeConjecture.Analytic.FiniteIdealRegularCoordinates
public import OnLeConjecture.Analytic.FiniteExceptionalBasepoints

/-!
# Construction of adapted weak-blowup successors

A proper finite-colength ideal admits the regular coordinates required by
`AdaptedWeakIdealState`. At each common exceptional zero, its analytic weak
ideal admits a successor state. If the order is unchanged, the existing
coordinates are already regular and no source change is needed.

Source changes here are recorded after the weak transform. Translating
these states into point-basis records requires separate coordinate
transport and is not asserted by this module.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace AdaptedWeakIdealState

variable {ι : Type*} [Fintype ι]

theorem exists_of_finite_colength
    (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    ∃ (e : PointedEquivGerm 2) (s : AdaptedWeakIdealState ι),
      ∀ i, s.generators i = e.forward.pullbackRingHom (F i) := by
  obtain ⟨m, e, N, hm, horder, ⟨i, hregular, hexact⟩, hN, _⟩ :=
    exists_regular_coordinates_for_finite_ideal F hproper hfinite
  exact ⟨e, {
    generators := fun i => e.forward.pullbackRingHom (F i)
    multiplicity := m
    multiplicity_pos := hm
    generator_mem := horder
    distinguished := i
    distinguished_exact := hexact
    distinguished_regular := hregular
    finite_colength := quotient_moduleFinite_of_maximalIdeal_pow_le _ hN
  }, fun _ => rfl⟩

@[expose] noncomputable def weakGenerators (s : AdaptedWeakIdealState ι) (ζ : ℂ) :
    ι → Germ 2 :=
  fun i => pointBlowupTransform ζ s.multiplicity (s.generators i) (s.generator_mem i)

theorem weakGenerators_factor (s : AdaptedWeakIdealState ι) (ζ : ℂ) (i : ι) :
    (pointBlowupChartGerm ζ).pullbackRingHom (s.generators i) =
      coordinate (1 : Fin 2) ^ s.multiplicity * s.weakGenerators ζ i :=
  pointBlowupTransform_factor ζ s.multiplicity (s.generators i) (s.generator_mem i)

theorem weakGenerators_finite_colength (s : AdaptedWeakIdealState ι) (ζ : ℂ) :
    Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range (s.weakGenerators ζ))) :=
  weakIdeal_quotient_moduleFinite ζ s.multiplicity s.generators (s.weakGenerators ζ)
    s.finite_colength s.generator_mem ⟨s.distinguished, s.distinguished_exact⟩
    (s.weakGenerators_factor ζ)

/-- A successor retains the chosen exceptional point and the subsequent
source equivalence. At equal order that equivalence fixes the parameter. -/
@[expose] def SuccessorAt (ζ : ℂ) (child parent : AdaptedWeakIdealState ι) : Prop :=
  ∃ e : PointedEquivGerm 2,
    (∀ i, child.generators i = e.forward.pullbackRingHom (parent.weakGenerators ζ i)) ∧
    (child.multiplicity = parent.multiplicity →
      e.forward.pullbackRingHom (coordinate (1 : Fin 2)) = coordinate 1)

theorem step_of_successorAt {ζ : ℂ} {child parent : AdaptedWeakIdealState ι}
    (h : SuccessorAt ζ child parent) : Step child parent := by
  obtain ⟨e, hgenerators, hpreserve⟩ := h
  exact ⟨ζ, e, parent.weakGenerators ζ, parent.weakGenerators_factor ζ,
    hgenerators, hpreserve⟩

theorem exists_successorAt_of_common_zero
    (parent : AdaptedWeakIdealState ι) (ζ : ℂ)
    (hproper : ∀ i, parent.weakGenerators ζ i ∈ maximalIdeal 2) :
    ∃ child : AdaptedWeakIdealState ι, SuccessorAt ζ child parent := by
  obtain ⟨e, child, hchild⟩ := exists_of_finite_colength (parent.weakGenerators ζ)
    hproper (parent.weakGenerators_finite_colength ζ)
  by_cases horder : child.multiplicity = parent.multiplicity
  · have hmem : ∀ i, parent.weakGenerators ζ i ∈
        maximalIdeal 2 ^ parent.multiplicity := by
      intro i
      have h := child.generator_mem i
      rw [hchild, horder] at h
      exact (e.pullback_mem_maximalIdeal_pow_iff _).mp h
    have hexact := pointBlowupTransform_not_mem_succ ζ parent.multiplicity
      (parent.generators parent.distinguished) (parent.weakGenerators ζ parent.distinguished)
      (parent.generator_mem _) parent.distinguished_exact (parent.weakGenerators_factor ζ _)
    have hregular := pointBlowupTransform_regular_of_full_order ζ parent.multiplicity
      (parent.generators parent.distinguished) (parent.weakGenerators ζ parent.distinguished)
      (parent.generator_mem _) parent.distinguished_exact (hmem _)
      (parent.weakGenerators_factor ζ _)
    let raw : AdaptedWeakIdealState ι := {
      generators := parent.weakGenerators ζ
      multiplicity := parent.multiplicity
      multiplicity_pos := parent.multiplicity_pos
      generator_mem := hmem
      distinguished := parent.distinguished
      distinguished_exact := hexact
      distinguished_regular := hregular
      finite_colength := parent.weakGenerators_finite_colength ζ
    }
    refine ⟨raw, PointedEquivGerm.identity 2, ?_, ?_⟩
    · intro i
      rw [PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity]
      rfl
    · intro _
      rw [PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity]
      rfl
  · exact ⟨child, e, hchild, fun h => (horder h).elim⟩

theorem exists_exceptional_finset (s : AdaptedWeakIdealState ι) :
    ∃ points : Finset ℂ, points.card ≤ s.multiplicity ∧
      ∀ ζ, ζ ∈ points ↔ ∀ i, s.weakGenerators ζ i ∈ maximalIdeal 2 :=
  exists_finiteExceptionalBasepoint_finset s.multiplicity s.generators s.generator_mem
    ⟨s.distinguished, s.distinguished_exact⟩

theorem complementary_weak_ideal_is_unit (s : AdaptedWeakIdealState ι) :
    none ∉ projectiveExceptionalBasepointSet s.multiplicity s.generators s.generator_mem :=
  none_not_mem_projectiveExceptionalBasepointSet_of_regular s.multiplicity
    s.generators s.generator_mem ⟨s.distinguished, s.distinguished_regular⟩

end AdaptedWeakIdealState

end OnLeConjecture.Analytic
