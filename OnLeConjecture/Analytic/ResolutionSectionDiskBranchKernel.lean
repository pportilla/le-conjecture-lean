/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionDiskBranchGerm

/-! # The exact local equation of the retained diskBranch

The already chosen source disk differs from the earlier transverse branch
by an invertible holomorphic source germ. Its pullback kernel is therefore
exactly the principal ideal of the assembled local section equation.
The holomorphic source change preserves positive branch orientation. The
hole boundary retains the opposite, clockwise orientation proved earlier.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}

/-- For any of the retained transverse coordinates and branch satisfying
its actual restriction identity, the SAME diskBranch differs by a source
analytic equivalence. -/
theorem diskBranchGerm_eq_transverse_comp (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) (e : PointedEquivGerm 2)
    (he : e.forward.pullbackRingHom
      ((PointedMapGerm.recenterOfFunction A.H j hA).1.component 0) = coordinate 0)
    (β : PointedMapGerm 1 2)
    (hβ : (hyperplaneInclusionGerm 2).comp β =
      (PointedMapGerm.recenterOfFunction A.H j hA).comp
        (e.forward.comp (hyperplaneInclusionGerm 1))) :
    ∃ α : PointedEquivGerm 1,
      L.diskSourceGerm D j = (e.forward.comp (hyperplaneInclusionGerm 1)).comp α.forward ∧
      L.diskBranchGerm D j hA = β.comp α.forward :=
  (PointedMapGerm.recenterOfFunction A.H j hA).exists_sectionBranch_sourceEquiv e he β hβ
    (L.diskSourceGerm D j) (L.diskSourceGerm_differential_injective D j)
    (L.diskSourceGerm_first_pullback_zero D j hA)

/-- The earlier branch supplied by the same critical-point datum has
exactly the same image germ as diskBranch after an analytic source change. -/
theorem exists_diskBranch_transverse_equiv (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) :
    ∃ (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2) (α : PointedEquivGerm 1),
      e.forward.pullbackRingHom
        ((PointedMapGerm.recenterOfFunction A.H j hA).1.component 0) = coordinate 0 ∧
      (hyperplaneInclusionGerm 2).comp β =
        (PointedMapGerm.recenterOfFunction A.H j hA).comp
          (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
      β.HasInjectiveRepresentative ∧
      RingHom.ker β.pullbackRingHom = Ideal.span {localSectionEquation A.H j} ∧
      L.diskSourceGerm D j = (e.forward.comp (hyperplaneInclusionGerm 1)).comp α.forward ∧
      L.diskBranchGerm D j hA = β.comp α.forward := by
  obtain ⟨_, _, e, β, _, _, _, _, _, _, _, he, hβ, hiβ, hker, _⟩ :=
    L.singular j j.property
  obtain ⟨α, hγ, hB⟩ := L.diskBranchGerm_eq_transverse_comp D j hA e he β hβ
  exact ⟨e, β, α, he, hβ, hiβ, hker, hγ, hB⟩

/-- The exact localSectionEquation kernel belongs to the literal retained
diskBranch, rather than to an unrelated normalization. -/
theorem diskBranchGerm_kernel (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) :
    RingHom.ker (L.diskBranchGerm D j hA).pullbackRingHom =
      Ideal.span {localSectionEquation A.H j} := by
  obtain ⟨_, β, α, _, _, _, hker, _, hB⟩ := L.exists_diskBranch_transverse_equiv D j hA
  rw [hB, PointedMapGerm.pullbackRingHom_comp,
    RingHom.ker_comp_of_injective β.pullbackRingHom α.pullbackRingEquiv.injective, hker]

/-- Local injectivity of the literal germ follows from the identified
transverse branch and the constructed analytic source equivalence. -/
theorem diskBranchGerm_hasInjectiveRepresentative (L : ResolutionSectionLevel A)
    (D : (j : L.points) → L.PointCoordinateDisk j) (j : L.points)
    (hA : AnalyticAt ℂ A.H (j : Source 2)) :
    (L.diskBranchGerm D j hA).HasInjectiveRepresentative := by
  obtain ⟨_, β, α, _, _, hiβ, _, _, hB⟩ := L.exists_diskBranch_transverse_equiv D j hA
  rw [hB]
  exact β.comp_hasInjectiveRepresentative α.forward hiβ α.forward_hasInjectiveRepresentative

end ResolutionSectionLevel
end OnLeConjecture.Analytic
