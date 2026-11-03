/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullCommutationCyclic
public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral
public import OnLeConjecture.KnotFloer.BifilteredSpectral

/-!
# Cyclic translations preserve the full grid bifiltration

The explicit cyclic row and column isomorphisms preserve the Laurent exponent and the
Alexander grading. They therefore preserve and reflect both filtration coordinates on
each Maslov homogeneous piece. Their induced homology maps preserve each class's weighted
spectral threshold. This proves invariance under cyclic translations only.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R]

/-- The cyclic row map preserves and reflects both coefficient filtration bounds. -/
theorem laurentCyclicRowsEquiv_mem_bifiltrationLevel_iff (a b : ℝ) (c : LaurentChain R n) :
    laurentCyclicRowsEquiv R c ∈ laurentBifiltrationLevel (G.relabelRows (finRotate n)) R a b ↔
      c ∈ laurentBifiltrationLevel G R a b := by
  simp only [mem_laurentBifiltrationLevel_iff]
  constructor
  · intro h x k hk
    have := h (x.relabelRows (finRotate n)) k
    simpa only [GridDiagram.alexander_relabelRows_finRotate] using this (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.relabelRows (finRotate n) = y :=
      ⟨y.relabelRows (finRotate n).symm, by simp⟩
    simpa only [GridDiagram.alexander_relabelRows_finRotate] using h x k (by simpa using hk)

/-- The cyclic column map preserves and reflects both coefficient filtration bounds. -/
theorem laurentCyclicColumnsEquiv_mem_bifiltrationLevel_iff (a b : ℝ) (c : LaurentChain R n) :
    laurentCyclicColumnsEquiv R c ∈
        laurentBifiltrationLevel (G.relabelColumns (finRotate n)) R a b ↔
      c ∈ laurentBifiltrationLevel G R a b := by
  simp only [mem_laurentBifiltrationLevel_iff]
  constructor
  · intro h x k hk
    have := h (x.relabelColumns (finRotate n)) k
    simpa only [GridDiagram.alexander_relabelColumns_finRotate] using this (by simpa using hk)
  · intro h y k hk
    obtain ⟨x, rfl⟩ : ∃ x, x.relabelColumns (finRotate n) = y :=
      ⟨y.relabelColumns (finRotate n).symm, by simp⟩
    simpa only [GridDiagram.alexander_relabelColumns_finRotate] using h x k (by simpa using hk)

variable [CharP R 2]

/-- The native cyclic row component is the explicit relabeling on homogeneous chains. -/
theorem laurentMaslovChainEquiv_cyclicRows (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv (G.relabelRows (finRotate n)) R m
      ((laurentMaslovCyclicRowsIso G R).hom.f m c) : LaurentChain R n) =
        laurentCyclicRowsEquiv R (laurentMaslovChainEquiv G R m c) := by
  rfl

/-- The native cyclic column component is the explicit relabeling on homogeneous chains. -/
theorem laurentMaslovChainEquiv_cyclicColumns (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv (G.relabelColumns (finRotate n)) R m
      ((laurentMaslovCyclicColumnsIso G R).hom.f m c) : LaurentChain R n) =
        laurentCyclicColumnsEquiv R (laurentMaslovChainEquiv G R m c) := by
  rfl

/-- Cyclic row translation preserves and reflects every bifiltration level. -/
theorem laurentMaslovCyclicRows_mem_level_iff (a b : ℝ) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovCyclicRowsIso G R).hom.f m c ∈
        (laurentMaslovBifiltration (G.relabelRows (finRotate n)) R).level a b m ↔
      c ∈ (laurentMaslovBifiltration G R).level a b m := by
  change (laurentMaslovChainEquiv (G.relabelRows (finRotate n)) R m
      ((laurentMaslovCyclicRowsIso G R).hom.f m c) : LaurentChain R n) ∈
      laurentBifiltrationLevel (G.relabelRows (finRotate n)) R a b ↔ _
  rw [laurentMaslovChainEquiv_cyclicRows, laurentCyclicRowsEquiv_mem_bifiltrationLevel_iff]
  rfl

/-- Cyclic column translation preserves and reflects every bifiltration level. -/
theorem laurentMaslovCyclicColumns_mem_level_iff (a b : ℝ) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovCyclicColumnsIso G R).hom.f m c ∈
        (laurentMaslovBifiltration (G.relabelColumns (finRotate n)) R).level a b m ↔
      c ∈ (laurentMaslovBifiltration G R).level a b m := by
  change (laurentMaslovChainEquiv (G.relabelColumns (finRotate n)) R m
      ((laurentMaslovCyclicColumnsIso G R).hom.f m c) : LaurentChain R n) ∈
      laurentBifiltrationLevel (G.relabelColumns (finRotate n)) R a b ↔ _
  rw [laurentMaslovChainEquiv_cyclicColumns, laurentCyclicColumnsEquiv_mem_bifiltrationLevel_iff]
  rfl

/-- The forward cyclic row chain map is bifiltered. -/
theorem laurentMaslovCyclicRows_preserves :
    (laurentMaslovBifiltration G R).Preserves
      (laurentMaslovBifiltration (G.relabelRows (finRotate n)) R)
      (laurentMaslovCyclicRowsIso G R).hom := by
  intro a b m c hc
  exact (laurentMaslovCyclicRows_mem_level_iff G R a b m c).mpr hc

/-- The inverse cyclic row chain map is bifiltered. -/
theorem laurentMaslovCyclicRows_inv_preserves :
    (laurentMaslovBifiltration (G.relabelRows (finRotate n)) R).Preserves
      (laurentMaslovBifiltration G R) (laurentMaslovCyclicRowsIso G R).inv := by
  intro a b m c hc
  apply (laurentMaslovCyclicRows_mem_level_iff G R a b m _).mp
  have h := congrArg (fun f => f.f m c) (laurentMaslovCyclicRowsIso G R).inv_hom_id
  change (laurentMaslovCyclicRowsIso G R).hom.f m
    ((laurentMaslovCyclicRowsIso G R).inv.f m c) = c at h
  rwa [h]

/-- The forward cyclic column chain map is bifiltered. -/
theorem laurentMaslovCyclicColumns_preserves :
    (laurentMaslovBifiltration G R).Preserves
      (laurentMaslovBifiltration (G.relabelColumns (finRotate n)) R)
      (laurentMaslovCyclicColumnsIso G R).hom := by
  intro a b m c hc
  exact (laurentMaslovCyclicColumns_mem_level_iff G R a b m c).mpr hc

/-- The inverse cyclic column chain map is bifiltered. -/
theorem laurentMaslovCyclicColumns_inv_preserves :
    (laurentMaslovBifiltration (G.relabelColumns (finRotate n)) R).Preserves
      (laurentMaslovBifiltration G R) (laurentMaslovCyclicColumnsIso G R).inv := by
  intro a b m c hc
  apply (laurentMaslovCyclicColumns_mem_level_iff G R a b m _).mp
  have h := congrArg (fun f => f.f m c) (laurentMaslovCyclicColumnsIso G R).inv_hom_id
  change (laurentMaslovCyclicColumnsIso G R).hom.f m
    ((laurentMaslovCyclicColumnsIso G R).inv.f m c) = c at h
  rwa [h]

/-- Cyclic row translation preserves the weighted threshold of every native homology class. -/
theorem spectralThreshold_laurentMaslovCyclicRows (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    ((laurentMaslovBifiltration (G.relabelRows (finRotate n)) R).weighted t).spectralThreshold m
      (homologyMap (laurentMaslovCyclicRowsIso G R).hom m ξ) =
        ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ := by
  exact RealFiltration.spectralThreshold_eq_of_homotopyEquiv
    (HomotopyEquiv.ofIso (laurentMaslovCyclicRowsIso G R))
    ((laurentMaslovCyclicRows_preserves G R).weighted t)
    ((laurentMaslovCyclicRows_inv_preserves G R).weighted t) m ξ

/-- Cyclic column translation preserves the weighted threshold of every native homology class. -/
theorem spectralThreshold_laurentMaslovCyclicColumns (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    ((laurentMaslovBifiltration (G.relabelColumns (finRotate n)) R).weighted t).spectralThreshold m
      (homologyMap (laurentMaslovCyclicColumnsIso G R).hom m ξ) =
        ((laurentMaslovBifiltration G R).weighted t).spectralThreshold m ξ := by
  exact RealFiltration.spectralThreshold_eq_of_homotopyEquiv
    (HomotopyEquiv.ofIso (laurentMaslovCyclicColumnsIso G R))
    ((laurentMaslovCyclicColumns_preserves G R).weighted t)
    ((laurentMaslovCyclicColumns_inv_preserves G R).weighted t) m ξ

/-- The algebraic class-Upsilon function is invariant under cyclic row translation. -/
theorem classUpsilon_laurentMaslovCyclicRows (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    (laurentMaslovBifiltration (G.relabelRows (finRotate n)) R).classUpsilon m
      (homologyMap (laurentMaslovCyclicRowsIso G R).hom m ξ) t =
        (laurentMaslovBifiltration G R).classUpsilon m ξ t := by
  unfold Bifiltration.classUpsilon
  rw [spectralThreshold_laurentMaslovCyclicRows]

/-- The algebraic class-Upsilon function is invariant under cyclic column translation. -/
theorem classUpsilon_laurentMaslovCyclicColumns (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) (t : ℝ) :
    (laurentMaslovBifiltration (G.relabelColumns (finRotate n)) R).classUpsilon m
      (homologyMap (laurentMaslovCyclicColumnsIso G R).hom m ξ) t =
        (laurentMaslovBifiltration G R).classUpsilon m ξ t := by
  unfold Bifiltration.classUpsilon
  rw [spectralThreshold_laurentMaslovCyclicColumns]

end OnLeConjecture.KnotFloer.GridFull
