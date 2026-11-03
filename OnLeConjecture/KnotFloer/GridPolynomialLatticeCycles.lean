/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridPolynomialLatticeHomology

/-!
# Polynomial homology image and cycle representatives

A Laurent homology class belongs to the polynomial image exactly when it has
a cycle representative supported in nonnegative Laurent exponents. This is a
representative criterion and imposes no uniqueness or dimension hypothesis.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex

variable {n : ℕ} (R : Type*) [CommRing R] [CharP R 2]

/-- The polynomial homology image is exactly the set of classes with a polynomial cycle
representative in the Laurent complex. -/
theorem mem_polynomialHomologyImage_iff_exists_cycle (G : GridDiagram n) (a : Fin n)
    (m : ℤ) (ξ : (laurentMaslovComplex G R).homology m) :
    ξ ∈ polynomialHomologyImage R G a m ↔
      ∃ z : (laurentMaslovComplex G R).cycles m,
        (∀ x k, k ∈ ((laurentMaslovChainEquiv G R m
          ((laurentMaslovComplex G R).iCycles m z) : LaurentChain R n) x).coeff.support →
            0 ≤ k) ∧ (laurentMaslovComplex G R).homologyπ m z = ξ := by
  let P := oneVariableMaslovComplex R G a
  let L := laurentMaslovComplex G R
  let φ := polynomialLatticeInclusion R G a
  constructor
  · rintro ⟨η, hη⟩
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (P.homologyπ m)).mp inferInstance η
    refine ⟨cyclesMap φ m z, ?_, ?_⟩
    · apply (mem_range_polynomialLatticeInclusion_iff R G a m _).mp
      refine ⟨P.iCycles m z, ?_⟩
      exact (congrArg (fun f : P.cycles m ⟶ L.X m => f z) (cyclesMap_i φ m)).symm
    · have h := congrArg (fun f : P.cycles m ⟶ L.homology m => f z)
        (homologyπ_naturality φ m)
      change homologyMap φ m (P.homologyπ m z) = L.homologyπ m (cyclesMap φ m z) at h
      exact h.symm.trans (by rw [hz]; exact hη)
  · rintro ⟨z, hz, hξ⟩
    obtain ⟨p, hp⟩ := (mem_range_polynomialLatticeInclusion_iff R G a m _).mpr hz
    let j := (ComplexShape.down ℤ).next m
    have hpcycle : P.d m j p = 0 := by
      apply polynomialLatticeInclusion_injective R G a j
      rw [map_zero]
      have h := congrArg (fun f : P.X m ⟶ L.X j => f p) (φ.comm m j)
      change L.d m j (φ.f m p) = φ.f j (P.d m j p) at h
      rw [hp] at h
      exact h.symm.trans
        (congrArg (fun f : L.cycles m ⟶ L.X j => f z) (L.iCycles_d m j))
    let w := P.cyclesMk p j rfl hpcycle
    have hw : P.iCycles m w = p := P.i_cyclesMk p j rfl hpcycle
    have hcycles : cyclesMap φ m w = z := by
      apply (ModuleCat.mono_iff_injective (L.iCycles m)).mp inferInstance
      have h := congrArg (fun f : P.cycles m ⟶ L.X m => f w) (cyclesMap_i φ m)
      change L.iCycles m (cyclesMap φ m w) = φ.f m (P.iCycles m w) at h
      rw [hw] at h
      exact h.trans hp
    refine ⟨P.homologyπ m w, ?_⟩
    have h := congrArg (fun f : P.cycles m ⟶ L.homology m => f w)
      (homologyπ_naturality φ m)
    change homologyMap φ m (P.homologyπ m w) = L.homologyπ m (cyclesMap φ m w) at h
    exact h.trans (by rw [hcycles]; exact hξ)

/-- The polynomial homology image does not depend on the selected O variable. -/
theorem polynomialHomologyImage_eq (G : GridDiagram n) (a b : Fin n) (m : ℤ) :
    polynomialHomologyImage R G a m = polynomialHomologyImage R G b m := by
  ext ξ
  rw [mem_polynomialHomologyImage_iff_exists_cycle, mem_polynomialHomologyImage_iff_exists_cycle]

end OnLeConjecture.KnotFloer.GridFull
