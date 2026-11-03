/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorTotalHomology
public import OnLeConjecture.KnotFloer.GridExteriorOSwitchClass
public import OnLeConjecture.KnotFloer.GridStabilizationColourAlgebra

/-!
# Laurent chain maps between grids of different sizes

The maps of `GridExteriorTotalHomology` and `GridExteriorOSwitchClass` are stated for two grids of
the same size. The composite map of the scissor and cleanup construction of the written proof of
Statement E (`statement_E_complete_proof.tex`, Section 12) changes the grid size, and its pieces
have Maslov degrees `-1`, `0` and `+1`. This file provides the corresponding statements for a grid
`G` of size `n` and a grid `H` of size `k`.

* `laurentMaslovHomOfMapHet`: a Laurent chain map preserving the Maslov degree as a morphism of
  native complexes, with its filtration shifts (`laurentMaslovHomOfMapHet_shifts`).
* `laurentTotalHomologyMapHet`: the induced map of total homology, with composition, invariance
  under null-homotopic changes (`laurentTotalHomologyMapHet_eq_of_isNullHomotopic`) and the
  value on total classes.
* `laurentGradedToTotal_naturality_of_compat`: the comparison between graded and total homology
  commutes with a native morphism and a Laurent map that agree on every Maslov piece.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp

variable {n k : ℕ} (G : GridDiagram n) (H : GridDiagram k) {R : Type*} [CommRing R] [CharP R 2]

/-! ### Native morphisms from Laurent maps -/

/-- The restriction of a degree-preserving Laurent map to a Maslov piece. -/
def laurentPieceMapHet (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m) (m : ℤ) :
    laurentMaslovPiece G R m →ₗ[R] laurentMaslovPiece H R m :=
  LinearMap.codRestrict _ ((f.restrictScalars R).comp (laurentMaslovPiece G R m).subtype)
    (fun c => hdeg m c c.property)

omit [CharP R 2] in
/-- The restricted map commutes with the graded differentials. -/
theorem laurentGradedDifferential_pieceMapHet
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (m : ℤ)
    (c : laurentMaslovPiece G R (m + 1)) :
    laurentGradedDifferential H R m (laurentPieceMapHet G H f hdeg (m + 1) c) =
      laurentPieceMapHet G H f hdeg m (laurentGradedDifferential G R m c) := by
  apply Subtype.ext
  exact LinearMap.congr_fun hcomm (c : LaurentChain R n)

/-- A degree-preserving Laurent chain map as a morphism of native complexes. -/
def laurentMaslovHomOfMapHet (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentMaslovComplex G R ⟶ laurentMaslovComplex H R where
  f m := ModuleCat.ofHom (laurentPieceMapHet G H f hdeg m)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    subst i
    simp only [laurentMaslovComplex_d]
    ext c : 2
    exact laurentGradedDifferential_pieceMapHet G H f hdeg hcomm j c

theorem laurentMaslovChainEquiv_homOfMapHet
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (m : ℤ)
    (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv H R m ((laurentMaslovHomOfMapHet G H f hdeg hcomm).f m c) :
      LaurentChain R k) = f (laurentMaslovChainEquiv G R m c) := rfl

/-- Filtration shifts of a native morphism made from a Laurent map. -/
theorem laurentMaslovHomOfMapHet_shifts
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hcomm : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (s : ℝ)
    (hlev : ∀ (u v : ℝ) (c : LaurentChain R n), c ∈ laurentBifiltrationLevel G R u v →
      f c ∈ laurentBifiltrationLevel H R u (v + s)) :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovHomOfMapHet G H f hdeg hcomm) 0 s := by
  intro u v m c hc
  have h := hlev u v (laurentMaslovChainEquiv G R m c) hc
  rw [add_zero]
  exact h

/-! ### Maps of total homology -/

variable {G H}

/-- A Laurent chain map restricted to the total cycles. -/
def laurentTotalCyclesMapHet (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentTotalCycles G R →ₗ[LaurentPolynomial R] laurentTotalCycles H R :=
  f.restrict fun c hc => by
    rw [mem_laurentTotalCycles] at hc ⊢
    have h := LinearMap.congr_fun hf c
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hc, map_zero] at h
    exact h

omit [CharP R 2] in
theorem laurentTotalBoundaries_le_comapHet
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentTotalBoundaries G R ≤
      (laurentTotalBoundaries H R).comap (laurentTotalCyclesMapHet f hf) := by
  intro z hz
  rw [Submodule.mem_comap, mem_laurentTotalBoundaries]
  obtain ⟨w, hw⟩ := (mem_laurentTotalBoundaries G R).mp hz
  refine ⟨f w, ?_⟩
  change f z = _
  rw [hw]
  exact (LinearMap.congr_fun hf w).symm

/-- The map of total homology induced by a Laurent chain map. -/
def laurentTotalHomologyMapHet (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentTotalHomology G R →ₗ[LaurentPolynomial R] laurentTotalHomology H R :=
  Submodule.mapQ (laurentTotalBoundaries G R) (laurentTotalBoundaries H R)
    (laurentTotalCyclesMapHet f hf) (laurentTotalBoundaries_le_comapHet f hf)

omit [CharP R 2] in
/-- The induced map sends the class of a cycle `c` to the class of `f c`. -/
theorem laurentTotalHomologyMapHet_class
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (c : LaurentChain R n)
    (hc : laurentDifferential G R c = 0) (hfc : laurentDifferential H R (f c) = 0) :
    laurentTotalHomologyMapHet f hf (laurentTotalClass G R c hc) =
      laurentTotalClass H R (f c) hfc := rfl

omit [CharP R 2] in
theorem laurentTotalHomologyMapHet_mk
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (z : laurentTotalCycles G R) :
    laurentTotalHomologyMapHet f hf (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (laurentTotalCyclesMapHet f hf z) := rfl

omit [CharP R 2] in
/-- The induced maps are compatible with composition. -/
theorem laurentTotalHomologyMapHet_comp {l : ℕ} {K : GridDiagram l}
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (g : LaurentChain R k →ₗ[LaurentPolynomial R] LaurentChain R l)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hg : laurentDifferential K R ∘ₗ g = g ∘ₗ laurentDifferential H R)
    (hgf : laurentDifferential K R ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMapHet (g ∘ₗ f) hgf =
      laurentTotalHomologyMapHet g hg ∘ₗ laurentTotalHomologyMapHet f hf := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, laurentTotalHomologyMapHet_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

omit [CharP R 2] in
/-- Laurent chain maps differing by a null-homotopic map induce the same map of total
homology. -/
theorem laurentTotalHomologyMapHet_eq_of_isNullHomotopic
    (f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hg : laurentDifferential H R ∘ₗ g = g ∘ₗ laurentDifferential G R)
    (h : IsNullHomotopic (laurentDifferential G R) (laurentDifferential H R) (f - g)) :
    laurentTotalHomologyMapHet f hf = laurentTotalHomologyMapHet g hg := by
  obtain ⟨K, hK⟩ := h
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  change Submodule.Quotient.mk (laurentTotalCyclesMapHet f hf z) =
    Submodule.Quotient.mk (laurentTotalCyclesMapHet g hg z)
  rw [Submodule.Quotient.eq, mem_laurentTotalBoundaries]
  refine ⟨K z, ?_⟩
  have hz : laurentDifferential G R z = 0 := (mem_laurentTotalCycles G R).mp z.property
  have h1 := LinearMap.congr_fun hK z
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero,
    add_zero] at h1
  exact h1

omit [CharP R 2] in
theorem laurentTotalHomologyMapHet_add
    (f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hg : laurentDifferential H R ∘ₗ g = g ∘ₗ laurentDifferential G R)
    (hfg : laurentDifferential H R ∘ₗ (f + g) = (f + g) ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMapHet (f + g) hfg =
      laurentTotalHomologyMapHet f hf + laurentTotalHomologyMapHet g hg := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.mkQ_apply,
    laurentTotalHomologyMapHet_mk]
  rw [← Submodule.Quotient.mk_add]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-! ### Comparison with graded homology -/

/-- The comparison between graded and total homology commutes with a native morphism and a
Laurent chain map that agree on every Maslov piece. -/
theorem laurentGradedToTotal_naturality_of_compat
    (φ : laurentMaslovComplex G R ⟶ laurentMaslovComplex H R)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R k)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hcompat : ∀ (m : ℤ) (x : (laurentMaslovComplex G R).X m),
      (laurentMaslovChainEquiv H R m (φ.f m x) : LaurentChain R k) =
        f (laurentMaslovChainEquiv G R m x)) (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) :
    laurentGradedToTotal H R m (homologyMap φ m ξ) =
      laurentTotalHomologyMapHet f hf (laurentGradedToTotal G R m ξ) := by
  obtain ⟨z, rfl⟩ := laurentMaslovComplex_homologyπ_surjective G R m ξ
  have hnat := congrArg (fun g : (laurentMaslovComplex G R).cycles m ⟶
      (laurentMaslovComplex H R).homology m => g z) (homologyπ_naturality φ m)
  change homologyMap φ m ((laurentMaslovComplex G R).homologyπ m z) =
    (laurentMaslovComplex H R).homologyπ m (cyclesMap φ m z) at hnat
  have hi := congrArg (fun g : (laurentMaslovComplex G R).cycles m ⟶
      (laurentMaslovComplex H R).X m => g z) (cyclesMap_i φ m)
  change (laurentMaslovComplex H R).iCycles m (cyclesMap φ m z) =
    φ.f m ((laurentMaslovComplex G R).iCycles m z) at hi
  rw [hnat, laurentGradedToTotal_homologyπ, laurentGradedToTotal_homologyπ,
    laurentTotalHomologyMapHet_class]
  · apply laurentTotalClass_congr
    rw [hi]
    exact hcompat m _
  · have h := LinearMap.congr_fun hf
      (laurentMaslovChainEquiv G R m ((laurentMaslovComplex G R).iCycles m z) : LaurentChain R n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      laurentDifferential_laurentMaslovChainEquiv_iCycles, map_zero] at h
    exact h

end OnLeConjecture.KnotFloer.GridFull
