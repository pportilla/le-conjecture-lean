/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridExteriorOSwitchClass
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Total homology of the full Laurent grid complex

Let `G` be a grid diagram and let `R` be a commutative ring. The full Laurent grid module
`LaurentChain R n` is the internal direct sum of its Maslov pieces, and the full Laurent
differential lowers the Maslov degree by one. This file compares the homology of the
integer-graded complex `laurentMaslovComplex G R` with the homology of the ungraded
differential module `(LaurentChain R n, laurentDifferential G R)`.

* `laurentMaslovComponent G R m` is the `R`-linear projection onto the Maslov piece of
  degree `m`. It sends `laurentDifferential G R c` to `laurentDifferential G R` of the
  component of degree `m + 1` of `c` (`laurentMaslovComponent_laurentDifferential`).
  Consequently, a homogeneous chain of degree `m` that is a boundary is the boundary of a
  homogeneous chain of degree `m + 1` (`exists_mem_maslovPiece_of_eq_laurentDifferential`).
* `laurentTotalHomology G R` is the quotient of the kernel of `laurentDifferential G R` by
  the cycles lying in its image, as a module over `LaurentPolynomial R`. A Laurent chain map
  `f` from `G` to `H` induces `laurentTotalHomologyMap f hf`. The induced maps are
  functorial and additive, and two chain maps that are homotopic in characteristic two
  induce the same map (`laurentTotalHomologyMap_eq_of_homotopy`).
* In characteristic two, `laurentGradedToTotal G R m` sends the homology class of a cycle of
  degree `m` of `laurentMaslovComplex G R` to the total class of its underlying chain. This
  `R`-linear map is injective (`laurentGradedToTotal_injective`) and commutes with the maps
  induced by Maslov degree preserving Laurent chain maps (`laurentGradedToTotal_naturality`).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex Finsupp Limits

variable {n : ℕ} (G H : GridDiagram n) (R : Type*) [CommRing R]

/-! ### Maslov components -/

/-- The part of a Laurent polynomial attached to the state `x` whose monomials have Maslov
degree `m`. -/
def laurentMaslovFilter (x : GridState n) (m : ℤ) :
    LaurentPolynomial R →ₗ[R] LaurentPolynomial R where
  toFun p := AddMonoidAlgebra.ofCoeff (p.coeff.filter fun k => laurentMaslovDegree G k x = m)
  map_add' p q := by
    apply AddMonoidAlgebra.ext
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.filter_add]
  map_smul' a p := by
    apply AddMonoidAlgebra.ext
    simp only [AddMonoidAlgebra.coeff_smul, Finsupp.filter_smul, RingHom.id_apply]

/-- The coefficients of the filtered Laurent polynomial. -/
theorem laurentMaslovFilter_coeff (x : GridState n) (m : ℤ) (p : LaurentPolynomial R) :
    (laurentMaslovFilter G R x m p).coeff =
      p.coeff.filter fun k => laurentMaslovDegree G k x = m := rfl

/-- The Maslov component of degree `m` of a Laurent chain. In each state it keeps exactly the
monomials of Maslov degree `m`. -/
def laurentMaslovComponent (m : ℤ) : LaurentChain R n →ₗ[R] LaurentChain R n where
  toFun c := Finsupp.equivFunOnFinite.symm fun x => laurentMaslovFilter G R x m (c x)
  map_add' c d := by
    ext x : 1
    simp
  map_smul' a c := by
    ext x : 1
    simp

/-- The value of a Maslov component at a state. -/
@[simp]
theorem laurentMaslovComponent_apply (m : ℤ) (c : LaurentChain R n) (x : GridState n) :
    laurentMaslovComponent G R m c x = laurentMaslovFilter G R x m (c x) := rfl

/-- The Maslov component of degree `m` is homogeneous of degree `m`. -/
theorem laurentMaslovComponent_mem (m : ℤ) (c : LaurentChain R n) :
    laurentMaslovComponent G R m c ∈ laurentMaslovPiece G R m := by
  intro x k hk
  rw [laurentMaslovComponent_apply, laurentMaslovFilter_coeff, Finsupp.support_filter] at hk
  exact (Finset.mem_filter.mp hk).2

/-- The Maslov component of degree `m` fixes every homogeneous chain of degree `m`. -/
theorem laurentMaslovComponent_of_mem {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m) : laurentMaslovComponent G R m c = c := by
  ext x : 1
  rw [laurentMaslovComponent_apply]
  apply AddMonoidAlgebra.ext
  rw [laurentMaslovFilter_coeff, Finsupp.filter_eq_self_iff]
  intro k hk
  exact hc x k (Finsupp.mem_support_iff.mpr hk)

/-- The Maslov component of degree `m` vanishes on homogeneous chains of degree `m' ≠ m`. -/
theorem laurentMaslovComponent_of_mem_ne {m m' : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m') (h : m' ≠ m) : laurentMaslovComponent G R m c = 0 := by
  ext x : 1
  rw [laurentMaslovComponent_apply, Finsupp.zero_apply]
  apply AddMonoidAlgebra.ext
  rw [laurentMaslovFilter_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.filter_eq_zero_iff]
  intro k hk
  by_contra hne
  exact h ((hc x k (Finsupp.mem_support_iff.mpr hne)).symm.trans hk)

/-- The Maslov component of degree `m` of a boundary is the boundary of the Maslov component
of degree `m + 1`. -/
theorem laurentMaslovComponent_laurentDifferential (m : ℤ) (c : LaurentChain R n) :
    laurentMaslovComponent G R m (laurentDifferential G R c) =
      laurentDifferential G R (laurentMaslovComponent G R (m + 1) c) := by
  have htop : c ∈ ⨆ j : ℤ, laurentMaslovPiece G R j := by
    rw [iSup_laurentMaslovPiece_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (laurentMaslovPiece G R) (motive := fun c =>
    laurentMaslovComponent G R m (laurentDifferential G R c) =
      laurentDifferential G R (laurentMaslovComponent G R (m + 1) c)) htop ?_ ?_ ?_
  · intro j c hc
    have hdc := laurentDifferential_mem_maslovPiece G hc
    by_cases hj : j = m + 1
    · subst hj
      rw [laurentMaslovComponent_of_mem G R hc,
        laurentMaslovComponent_of_mem G R (by simpa using hdc)]
    · rw [laurentMaslovComponent_of_mem_ne G R hc hj, map_zero,
        laurentMaslovComponent_of_mem_ne G R hdc (by omega)]
  · simp only [map_zero]
  · intro c c' hc hc'
    rw [map_add, map_add, hc, hc', map_add, map_add]

/-- A homogeneous boundary of degree `m` is the boundary of a homogeneous chain of
degree `m + 1`. -/
theorem exists_mem_maslovPiece_of_eq_laurentDifferential {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m) (w : LaurentChain R n)
    (hw : c = laurentDifferential G R w) :
    ∃ w' ∈ laurentMaslovPiece G R (m + 1), c = laurentDifferential G R w' := by
  refine ⟨laurentMaslovComponent G R (m + 1) w, laurentMaslovComponent_mem G R (m + 1) w, ?_⟩
  rw [← laurentMaslovComponent_laurentDifferential, ← hw, laurentMaslovComponent_of_mem G R hc]

/-! ### Total homology -/

/-- The total cycles: the kernel of the full Laurent differential. -/
def laurentTotalCycles : Submodule (LaurentPolynomial R) (LaurentChain R n) :=
  LinearMap.ker (laurentDifferential G R)

/-- A chain is a total cycle exactly when its differential vanishes. -/
theorem mem_laurentTotalCycles {c : LaurentChain R n} :
    c ∈ laurentTotalCycles G R ↔ laurentDifferential G R c = 0 := LinearMap.mem_ker

/-- The additive group structure of the total cycles. Declaring it directly lets instance
search find the quotient module structures on the total homology. -/
instance instAddCommGroupLaurentTotalCycles : AddCommGroup (laurentTotalCycles G R) :=
  Submodule.addCommGroup _

/-- The total boundaries, as a submodule of the total cycles: the cycles lying in the image
of the full Laurent differential. -/
def laurentTotalBoundaries : Submodule (LaurentPolynomial R) (laurentTotalCycles G R) :=
  (LinearMap.range (laurentDifferential G R)).comap (laurentTotalCycles G R).subtype

/-- A total cycle is a total boundary exactly when it is the differential of a chain. -/
theorem mem_laurentTotalBoundaries {z : laurentTotalCycles G R} :
    z ∈ laurentTotalBoundaries G R ↔
      ∃ w : LaurentChain R n, (z : LaurentChain R n) = laurentDifferential G R w := by
  simp only [laurentTotalBoundaries, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_range, eq_comm]

/-- In characteristic two, every boundary of the full Laurent differential is a cycle. -/
theorem laurentDifferential_mem_laurentTotalCycles [CharP R 2] (w : LaurentChain R n) :
    laurentDifferential G R w ∈ laurentTotalCycles G R :=
  (mem_laurentTotalCycles G R).mpr (laurentDifferential_sq_eq_zero G R w)

/-- The total homology of the full Laurent grid complex, as a module over the Laurent
polynomial ring. -/
abbrev laurentTotalHomology : Type _ := laurentTotalCycles G R ⧸ laurentTotalBoundaries G R

/-- The total homology class of a cycle of the full Laurent differential. -/
def laurentTotalClass (c : LaurentChain R n) (hc : laurentDifferential G R c = 0) :
    laurentTotalHomology G R :=
  Submodule.Quotient.mk ⟨c, (mem_laurentTotalCycles G R).mpr hc⟩

/-- The total class depends only on the cycle, through equal chains. -/
theorem laurentTotalClass_congr {c c' : LaurentChain R n} (h : c = c')
    (hc : laurentDifferential G R c = 0) (hc' : laurentDifferential G R c' = 0) :
    laurentTotalClass G R c hc = laurentTotalClass G R c' hc' := by
  subst h
  rfl

/-- The total class of a sum of cycles is the sum of their total classes. -/
theorem laurentTotalClass_add {c c' : LaurentChain R n} (hc : laurentDifferential G R c = 0)
    (hc' : laurentDifferential G R c' = 0) (hcc' : laurentDifferential G R (c + c') = 0) :
    laurentTotalClass G R (c + c') hcc' =
      laurentTotalClass G R c hc + laurentTotalClass G R c' hc' := rfl

/-- The total class of a scalar multiple of a cycle is the multiple of its total class. -/
theorem laurentTotalClass_smul {S : Type*} [Semiring S] [SMul S (LaurentPolynomial R)]
    [Module S (LaurentChain R n)] [IsScalarTower S (LaurentPolynomial R) (LaurentChain R n)]
    (a : S) {c : LaurentChain R n} (hc : laurentDifferential G R c = 0)
    (hac : laurentDifferential G R (a • c) = 0) :
    laurentTotalClass G R (a • c) hac = a • laurentTotalClass G R c hc := rfl

/-- Every total homology class is the class of a cycle. -/
theorem exists_laurentTotalClass_eq (ξ : laurentTotalHomology G R) :
    ∃ (c : LaurentChain R n) (hc : laurentDifferential G R c = 0),
      laurentTotalClass G R c hc = ξ := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact ⟨c, (mem_laurentTotalCycles G R).mp hc, rfl⟩

/-- The total class of a cycle vanishes exactly when the cycle is a boundary. -/
theorem laurentTotalClass_eq_zero_iff {c : LaurentChain R n}
    (hc : laurentDifferential G R c = 0) :
    laurentTotalClass G R c hc = 0 ↔ ∃ w : LaurentChain R n, c = laurentDifferential G R w := by
  rw [laurentTotalClass, Submodule.Quotient.mk_eq_zero, mem_laurentTotalBoundaries]

/-! ### Maps induced by Laurent chain maps -/

section Induced

variable {G H R}

/-- A Laurent chain map restricted to the total cycles. -/
def laurentTotalCyclesMap (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentTotalCycles G R →ₗ[LaurentPolynomial R] laurentTotalCycles H R :=
  f.restrict fun c hc => by
    rw [mem_laurentTotalCycles] at hc ⊢
    have h := LinearMap.congr_fun hf c
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hc, map_zero] at h
    exact h

/-- The restricted map acts on the underlying chain of a total cycle as `f`. -/
theorem laurentTotalCyclesMap_apply
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (z : laurentTotalCycles G R) :
    (laurentTotalCyclesMap f hf z : LaurentChain R n) = f z := rfl

/-- A Laurent chain map sends total boundaries to total boundaries. -/
theorem laurentTotalBoundaries_le_comap
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentTotalBoundaries G R ≤
      (laurentTotalBoundaries H R).comap (laurentTotalCyclesMap f hf) := by
  intro z hz
  rw [Submodule.mem_comap, mem_laurentTotalBoundaries, laurentTotalCyclesMap_apply]
  obtain ⟨w, hw⟩ := (mem_laurentTotalBoundaries G R).mp hz
  refine ⟨f w, ?_⟩
  rw [hw]
  exact (LinearMap.congr_fun hf w).symm

/-- The map of total homology induced by a Laurent chain map. -/
def laurentTotalHomologyMap (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) :
    laurentTotalHomology G R →ₗ[LaurentPolynomial R] laurentTotalHomology H R :=
  Submodule.mapQ (laurentTotalBoundaries G R) (laurentTotalBoundaries H R)
    (laurentTotalCyclesMap f hf) (laurentTotalBoundaries_le_comap f hf)

/-- The induced map sends the class of a cycle `c` to the class of `f c`. -/
theorem laurentTotalHomologyMap_class
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (c : LaurentChain R n)
    (hc : laurentDifferential G R c = 0) (hfc : laurentDifferential H R (f c) = 0) :
    laurentTotalHomologyMap f hf (laurentTotalClass G R c hc) =
      laurentTotalClass H R (f c) hfc := rfl

/-- The induced map on the quotient class of a total cycle. -/
theorem laurentTotalHomologyMap_mk
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (z : laurentTotalCycles G R) :
    laurentTotalHomologyMap f hf (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (laurentTotalCyclesMap f hf z) := rfl

/-- The induced maps are compatible with composition. -/
theorem laurentTotalHomologyMap_comp {K : GridDiagram n}
    (f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hg : laurentDifferential K R ∘ₗ g = g ∘ₗ laurentDifferential H R)
    (hgf : laurentDifferential K R ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMap (g ∘ₗ f) hgf =
      laurentTotalHomologyMap g hg ∘ₗ laurentTotalHomologyMap f hf := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, laurentTotalHomologyMap_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- The identity chain map induces the identity. -/
theorem laurentTotalHomologyMap_id
    (h : laurentDifferential G R ∘ₗ LinearMap.id = LinearMap.id ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMap LinearMap.id h = LinearMap.id :=
  Submodule.linearMap_qext _ rfl

/-- The induced map of a sum is the sum of the induced maps. -/
theorem laurentTotalHomologyMap_add
    (f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hg : laurentDifferential H R ∘ₗ g = g ∘ₗ laurentDifferential G R)
    (hfg : laurentDifferential H R ∘ₗ (f + g) = (f + g) ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMap (f + g) hfg =
      laurentTotalHomologyMap f hf + laurentTotalHomologyMap g hg := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.mkQ_apply,
    laurentTotalHomologyMap_mk]
  rw [← Submodule.Quotient.mk_add]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- The induced map of a Laurent multiple is the Laurent multiple of the induced map. -/
theorem laurentTotalHomologyMap_smul (p : LaurentPolynomial R)
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hpf : laurentDifferential H R ∘ₗ (p • f) = (p • f) ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMap (p • f) hpf = p • laurentTotalHomologyMap f hf := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.mkQ_apply,
    laurentTotalHomologyMap_mk]
  rw [← Submodule.Quotient.mk_smul]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- The zero chain map induces the zero map. -/
theorem laurentTotalHomologyMap_zero
    (h0 : laurentDifferential H R ∘ₗ (0 : LaurentChain R n →ₗ[LaurentPolynomial R]
      LaurentChain R n) = 0 ∘ₗ laurentDifferential G R) :
    laurentTotalHomologyMap 0 h0 = 0 :=
  Submodule.linearMap_qext _ rfl

/-- Two Laurent chain maps that are homotopic in characteristic two induce the same map of
total homology. -/
theorem laurentTotalHomologyMap_eq_of_homotopy [CharP R 2]
    (f g : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R)
    (hg : laurentDifferential H R ∘ₗ g = g ∘ₗ laurentDifferential G R)
    (h : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hh : f + g + (laurentDifferential H R ∘ₗ h + h ∘ₗ laurentDifferential G R) = 0) :
    laurentTotalHomologyMap f hf = laurentTotalHomologyMap g hg := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
  change Submodule.Quotient.mk (laurentTotalCyclesMap f hf z) =
    Submodule.Quotient.mk (laurentTotalCyclesMap g hg z)
  rw [Submodule.Quotient.eq, mem_laurentTotalBoundaries]
  refine ⟨h z, ?_⟩
  have hz : laurentDifferential G R z = 0 := (mem_laurentTotalCycles G R).mp z.property
  have h2 : ∀ v : LaurentChain R n, v + v = 0 := fun v => by
    rw [← two_smul R v, CharTwo.two_eq_zero, zero_smul]
  have hsum := LinearMap.congr_fun hh z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero,
    LinearMap.zero_apply] at hsum
  change f z - g z = laurentDifferential H R (h z)
  have key : f z - g z - laurentDifferential H R (h z) =
      (f z + g z + laurentDifferential H R (h z)) - (g z + g z) -
        (laurentDifferential H R (h z) + laurentDifferential H R (h z)) := by
    abel
  rw [hsum, h2, h2, sub_zero, sub_zero] at key
  exact sub_eq_zero.mp key

end Induced

/-! ### Comparison with the homology of the graded complex -/

section Graded

variable [CharP R 2]

/-- The underlying chain of a cycle of the graded complex is a total cycle. -/
theorem laurentDifferential_laurentMaslovChainEquiv_iCycles (m : ℤ)
    (z : (laurentMaslovComplex G R).cycles m) :
    laurentDifferential G R
      (laurentMaslovChainEquiv G R m ((laurentMaslovComplex G R).iCycles m z)) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, k + 1 = m := ⟨m - 1, by omega⟩
  have h0 := congrArg (fun f : (laurentMaslovComplex G R).cycles (k + 1) ⟶
      (laurentMaslovComplex G R).X k => f z) ((laurentMaslovComplex G R).iCycles_d (k + 1) k)
  change (laurentMaslovComplex G R).d (k + 1) k
    ((laurentMaslovComplex G R).iCycles (k + 1) z) = 0 at h0
  have hd := laurentMaslovChainEquiv_d G R k ((laurentMaslovComplex G R).iCycles (k + 1) z)
  rw [h0, map_zero, Submodule.coe_zero] at hd
  exact hd.symm

/-- The total class of the underlying chain of a cycle of the graded complex. -/
def laurentGradedCyclesToTotal (m : ℤ) :
    (laurentMaslovComplex G R).cycles m →ₗ[R] laurentTotalHomology G R where
  toFun z := laurentTotalClass G R _ (laurentDifferential_laurentMaslovChainEquiv_iCycles G R m z)
  map_add' z z' := by
    have hz := laurentDifferential_laurentMaslovChainEquiv_iCycles G R m z
    have hz' := laurentDifferential_laurentMaslovChainEquiv_iCycles G R m z'
    rw [← laurentTotalClass_add G R hz hz' (by rw [map_add, hz, hz', add_zero])]
    exact laurentTotalClass_congr G R (by rw [map_add, map_add, Submodule.coe_add]) _ _
  map_smul' a z := by
    have hz := laurentDifferential_laurentMaslovChainEquiv_iCycles G R m z
    rw [RingHom.id_apply, ← laurentTotalClass_smul G R a hz (by
      rw [← algebraMap_smul (LaurentPolynomial R), map_smul, hz, smul_zero])]
    exact laurentTotalClass_congr G R (by rw [map_smul, map_smul, Submodule.coe_smul]) _ _

/-- The value of the map from graded cycles to total homology. -/
theorem laurentGradedCyclesToTotal_apply (m : ℤ) (z : (laurentMaslovComplex G R).cycles m) :
    laurentGradedCyclesToTotal G R m z = laurentTotalClass G R _
      (laurentDifferential_laurentMaslovChainEquiv_iCycles G R m z) := rfl

/-- The total class of the underlying chain of a graded boundary vanishes. -/
theorem toCycles_comp_laurentGradedCyclesToTotal (m : ℤ) :
    (laurentMaslovComplex G R).toCycles (m + 1) m ≫
      ModuleCat.ofHom (laurentGradedCyclesToTotal G R m) = 0 := by
  ext b : 2
  have hi := congrArg (fun f : (laurentMaslovComplex G R).X (m + 1) ⟶
      (laurentMaslovComplex G R).X m => f b) ((laurentMaslovComplex G R).toCycles_i (m + 1) m)
  change (laurentMaslovComplex G R).iCycles m ((laurentMaslovComplex G R).toCycles (m + 1) m b) =
    (laurentMaslovComplex G R).d (m + 1) m b at hi
  change laurentGradedCyclesToTotal G R m ((laurentMaslovComplex G R).toCycles (m + 1) m b) = 0
  rw [laurentGradedCyclesToTotal_apply, laurentTotalClass_eq_zero_iff]
  refine ⟨laurentMaslovChainEquiv G R (m + 1) b, ?_⟩
  rw [hi]
  exact laurentMaslovChainEquiv_d G R m b

/-- The `R`-linear map from the homology of the graded complex in degree `m` to the total
homology, induced by forgetting the Maslov grading. -/
def laurentGradedToTotal (m : ℤ) :
    (laurentMaslovComplex G R).homology m →ₗ[R] laurentTotalHomology G R :=
  (Cofork.IsColimit.desc ((laurentMaslovComplex G R).homologyIsCokernel (m + 1) m (by simp))
    (ModuleCat.ofHom (laurentGradedCyclesToTotal G R m))
    ((toCycles_comp_laurentGradedCyclesToTotal G R m).trans zero_comp.symm)).hom

/-- The comparison map sends the homology class of a graded cycle to the total class of its
underlying chain. -/
theorem laurentGradedToTotal_homologyπ (m : ℤ) (z : (laurentMaslovComplex G R).cycles m) :
    laurentGradedToTotal G R m ((laurentMaslovComplex G R).homologyπ m z) =
      laurentTotalClass G R _ (laurentDifferential_laurentMaslovChainEquiv_iCycles G R m z) := by
  have h := congrArg (fun f : (laurentMaslovComplex G R).cycles m ⟶
      ModuleCat.of R (laurentTotalHomology G R) => f z)
    (Cofork.IsColimit.π_desc' ((laurentMaslovComplex G R).homologyIsCokernel (m + 1) m
      (by simp)) (ModuleCat.ofHom (laurentGradedCyclesToTotal G R m))
      ((toCycles_comp_laurentGradedCyclesToTotal G R m).trans zero_comp.symm))
  exact h

/-- Every homology class of the graded complex is represented by a cycle. -/
theorem laurentMaslovComplex_homologyπ_surjective (m : ℤ) :
    Function.Surjective ((laurentMaslovComplex G R).homologyπ m) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The comparison map from graded homology to total homology is injective. -/
theorem laurentGradedToTotal_injective (m : ℤ) :
    Function.Injective (laurentGradedToTotal G R m) := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨z, rfl⟩ := laurentMaslovComplex_homologyπ_surjective G R m ξ
  rw [laurentGradedToTotal_homologyπ, laurentTotalClass_eq_zero_iff] at hξ
  obtain ⟨w, hw⟩ := hξ
  obtain ⟨w', hw', hcw'⟩ := exists_mem_maslovPiece_of_eq_laurentDifferential G R
    (laurentMaslovChainEquiv G R m ((laurentMaslovComplex G R).iCycles m z)).property w hw
  let b : (laurentMaslovComplex G R).X (m + 1) :=
    (laurentMaslovChainEquiv G R (m + 1)).symm ⟨w', hw'⟩
  have hb : (laurentMaslovChainEquiv G R (m + 1) b : LaurentChain R n) = w' :=
    congrArg Subtype.val ((laurentMaslovChainEquiv G R (m + 1)).apply_symm_apply ⟨w', hw'⟩)
  have hz : z = (laurentMaslovComplex G R).toCycles (m + 1) m b := by
    apply (ModuleCat.mono_iff_injective ((laurentMaslovComplex G R).iCycles m)).mp inferInstance
    have hi := congrArg (fun f : (laurentMaslovComplex G R).X (m + 1) ⟶
        (laurentMaslovComplex G R).X m => f b) ((laurentMaslovComplex G R).toCycles_i (m + 1) m)
    change (laurentMaslovComplex G R).iCycles m
      ((laurentMaslovComplex G R).toCycles (m + 1) m b) =
        (laurentMaslovComplex G R).d (m + 1) m b at hi
    rw [hi]
    apply (laurentMaslovChainEquiv G R m).injective
    apply Subtype.ext
    rw [laurentMaslovChainEquiv_d, hb]
    exact hcw'
  rw [hz]
  exact congrArg (fun f : (laurentMaslovComplex G R).X (m + 1) ⟶
    (laurentMaslovComplex G R).homology m => f b)
    ((laurentMaslovComplex G R).toCycles_comp_homologyπ (m + 1) m)

/-- The comparison maps commute with the maps induced by a Laurent chain map that preserves
the Maslov degree. -/
theorem laurentGradedToTotal_naturality
    (f : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n)
    (hdeg : ∀ m (c : LaurentChain R n), c ∈ laurentMaslovPiece G R m →
      f c ∈ laurentMaslovPiece H R m)
    (hf : laurentDifferential H R ∘ₗ f = f ∘ₗ laurentDifferential G R) (m : ℤ)
    (ξ : (laurentMaslovComplex G R).homology m) :
    laurentGradedToTotal H R m (homologyMap (laurentMaslovHomOfMap G H f hdeg hf) m ξ) =
      laurentTotalHomologyMap f hf (laurentGradedToTotal G R m ξ) := by
  obtain ⟨z, rfl⟩ := laurentMaslovComplex_homologyπ_surjective G R m ξ
  obtain ⟨φ, hφ⟩ : ∃ φ, laurentMaslovHomOfMap G H f hdeg hf = φ := ⟨_, rfl⟩
  have hnat := congrArg (fun g : (laurentMaslovComplex G R).cycles m ⟶
      (laurentMaslovComplex H R).homology m => g z) (homologyπ_naturality φ m)
  change homologyMap φ m ((laurentMaslovComplex G R).homologyπ m z) =
    (laurentMaslovComplex H R).homologyπ m (cyclesMap φ m z) at hnat
  have hi := congrArg (fun g : (laurentMaslovComplex G R).cycles m ⟶
      (laurentMaslovComplex H R).X m => g z) (cyclesMap_i φ m)
  change (laurentMaslovComplex H R).iCycles m (cyclesMap φ m z) =
    φ.f m ((laurentMaslovComplex G R).iCycles m z) at hi
  rw [hφ, hnat, laurentGradedToTotal_homologyπ, laurentGradedToTotal_homologyπ,
    laurentTotalHomologyMap_class]
  · apply laurentTotalClass_congr
    rw [hi, ← hφ]
    exact laurentMaslovChainEquiv_homOfMap G H f hdeg hf m _
  · have h := LinearMap.congr_fun hf
      (laurentMaslovChainEquiv G R m ((laurentMaslovComplex G R).iCycles m z) : LaurentChain R n)
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      laurentDifferential_laurentMaslovChainEquiv_iCycles, map_zero] at h
    exact h

end Graded

end OnLeConjecture.KnotFloer.GridFull
