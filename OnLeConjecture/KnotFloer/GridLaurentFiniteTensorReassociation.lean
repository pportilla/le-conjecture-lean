/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorSingleton
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamCanonical

/-!
# Inserting one grid factor into a finite tensor

Let `κ` be a finite index type presented as the image of an injective map from `ι`
together with one further index. A pure tensor over `ι` and one chain of the further
factor combine to a pure tensor over `κ`. This gives a Laurent-bilinear insertion map.
It preserves the Maslov degree and both filtration coordinates additively, and it
satisfies the Leibniz rule for the finite tensor differentials in characteristic two.

A Laurent-linear filtered chain map `f` from a grid complex `C(T)` to the finite tensor
over `ι` therefore induces a filtered chain map from the binary tensor `C(T) ⊗ C(H)` to
the finite tensor over `κ`, on pure tensors `c ⊗ d ↦ f(c)` with `d` inserted. If `f` carries
the normalized class of `T` to the canonical finite tensor class, the induced map carries
the binary canonical class to the canonical finite tensor class over `κ`.

The Laurent linearity of `f` is required: a chain map of the Maslov-graded vector space
complexes that does not commute with multiplication by the Laurent variable cannot be
tensored over the Laurent ring with the identity of another factor. The statement M609 is
therefore formulated for the structure `LaurentGridFiniteMap`. The instance `κ = Option ι`
gives the reassociation M609. The instance `κ = Fin (N + 1)` is used for the iterated seam.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct TensorProduct CategoryTheory HomologicalComplex

section Maps

variable (K : Type*) [Field K]

/-- The finite tensor filtration level is monotone in both bounds. -/
theorem laurentFiniteBifiltrationLevel_mono {ι : Type*} [Fintype ι]
    {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i)) {A B A' B' : ℝ}
    (hA : A ≤ A') (hB : B ≤ B') :
    laurentFiniteBifiltrationLevel (K := K) G A B ≤ laurentFiniteBifiltrationLevel G A' B' :=
  Submodule.span_mono (by
    rintro z ⟨j, a, b, x, hx, ha, hb, hz⟩
    exact ⟨j, a, b, x, hx, ha.trans hA, hb.trans hB, hz⟩)

/-- A Laurent-linear map from grid chains to a finite tensor that preserves the Maslov
degree, commutes with the differentials and preserves both filtration coordinates. -/
structure LaurentGridFiniteMap {t : ℕ} (T : GridDiagram t) {ι : Type} [Fintype ι]
    [DecidableEq ι] {n : ι → ℕ} (D : ∀ i, GridDiagram (n i)) where
  /-- The underlying Laurent-linear map. -/
  toLinearMap : LaurentChain K t →ₗ[LaurentPolynomial K] LaurentFiniteTensor (K := K) (n := n)
  mem_maslovPiece : ∀ r c, c ∈ laurentMaslovPiece T K r →
    toLinearMap c ∈ laurentFiniteMaslovPiece D r
  differential : ∀ c, toLinearMap (laurentDifferential T K c) =
    laurentFiniteDifferential D (toLinearMap c)
  mem_bifiltrationLevel : ∀ a b c, c ∈ laurentBifiltrationLevel T K a b →
    toLinearMap c ∈ laurentFiniteBifiltrationLevel D a b

/-- A Laurent-linear map from a binary tensor of grid chains to a finite tensor that
preserves the Maslov degree, commutes with the differentials and preserves both
filtration coordinates. -/
structure LaurentTensorFiniteMap {t h : ℕ} (T : GridDiagram t) (H : GridDiagram h)
    {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (D : ∀ i, GridDiagram (n i)) where
  /-- The underlying Laurent-linear map. -/
  toLinearMap : LaurentChain K t ⊗[LaurentPolynomial K] LaurentChain K h →ₗ[LaurentPolynomial K]
    LaurentFiniteTensor (K := K) (n := n)
  mem_maslovPiece : ∀ r w, w ∈ laurentTensorMaslovPiece (K := K) T H r →
    toLinearMap w ∈ laurentFiniteMaslovPiece D r
  differential : ∀ w, toLinearMap (laurentTensorDifferential T H w) =
    laurentFiniteDifferential D (toLinearMap w)
  mem_bifiltrationLevel : ∀ a b w, w ∈ laurentTensorBifiltrationLevel (K := K) T H a b →
    toLinearMap w ∈ laurentFiniteBifiltrationLevel D a b

variable {K}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {D : ∀ i, GridDiagram (n i)}

namespace LaurentGridFiniteMap

variable {t : ℕ} {T : GridDiagram t} [CharP K 2] (F : LaurentGridFiniteMap K T D)

/-- The chain map of native complexes induced by a Laurent grid map. -/
def hom : laurentMaslovComplex T K ⟶ laurentFiniteMaslovComplex (K := K) D :=
  (laurentGridPieceData T).hom (laurentFinitePieceData D) (F.toLinearMap.restrictScalars K)
    F.mem_maslovPiece F.differential

theorem hom_apply (r : ℤ) (c : (laurentMaslovComplex T K).X r) :
    (laurentFiniteMaslovChainEquiv D r (F.hom.f r c) : LaurentFiniteTensor (K := K) (n := n)) =
      F.toLinearMap (laurentMaslovChainEquiv T K r c : LaurentChain K t) :=
  PieceComplexData.hom_apply _ _ _ _ _ r c

/-- The induced chain map has shifts `(0,0)`. -/
theorem hom_shifts :
    (laurentMaslovBifiltration T K).Shifts (laurentFiniteMaslovBifiltration D) F.hom 0 0 :=
  PieceComplexData.hom_shifts (laurentGridPieceData T) (laurentFinitePieceData D) _ _ _
    F.mem_bifiltrationLevel

/-- Precomposition with a filtered Laurent grid map. -/
def precomp {t' : ℕ} {T' : GridDiagram t'}
    (g : LaurentChain K t' →ₗ[LaurentPolynomial K] LaurentChain K t)
    (hg : ∀ r c, c ∈ laurentMaslovPiece T' K r → g c ∈ laurentMaslovPiece T K r)
    (hgd : ∀ c, g (laurentDifferential T' K c) = laurentDifferential T K (g c))
    (hgl : ∀ a b c, c ∈ laurentBifiltrationLevel T' K a b →
      g c ∈ laurentBifiltrationLevel T K a b) :
    LaurentGridFiniteMap K T' D where
  toLinearMap := F.toLinearMap ∘ₗ g
  mem_maslovPiece r c hc := F.mem_maslovPiece r _ (hg r c hc)
  differential c := by simp only [LinearMap.comp_apply, hgd, F.differential]
  mem_bifiltrationLevel a b c hc := F.mem_bifiltrationLevel a b _ (hgl a b c hc)

/-- The chain map of a precomposition is the composite of chain maps. -/
theorem precomp_hom {t' : ℕ} {T' : GridDiagram t'}
    (g : LaurentChain K t' →ₗ[LaurentPolynomial K] LaurentChain K t)
    (hg : ∀ r c, c ∈ laurentMaslovPiece T' K r → g c ∈ laurentMaslovPiece T K r)
    (hgd : ∀ c, g (laurentDifferential T' K c) = laurentDifferential T K (g c))
    (hgl : ∀ a b c, c ∈ laurentBifiltrationLevel T' K a b → g c ∈ laurentBifiltrationLevel T K a b)
    (φ : laurentMaslovComplex T' K ⟶ laurentMaslovComplex T K)
    (hφ : ∀ r c, (laurentMaslovChainEquiv T K r (φ.f r c) : LaurentChain K t) =
      g (laurentMaslovChainEquiv T' K r c)) :
    (F.precomp g hg hgd hgl).hom = φ ≫ F.hom := by
  ext r : 1
  ext c
  apply (laurentFiniteMaslovChainEquiv D r).injective
  apply Subtype.ext
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply, hom_apply, hom_apply, hφ]
  rfl

end LaurentGridFiniteMap

namespace LaurentTensorFiniteMap

variable {t h : ℕ} {T : GridDiagram t} {H : GridDiagram h} [CharP K 2]
  (F : LaurentTensorFiniteMap K T H D)

/-- The chain map of native complexes induced by a Laurent tensor map. -/
def hom : laurentTensorMaslovComplex (K := K) T H ⟶ laurentFiniteMaslovComplex (K := K) D :=
  (laurentTensorPieceData T H).hom (laurentFinitePieceData D) (F.toLinearMap.restrictScalars K)
    F.mem_maslovPiece F.differential

theorem hom_apply (r : ℤ) (w : (laurentTensorMaslovComplex (K := K) T H).X r) :
    (laurentFiniteMaslovChainEquiv D r (F.hom.f r w) : LaurentFiniteTensor (K := K) (n := n)) =
      F.toLinearMap (laurentTensorMaslovChainEquiv T H r w :
        LaurentChain K t ⊗[LaurentPolynomial K] LaurentChain K h) :=
  PieceComplexData.hom_apply _ _ _ _ _ r w

/-- The induced chain map has shifts `(0,0)`. -/
theorem hom_shifts :
    (laurentTensorMaslovBifiltration (K := K) T H).Shifts (laurentFiniteMaslovBifiltration D)
      F.hom 0 0 :=
  PieceComplexData.hom_shifts (laurentTensorPieceData T H) (laurentFinitePieceData D) _ _ _
    F.mem_bifiltrationLevel

end LaurentTensorFiniteMap

end Maps

section Induced

variable {K : Type*} [Field K] [CharP K 2]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {D : ∀ i, GridDiagram (n i)}
variable {t : ℕ} {T : GridDiagram t}

/-- A chain map from a native grid complex to a finite tensor complex is the restriction to
the Maslov pieces of one Laurent-linear map of the underlying modules. -/
def LaurentGridInduced (θ : laurentMaslovComplex T K ⟶ laurentFiniteMaslovComplex (K := K) D) :
    Prop :=
  ∃ f : LaurentChain K t →ₗ[LaurentPolynomial K] LaurentFiniteTensor (K := K) (n := n),
    ∀ r c, (laurentFiniteMaslovChainEquiv D r (θ.f r c) : LaurentFiniteTensor (K := K) (n := n)) =
      f (laurentMaslovChainEquiv T K r c : LaurentChain K t)

/-- A chain map from a native binary tensor complex to a finite tensor complex is the
restriction to the Maslov pieces of one Laurent-linear map of the underlying modules. -/
def LaurentTensorInduced {h : ℕ} {H : GridDiagram h}
    (ψ : laurentTensorMaslovComplex (K := K) T H ⟶ laurentFiniteMaslovComplex (K := K) D) :
    Prop :=
  ∃ f : LaurentChain K t ⊗[LaurentPolynomial K] LaurentChain K h →ₗ[LaurentPolynomial K]
      LaurentFiniteTensor (K := K) (n := n),
    ∀ r w, (laurentFiniteMaslovChainEquiv D r (ψ.f r w) : LaurentFiniteTensor (K := K) (n := n)) =
      f (laurentTensorMaslovChainEquiv T H r w :
        LaurentChain K t ⊗[LaurentPolynomial K] LaurentChain K h)

/-- The chain map of a Laurent grid map is Laurent induced. -/
theorem LaurentGridFiniteMap.laurentGridInduced (F : LaurentGridFiniteMap K T D) :
    LaurentGridInduced F.hom :=
  ⟨F.toLinearMap, F.hom_apply⟩

/-- The chain map of a Laurent tensor map is Laurent induced. -/
theorem LaurentTensorFiniteMap.laurentTensorInduced {h : ℕ} {H : GridDiagram h}
    (F : LaurentTensorFiniteMap K T H D) : LaurentTensorInduced F.hom :=
  ⟨F.toLinearMap, F.hom_apply⟩

omit [CharP K 2] in
/-- A Laurent chain is a sum of its monomials, so a submodule containing its monomials
contains it. -/
private theorem laurentChain_mem_of_monomials (S : Submodule K (LaurentChain K t))
    (c : LaurentChain K t)
    (hc : ∀ x j, j ∈ (c x).coeff.support → laurentMonomialGenerator K j x ∈ S) :
    c ∈ S := by
  classical
  have hexp : c = ∑ x ∈ c.support, ∑ j ∈ (c x).coeff.support,
      (c x).coeff j • laurentMonomialGenerator K j x := by
    conv_lhs => rw [← c.sum_single]
    unfold Finsupp.sum
    apply Finset.sum_congr rfl
    intro x hx
    conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (c x), Finsupp.sum]
    rw [Finsupp.single_finsetSum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [laurentMonomialGenerator, LaurentPolynomial.T, Finsupp.smul_single,
      AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [hexp]
  exact S.sum_mem fun x _ => S.sum_mem fun j hj => S.smul_mem _ (hc x j hj)

omit [CharP K 2] in
/-- A monomial of a chain at a filtration level lies at the same level. -/
private theorem laurentMonomialGenerator_mem_level_of_mem {a b : ℝ} {c : LaurentChain K t}
    (hc : c ∈ laurentBifiltrationLevel T K a b) {x : GridState t} {j : ℤ}
    (hj : j ∈ (c x).coeff.support) :
    laurentMonomialGenerator K j x ∈ laurentBifiltrationLevel T K a b := by
  classical
  intro y k hk
  by_cases hy : y = x
  · subst y
    simp only [laurentMonomialGenerator, Finsupp.single_eq_same] at hk
    change k ∈ (Finsupp.single j (1 : K)).support at hk
    have hkj : k = j := by simpa using hk
    subst hkj
    exact hc _ _ hj
  · simp [laurentMonomialGenerator, Finsupp.single_eq_of_ne hy] at hk

/-- A Laurent induced chain map with shifts `(0,0)` is the chain map of a Laurent grid map. -/
theorem LaurentGridInduced.exists_laurentGridFiniteMap
    {θ : laurentMaslovComplex T K ⟶ laurentFiniteMaslovComplex (K := K) D}
    (hlin : LaurentGridInduced θ)
    (hθ : (laurentMaslovBifiltration T K).Shifts (laurentFiniteMaslovBifiltration D) θ 0 0) :
    ∃ F : LaurentGridFiniteMap K T D, F.hom = θ := by
  obtain ⟨f, hf⟩ := hlin
  have hpiece : ∀ r c, c ∈ laurentMaslovPiece T K r → f c ∈ laurentFiniteMaslovPiece D r := by
    intro r c hc
    have h := hf r ((laurentMaslovChainEquiv T K r).symm ⟨c, hc⟩)
    rw [LinearEquiv.apply_symm_apply] at h
    change _ = f c at h
    rw [← h]
    exact (laurentFiniteMaslovChainEquiv D r _).property
  have hhom : ∀ r c, c ∈ laurentMaslovPiece T K r →
      f (laurentDifferential T K c) = laurentFiniteDifferential D (f c) := by
    intro r c hc
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hcomm := congrArg (fun g => g ((laurentMaslovChainEquiv T K (m + 1)).symm ⟨c, hc⟩))
      (θ.comm (m + 1) m)
    have h1 := congrArg (fun z => (laurentFiniteMaslovChainEquiv D m z :
      LaurentFiniteTensor (K := K) (n := n))) hcomm
    simp only [ModuleCat.comp_apply] at h1
    rw [laurentFiniteMaslovChainEquiv_d, hf, hf, laurentMaslovChainEquiv_d,
      LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hd : ∀ c, f (laurentDifferential T K c) = laurentFiniteDifferential D (f c) := by
    have h : f ∘ₗ laurentDifferential T K = laurentFiniteDifferential D ∘ₗ f := by
      refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
      have hx : (Finsupp.single x 1 : LaurentChain K t) = laurentMonomialGenerator K 0 x := by
        simp [laurentMonomialGenerator]
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, hx]
      exact hhom _ _ (laurentMonomialGenerator_mem_laurentMaslovPiece T K 0 x)
    exact fun c => LinearMap.congr_fun h c
  have hlev : ∀ a b c, c ∈ laurentBifiltrationLevel T K a b →
      f c ∈ laurentFiniteBifiltrationLevel D a b := by
    intro a b c hc
    apply laurentChain_mem_of_monomials ((laurentFiniteBifiltrationLevel D a b).comap
      (f.restrictScalars K)) c
    intro x j hj
    have hm := laurentMonomialGenerator_mem_laurentMaslovPiece T K j x
    have hs := hθ a b _ ((laurentMaslovChainEquiv T K _).symm ⟨_, hm⟩) (by
      change ((laurentMaslovChainEquiv T K _) ((laurentMaslovChainEquiv T K _).symm ⟨_, hm⟩) :
        LaurentChain K t) ∈ laurentBifiltrationLevel T K a b
      rw [LinearEquiv.apply_symm_apply]
      exact laurentMonomialGenerator_mem_level_of_mem hc hj)
    rw [add_zero, add_zero] at hs
    have hs' : (laurentFiniteMaslovChainEquiv D (laurentMaslovDegree T j x)
        (θ.f (laurentMaslovDegree T j x) ((laurentMaslovChainEquiv T K
          (laurentMaslovDegree T j x)).symm ⟨laurentMonomialGenerator K j x, hm⟩)) :
        LaurentFiniteTensor (K := K) (n := n)) ∈ laurentFiniteBifiltrationLevel D a b := hs
    rw [hf, LinearEquiv.apply_symm_apply] at hs'
    exact hs'
  refine ⟨⟨f, hpiece, hd, hlev⟩, ?_⟩
  ext r : 1
  ext c
  apply (laurentFiniteMaslovChainEquiv D r).injective
  apply Subtype.ext
  rw [LaurentGridFiniteMap.hom_apply, hf]

end Induced

/-- The homology class of a cycle after a chain map is the class of the mapped cycle. -/
theorem homologyMap_homologyπ_zero {K : Type*} [Field K] {C D : ChainComplex (ModuleCat K) ℤ}
    (φ : C ⟶ D) (c : C.cycles 0) :
    homologyMap φ 0 (C.homologyπ 0 c) = D.homologyπ 0 (cyclesMap φ 0 c) :=
  homologyMap_homologyπ_eq_of_iCycles φ c _
    (congrArg (fun g : C.cycles 0 ⟶ D.X 0 => g c) (cyclesMap_i φ 0)).symm

section Insertion

/-- A finite index type `κ` presented as the image of an injective map from `ι` together
with one further index. -/
structure FactorInsertion (ι κ : Type) where
  /-- The inclusion of the old indices. -/
  embed : ι → κ
  /-- The new index. -/
  new : κ
  embed_injective : Function.Injective embed
  embed_ne_new : ∀ i, embed i ≠ new
  cover : ∀ k, k = new ∨ ∃ i, embed i = k

namespace FactorInsertion

variable {ι κ : Type} (I : FactorInsertion ι κ)

/-- A dependent family over `κ` assembled from a family over `ι` and one new value. -/
structure Comb (β : κ → Type*) where
  /-- The assembled family. -/
  comb : (∀ i, β (I.embed i)) → β I.new → ∀ k, β k
  comb_embed : ∀ x e i, comb x e (I.embed i) = x i
  comb_new : ∀ x e, comb x e I.new = e

variable {I}

/-- Updating an old coordinate before assembling updates the corresponding coordinate. -/
theorem Comb.comb_update [DecidableEq ι] [DecidableEq κ] {β : κ → Type*} (C : I.Comb β)
    (x : ∀ i, β (I.embed i)) (e : β I.new) (i : ι) (v : β (I.embed i)) :
    C.comb (Function.update x i v) e = Function.update (C.comb x e) (I.embed i) v := by
  funext k
  rcases I.cover k with rfl | ⟨i', rfl⟩
  · rw [C.comb_new, Function.update_of_ne (I.embed_ne_new i).symm, C.comb_new]
  · by_cases h : i' = i
    · subst h
      rw [C.comb_embed, Function.update_self, Function.update_self]
    · rw [C.comb_embed, Function.update_of_ne h, Function.update_of_ne (I.embed_injective.ne h),
        C.comb_embed]

/-- Changing the new value updates the new coordinate. -/
theorem Comb.comb_update_new [DecidableEq κ] {β : κ → Type*} (C : I.Comb β)
    (x : ∀ i, β (I.embed i)) (e v : β I.new) :
    C.comb x v = Function.update (C.comb x e) I.new v := by
  funext k
  rcases I.cover k with rfl | ⟨i, rfl⟩
  · rw [C.comb_new, Function.update_self]
  · rw [C.comb_embed, Function.update_of_ne (I.embed_ne_new i), C.comb_embed]

variable (I)

/-- The non-dependent extension of a function on old indices by a value at the new index. -/
def extend {α : Type*} (x : ι → α) (e : α) : κ → α := by
  classical
  exact fun k => if h : ∃ i, I.embed i = k then x h.choose else e

theorem extend_embed {α : Type*} (x : ι → α) (e : α) (i : ι) : I.extend x e (I.embed i) = x i := by
  classical
  have h : ∃ i', I.embed i' = I.embed i := ⟨i, rfl⟩
  simp only [extend, dif_pos h]
  rw [I.embed_injective h.choose_spec]

theorem extend_new {α : Type*} (x : ι → α) (e : α) : I.extend x e I.new = e := by
  classical
  have h : ¬∃ i, I.embed i = I.new := fun ⟨i, hi⟩ => I.embed_ne_new i hi
  simp only [extend, dif_neg h]

/-- The sum over `κ` splits into the old indices and the new index. -/
theorem sum_eq [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M] (f : κ → M) :
    ∑ k, f k = ∑ i, f (I.embed i) + f I.new := by
  classical
  have huniv : (Finset.univ : Finset κ) =
      insert I.new (Finset.univ.map ⟨I.embed, I.embed_injective⟩) := by
    ext k
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_map, Function.Embedding.coeFn_mk,
      true_and, true_iff]
    exact I.cover k
  have hnot : I.new ∉ Finset.univ.map ⟨I.embed, I.embed_injective⟩ := by
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and, not_exists]
    exact I.embed_ne_new
  rw [huniv, Finset.sum_insert hnot, Finset.sum_map, add_comm]
  rfl

theorem sum_extend [Fintype ι] [Fintype κ] {M : Type*} [AddCommMonoid M] (x : ι → M) (e : M) :
    ∑ k, I.extend x e k = ∑ i, x i + e := by
  rw [I.sum_eq]
  simp only [extend_embed, extend_new]

end FactorInsertion

variable {K : Type*} [Field K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (I : FactorInsertion ι κ) {n : κ → ℕ} (G : ∀ k, GridDiagram (n k))
variable (C : I.Comb (fun k => LaurentChain K (n k)))

/-- Inserting a chain of the new factor into pure tensors over the old indices. -/
def insertMultilinear :
    MultilinearMap (LaurentPolynomial K) (fun i => LaurentChain K (n (I.embed i)))
      (LaurentChain K (n I.new) →ₗ[LaurentPolynomial K] LaurentFiniteTensor (K := K) (n := n)) where
  toFun x :=
    { toFun e := tprod (LaurentPolynomial K) (C.comb x e)
      map_add' e e' := by
        rw [C.comb_update_new x 0 (e + e'), C.comb_update_new x 0 e, C.comb_update_new x 0 e',
          MultilinearMap.map_update_add]
      map_smul' a e := by
        rw [C.comb_update_new x 0 (a • e), C.comb_update_new x 0 e,
          MultilinearMap.map_update_smul]
        rfl }
  map_update_add' x i v w := by
    refine LinearMap.ext fun e => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, C.comb_update,
      MultilinearMap.map_update_add]
  map_update_smul' x i a v := by
    refine LinearMap.ext fun e => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, C.comb_update,
      MultilinearMap.map_update_smul]

/-- The Laurent-bilinear insertion of a chain of the new factor. -/
def insertLinear :
    LaurentFiniteTensor (K := K) (n := fun i => n (I.embed i)) →ₗ[LaurentPolynomial K]
      LaurentChain K (n I.new) →ₗ[LaurentPolynomial K] LaurentFiniteTensor (K := K) (n := n) :=
  PiTensorProduct.lift (insertMultilinear I C)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
@[simp]
theorem insertLinear_tprod (x : ∀ i, LaurentChain K (n (I.embed i)))
    (e : LaurentChain K (n I.new)) :
    insertLinear I C (tprod (LaurentPolynomial K) x) e =
      tprod (LaurentPolynomial K) (C.comb x e) := by
  simp [insertLinear, insertMultilinear]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem insertLinear_smul_tprod (j : ℤ) (x : ∀ i, LaurentChain K (n (I.embed i)))
    (e : LaurentChain K (n I.new)) :
    insertLinear I C ((LaurentPolynomial.T j : LaurentPolynomial K) •
        tprod (LaurentPolynomial K) x) e =
      (LaurentPolynomial.T j : LaurentPolynomial K) • tprod (LaurentPolynomial K) (C.comb x e) := by
  rw [map_smul, LinearMap.smul_apply, insertLinear_tprod]

/-- Insertion with a fixed new chain, as a map over the coefficients. -/
def insertRight (e : LaurentChain K (n I.new)) :
    LaurentFiniteTensor (K := K) (n := fun i => n (I.embed i)) →ₗ[K]
      LaurentFiniteTensor (K := K) (n := n) :=
  ((insertLinear I C).flip e).restrictScalars K

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
theorem insertRight_apply (e : LaurentChain K (n I.new))
    (z : LaurentFiniteTensor (K := K) (n := fun i => n (I.embed i))) :
    insertRight I C e z = insertLinear I C z e := rfl

omit [DecidableEq ι] in
/-- Insertion adds Maslov degrees. -/
theorem insertLinear_mem_maslovPiece {r q : ℤ}
    {z : LaurentFiniteTensor (K := K) (n := fun i => n (I.embed i))}
    (hz : z ∈ laurentFiniteMaslovPiece (fun i => G (I.embed i)) r)
    {e : LaurentChain K (n I.new)} (he : e ∈ laurentMaslovPiece (G I.new) K q) :
    insertLinear I C z e ∈ laurentFiniteMaslovPiece G (r + q) := by
  rw [← insertRight_apply]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, p, x, hx, hr, rfl⟩ := hz
    rw [insertRight_apply, insertLinear_smul_tprod]
    apply Submodule.subset_span
    refine ⟨j, I.extend p q, C.comb x e, fun k => ?_, ?_, rfl⟩
    · rcases I.cover k with rfl | ⟨i, rfl⟩
      · rw [C.comb_new, I.extend_new]
        exact he
      · rw [C.comb_embed, I.extend_embed]
        exact hx i
    · rw [I.sum_extend]
      omega
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz => simpa using Submodule.smul_mem _ a hz

omit [DecidableEq ι] in
/-- Insertion adds both filtration bounds. -/
theorem insertLinear_mem_bifiltrationLevel {A B c d : ℝ}
    {z : LaurentFiniteTensor (K := K) (n := fun i => n (I.embed i))}
    (hz : z ∈ laurentFiniteBifiltrationLevel (fun i => G (I.embed i)) A B)
    {e : LaurentChain K (n I.new)} (he : e ∈ laurentBifiltrationLevel (G I.new) K c d) :
    insertLinear I C z e ∈ laurentFiniteBifiltrationLevel G (A + c) (B + d) := by
  rw [← insertRight_apply]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, u, v, x, hx, hA, hB, rfl⟩ := hz
    rw [insertRight_apply, insertLinear_smul_tprod]
    apply Submodule.subset_span
    refine ⟨j, I.extend u c, I.extend v d, C.comb x e, fun k => ?_, ?_, ?_, rfl⟩
    · rcases I.cover k with rfl | ⟨i, rfl⟩
      · rw [C.comb_new, I.extend_new, I.extend_new]
        exact he
      · rw [C.comb_embed, I.extend_embed, I.extend_embed]
        exact hx i
    · rw [I.sum_extend]
      linarith
    · rw [I.sum_extend]
      linarith
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz => simpa using Submodule.smul_mem _ a hz

/-- The finite tensor differential satisfies the Leibniz rule for insertion. -/
theorem laurentFiniteDifferential_insertLinear
    (z : LaurentFiniteTensor (K := K) (n := fun i => n (I.embed i)))
    (e : LaurentChain K (n I.new)) :
    laurentFiniteDifferential G (insertLinear I C z e) =
      insertLinear I C (laurentFiniteDifferential (fun i => G (I.embed i)) z) e +
        insertLinear I C z (laurentDifferential (G I.new) K e) := by
  have h : laurentFiniteDifferential G ∘ₗ (insertLinear I C).flip e =
      (insertLinear I C).flip e ∘ₗ laurentFiniteDifferential (fun i => G (I.embed i)) +
        (insertLinear I C).flip (laurentDifferential (G I.new) K e) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.flip_apply, insertLinear_tprod, laurentFiniteDifferential_tprod, map_sum]
    rw [I.sum_eq, C.comb_new]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [C.comb_embed, ← C.comb_update]
    · rw [← C.comb_update_new]
  exact LinearMap.congr_fun h z

variable [CharP K 2]

/-- Insertion of a fixed degree-zero cycle of the new factor is a chain map. -/
def insertCycleHom (e : (laurentMaslovComplex (G I.new) K).cycles 0) :
    laurentFiniteMaslovComplex (K := K) (fun i => G (I.embed i)) ⟶
      laurentFiniteMaslovComplex (K := K) G :=
  (laurentFinitePieceData (fun i => G (I.embed i))).hom (laurentFinitePieceData G)
    (insertRight I C (laurentMaslovChainEquiv (G I.new) K 0
      ((laurentMaslovComplex (G I.new) K).iCycles 0 e)))
    (fun r z hz => by
      have h := insertLinear_mem_maslovPiece I G C (q := 0) hz
        (laurentMaslovChainEquiv (G I.new) K 0
          ((laurentMaslovComplex (G I.new) K).iCycles 0 e)).property
      rw [add_zero] at h
      exact h)
    (fun z => by
      change insertLinear I C (laurentFiniteDifferential (fun i => G (I.embed i)) z) _ =
        laurentFiniteDifferential G (insertLinear I C z _)
      rw [laurentFiniteDifferential_insertLinear, laurentDifferential_native_cycle, map_zero,
        add_zero])

theorem insertCycleHom_apply (e : (laurentMaslovComplex (G I.new) K).cycles 0) (r : ℤ)
    (z : (laurentFiniteMaslovComplex (K := K) (fun i => G (I.embed i))).X r) :
    (laurentFiniteMaslovChainEquiv G r ((insertCycleHom I G C e).f r z) :
        LaurentFiniteTensor (K := K) (n := n)) =
      insertLinear I C (laurentFiniteMaslovChainEquiv (fun i => G (I.embed i)) r z)
        (laurentMaslovChainEquiv (G I.new) K 0 ((laurentMaslovComplex (G I.new) K).iCycles 0 e)) :=
  PieceComplexData.hom_apply _ _ _ _ _ r z

variable {t : ℕ} {T : GridDiagram t}

/-- The tensor map `c ⊗ d ↦ f(c)` with `d` inserted, induced by a Laurent grid map `f`. -/
def LaurentGridFiniteMap.insertTensor
    (F : LaurentGridFiniteMap K T (fun i => G (I.embed i))) :
    LaurentTensorFiniteMap K T (G I.new) G where
  toLinearMap := TensorProduct.lift (insertLinear I C ∘ₗ F.toLinearMap)
  mem_maslovPiece r w hw := by
    change (TensorProduct.lift (insertLinear I C ∘ₗ F.toLinearMap)).restrictScalars K w ∈ _
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨p, q, c, d, hc, hd, rfl, rfl⟩ := hw
      simp only [LinearMap.restrictScalars_apply, TensorProduct.lift.tmul, LinearMap.comp_apply]
      exact insertLinear_mem_maslovPiece I G C (F.mem_maslovPiece p c hc) hd
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => simpa using Submodule.add_mem _ hw hw'
    | smul a w _ hw => simpa using Submodule.smul_mem _ a hw
  differential w := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      simp only [laurentTensorDifferential_tmul, map_add, TensorProduct.lift.tmul,
        LinearMap.comp_apply, F.differential]
      rw [laurentFiniteDifferential_insertLinear]
    | add w w' hw hw' => simp only [map_add, hw, hw']
  mem_bifiltrationLevel A B w hw := by
    change (TensorProduct.lift (insertLinear I C ∘ₗ F.toLinearMap)).restrictScalars K w ∈ _
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, b, c, d, x, y, hx, hy, hA, hB, rfl⟩ := hw
      simp only [LinearMap.restrictScalars_apply, TensorProduct.lift.tmul, LinearMap.comp_apply]
      exact laurentFiniteBifiltrationLevel_mono G hA hB
        (insertLinear_mem_bifiltrationLevel I G C (F.mem_bifiltrationLevel a b x hx) hy)
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add w w' _ _ hw hw' => simpa using Submodule.add_mem _ hw hw'
    | smul a w _ hw => simpa using Submodule.smul_mem _ a hw

omit [CharP K 2] in
theorem LaurentGridFiniteMap.insertTensor_tmul
    (F : LaurentGridFiniteMap K T (fun i => G (I.embed i))) (c : LaurentChain K t)
    (d : LaurentChain K (n I.new)) :
    (F.insertTensor I G C).toLinearMap (c ⊗ₜ[LaurentPolynomial K] d) =
      insertLinear I C (F.toLinearMap c) d := by
  simp [LaurentGridFiniteMap.insertTensor]

/-- The binary native class maps to the class obtained by mapping the first cycle and
inserting the second. -/
theorem LaurentGridFiniteMap.insertTensor_nativeClass
    (F : LaurentGridFiniteMap K T (fun i => G (I.embed i)))
    (c : (laurentMaslovComplex T K).cycles 0) (d : (laurentMaslovComplex (G I.new) K).cycles 0) :
    homologyMap (F.insertTensor I G C).hom 0 (laurentTensorNativeClass T (G I.new) c d) =
      homologyMap (insertCycleHom I G C d) 0
        (homologyMap F.hom 0 ((laurentMaslovComplex T K).homologyπ 0 c)) := by
  rw [homologyMap_homologyπ_zero, homologyMap_homologyπ_zero]
  apply homologyMap_homologyπ_eq_of_iCycles
  rw [laurentTensorNativeCycle_iCycles]
  have h₁ := congrArg
    (fun g : (laurentFiniteMaslovComplex (K := K) (fun i => G (I.embed i))).cycles 0 ⟶
      (laurentFiniteMaslovComplex (K := K) G).X 0 => g (cyclesMap F.hom 0 c))
    (cyclesMap_i (insertCycleHom I G C d) 0)
  have h₂ := congrArg (fun g : (laurentMaslovComplex T K).cycles 0 ⟶
      (laurentFiniteMaslovComplex (K := K) (fun i => G (I.embed i))).X 0 => g c)
    (cyclesMap_i F.hom 0)
  simp only [ModuleCat.comp_apply] at h₁ h₂
  rw [h₁, h₂]
  apply (laurentFiniteMaslovChainEquiv G 0).injective
  apply Subtype.ext
  rw [LaurentTensorFiniteMap.hom_apply, insertCycleHom_apply, LaurentGridFiniteMap.hom_apply]
  simp only [laurentTensorNativeChain, LinearEquiv.apply_symm_apply]
  exact LaurentGridFiniteMap.insertTensor_tmul I G C F _ _

section Canonical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (C₂ : I.Comb (fun k => LaurentChain (ZMod 2) (n k))) (hD : ∀ k, 2 ≤ n k)

/-- Inserting the canonical cycle of the new factor carries the canonical tensor class over
the old indices to the canonical tensor class over all indices. -/
theorem insertCycleHom_canonicalClass :
    homologyMap (insertCycleHom I G C₂ (gridCanonicalCycle (G I.new) (hD I.new))) 0
        (gridCanonicalFiniteTensorClass (fun i => G (I.embed i)) (fun i => hD (I.embed i))) =
      gridCanonicalFiniteTensorClass G hD := by
  apply homologyMap_homologyπ_eq_of_iCycles
  rw [laurentFiniteNativeCycle_iCycles, laurentFiniteNativeCycle_iCycles]
  apply (laurentFiniteMaslovChainEquiv G 0).injective
  apply Subtype.ext
  rw [insertCycleHom_apply]
  simp only [laurentFiniteNativeChain, LinearEquiv.apply_symm_apply, insertLinear_tprod]
  congr 1
  funext k
  rcases I.cover k with rfl | ⟨i, rfl⟩
  · rw [C₂.comb_new]
  · rw [C₂.comb_embed]

/-- If a Laurent grid map carries the normalized class to the canonical tensor class over the
old indices, its insertion tensor map carries the binary canonical class to the canonical
tensor class over all indices. -/
theorem LaurentGridFiniteMap.insertTensor_canonicalClass
    {T : GridDiagram t} (hT : 2 ≤ t)
    (F : LaurentGridFiniteMap (ZMod 2) T (fun i => G (I.embed i)))
    (hF : homologyMap F.hom 0 (gridCanonicalClass T hT) =
      gridCanonicalFiniteTensorClass (fun i => G (I.embed i)) (fun i => hD (I.embed i))) :
    homologyMap (F.insertTensor I G C₂).hom 0
        (laurentTensorNativeClass T (G I.new) (gridCanonicalCycle T hT)
          (gridCanonicalCycle (G I.new) (hD I.new))) =
      gridCanonicalFiniteTensorClass G hD := by
  rw [LaurentGridFiniteMap.insertTensor_nativeClass, gridCanonicalCycle_class, hF,
    insertCycleHom_canonicalClass]

end Canonical

end Insertion

section Option

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sizes of the family over `Option ι` with `none ↦ h` and `some i ↦ s i`. -/
def optionSizes (h : ℕ) (s : ι → ℕ) : Option ι → ℕ := fun o => Option.rec h s o

/-- The family over `Option ι` with `none ↦ H` and `some i ↦ D i`. -/
def optionFamily {h : ℕ} {s : ι → ℕ} (H : GridDiagram h) (D : ∀ i, GridDiagram (s i)) :
    ∀ o, GridDiagram (optionSizes h s o) :=
  fun o => Option.rec (motive := fun o => GridDiagram (optionSizes h s o)) H D o

/-- `Option ι` is `ι` with the new index `none`. -/
abbrev optionInsertion : FactorInsertion ι (Option ι) where
  embed := some
  new := none
  embed_injective := Option.some_injective ι
  embed_ne_new i := Option.some_ne_none i
  cover o := by
    cases o with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩

/-- Assembly of a family over `Option ι`. -/
def optionComb (β : Option ι → Type*) : (optionInsertion (ι := ι)).Comb β where
  comb x e o := Option.rec (motive := β) e x o
  comb_embed _ _ _ := rfl
  comb_new _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem two_le_optionSizes {h : ℕ} {s : ι → ℕ} (hh : 2 ≤ h) (hs : ∀ i, 2 ≤ s i) :
    ∀ o, 2 ≤ optionSizes h s o := by
  intro o
  cases o with
  | none => exact hh
  | some i => exact hs i

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Reassociation and tensor functoriality (M609). Let `θ` be a chain map from `C(T)` to the
finite tensor of `D` that is the restriction of one Laurent-linear map, has shifts `(0,0)`,
and carries the normalized class to the canonical tensor class. Then there is a chain map
from `C(T) ⊗ C(H)` to the finite tensor over `Option ι` of `none ↦ H`, `some i ↦ D i`, again
the restriction of one Laurent-linear map, with shifts `(0,0)`, carrying the binary canonical
class to the canonical finite tensor class. -/
theorem exists_tensorGrid_finiteTensor_map {t h : ℕ} (T : GridDiagram (t + 1))
    (H : GridDiagram (h + 1)) (hT : 2 ≤ t + 1) (hH : 2 ≤ h + 1) {s : ι → ℕ}
    (D : ∀ i, GridDiagram (s i)) (hD : ∀ i, 2 ≤ s i)
    (θ : laurentMaslovComplex T (ZMod 2) ⟶ laurentFiniteMaslovComplex (K := ZMod 2) D)
    (hlin : LaurentGridInduced θ)
    (hθ : (laurentMaslovBifiltration T (ZMod 2)).Shifts (laurentFiniteMaslovBifiltration D) θ 0 0)
    (hθc : homologyMap θ 0 (gridCanonicalClass T hT) = gridCanonicalFiniteTensorClass D hD) :
    ∃ ψ : laurentTensorMaslovComplex (K := ZMod 2) T H ⟶
        laurentFiniteMaslovComplex (K := ZMod 2) (optionFamily H D),
      LaurentTensorInduced ψ ∧
      (laurentTensorMaslovBifiltration (K := ZMod 2) T H).Shifts
          (laurentFiniteMaslovBifiltration (optionFamily H D)) ψ 0 0 ∧
        homologyMap ψ 0 (gridCanonicalBinaryTensorClass T H hT hH) =
          gridCanonicalFiniteTensorClass (optionFamily H D) (two_le_optionSizes hH hD) := by
  obtain ⟨F, rfl⟩ := hlin.exists_laurentGridFiniteMap hθ
  let Ψ := F.insertTensor optionInsertion (optionFamily H D)
    (optionComb (fun o => LaurentChain (ZMod 2) (optionSizes (h + 1) s o)))
  exact ⟨Ψ.hom, Ψ.laurentTensorInduced, Ψ.hom_shifts,
    F.insertTensor_canonicalClass optionInsertion (optionFamily H D) (optionComb _)
      (two_le_optionSizes hH hD) hT hθc⟩

end Option

section SingletonMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι] (i₀ : ι)
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- The singleton tensor equivalence as a Laurent grid map. -/
def laurentFiniteSubsingletonMap : LaurentGridFiniteMap K (G i₀) G where
  toLinearMap := (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
    (s := fun i => LaurentChain K (n i)) i₀).symm.toLinearMap
  mem_maslovPiece r c hc := (subsingletonEquiv_symm_mem_maslovPiece_iff i₀ G r c).mpr hc
  differential c := subsingletonEquiv_symm_differential i₀ G c
  mem_bifiltrationLevel a b c hc :=
    (subsingletonEquiv_symm_mem_bifiltrationLevel_iff i₀ G a b c).mpr hc

/-- The chain map of the singleton Laurent map is the singleton isomorphism. -/
theorem laurentFiniteSubsingletonMap_hom [CharP K 2] :
    (laurentFiniteSubsingletonMap i₀ G).hom =
      (laurentFiniteMaslovSubsingletonIso (K := K) i₀ G).hom := by
  ext r : 1
  ext c
  apply (laurentFiniteMaslovChainEquiv G r).injective
  apply Subtype.ext
  rw [LaurentGridFiniteMap.hom_apply, laurentFiniteMaslovSubsingletonIso_hom_apply]
  rfl

end SingletonMap

end OnLeConjecture.KnotFloer.GridFull
