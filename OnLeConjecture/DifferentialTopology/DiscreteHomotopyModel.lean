/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Discrete homotopy models

A space covered by `k` pairwise disjoint open contractible subsets is homotopy
equivalent to `Fin k` with its discrete topology. The equivalence sends a point
to the index of the subset containing it, and its homotopy inverse sends an
index to a contraction point of the corresponding subset.

A covering map over a convex subset `W` of a real normed space restricts to a
trivial covering over `W`: lifts of the identity of `W` through the points of
one fibre are continuous sections whose ranges are pairwise disjoint open
subsets of `p ⁻¹' W` homeomorphic to `W`. Consequently `p ⁻¹' W` is homotopy
equivalent to `Fin k`, where `k` is the cardinality of a fibre over `W`.

## Main results

* `nonempty_homotopyEquiv_fin_of_disjoint_contractible`: a disjoint open cover
  by `k` contractible subsets gives a homotopy equivalence with `Fin k`.
* `nonempty_homotopyEquiv_fin_of_isCoveringMapOn_convex`: the preimage of a
  convex set under a covering map over it is homotopy equivalent to `Fin k`,
  where `k` is the cardinality of a finite fibre over that set.
-/

@[expose] public noncomputable section

open ContinuousMap Function Set Topology unitInterval

namespace OnLeConjecture.DifferentialTopology

section DisjointContractible

variable {X : Type*} [TopologicalSpace X]

/-- A space covered by `k` pairwise disjoint open subsets, each of which is a
contractible space, is homotopy equivalent to `Fin k` with its discrete
topology. -/
theorem nonempty_homotopyEquiv_fin_of_disjoint_contractible {k : ℕ} (C : Fin k → Set X)
    (hopen : ∀ i, IsOpen (C i)) (hdisj : Pairwise (Disjoint on C))
    (hcover : ⋃ i, C i = Set.univ) (hcontr : ∀ i, ContractibleSpace (C i)) :
    Nonempty (X ≃ₕ Fin k) := by
  have hmem : ∀ x : X, ∃ i, x ∈ C i := fun x ↦ Set.mem_iUnion.1 (hcover ▸ Set.mem_univ x)
  choose ι hι using hmem
  have huniq : ∀ {i j : Fin k} {x : X}, x ∈ C i → x ∈ C j → i = j := fun hi hj ↦
    by_contra fun h ↦ Set.disjoint_left.1 (hdisj h) hi hj
  have hcont : Continuous ι := by
    refine continuous_discrete_rng.2 fun i ↦ ?_
    convert hopen i using 1
    ext x
    exact ⟨fun h ↦ h ▸ hι x, fun h ↦ huniq (hι x) h⟩
  have hnull : ∀ i, ∃ c : C i, (ContinuousMap.id (C i)).Homotopic (.const _ c) := fun i ↦
    @id_nullhomotopic _ _ (hcontr i)
  choose c hc using hnull
  let H : ∀ i, Homotopy (ContinuousMap.id (C i)) (.const _ (c i)) := fun i ↦ (hc i).some
  let S : Fin k → Set (I × X) := fun i ↦ Prod.snd ⁻¹' C i
  let φ : ∀ i, C(S i, X) := fun i ↦
    ⟨fun q ↦ (H i (q.1.1, ⟨q.1.2, q.2⟩) : X), by fun_prop⟩
  have hφ : ∀ (i j) (q : I × X) (hi : q ∈ S i) (hj : q ∈ S j),
      φ i ⟨q, hi⟩ = φ j ⟨q, hj⟩ := by
    intro i j q hi hj
    obtain rfl := huniq hi hj
    rfl
  have hS : ∀ q : I × X, ∃ i, S i ∈ 𝓝 q := fun q ↦
    ⟨ι q.2, ((hopen _).preimage continuous_snd).mem_nhds (hι q.2)⟩
  let G : C(I × X, X) := liftCover S φ hφ hS
  have hG : ∀ (t : I) (x : X), G (t, x) = (H (ι x) (t, ⟨x, hι x⟩) : X) := fun t x ↦
    liftCover_coe (S := S) (φ := φ) (i := ι x) ⟨(t, x), hι x⟩
  let f : C(X, Fin k) := ⟨ι, hcont⟩
  let g : C(Fin k, X) := ⟨fun i ↦ (c i : X), continuous_of_discreteTopology⟩
  have hfg : f.comp g = ContinuousMap.id (Fin k) := ContinuousMap.ext fun i ↦
    huniq (hι (c i : X)) (c i).2
  let Hgf : Homotopy (ContinuousMap.id X) (g.comp f) :=
    { toContinuousMap := G
      map_zero_left := fun x ↦ by simp [hG]
      map_one_left := fun x ↦ by simp [hG, f, g] }
  exact ⟨{ toFun := f
           invFun := g
           left_inv := ⟨Hgf.symm⟩
           right_inv := hfg ▸ Homotopic.refl _ }⟩

/-- A homotopy model by `Fin k` transfers along a homeomorphism. -/
theorem nonempty_homotopyEquiv_fin_of_homeomorph {Y : Type*} [TopologicalSpace Y] {k : ℕ}
    (e : Y ≃ₜ X) (h : Nonempty (X ≃ₕ Fin k)) : Nonempty (Y ≃ₕ Fin k) :=
  h.map e.toHomotopyEquiv.trans

end DisjointContractible

section StarConvex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V]

/-- A space homeomorphic to a nonempty star-convex subset of a real topological
vector space is contractible. -/
theorem contractibleSpace_of_homeomorph_starConvex {Y : Type*} [TopologicalSpace Y]
    {s : Set V} {x : V} (e : Y ≃ₜ s) (hs : StarConvex ℝ x s) (hne : s.Nonempty) :
    ContractibleSpace Y :=
  have := hs.contractibleSpace hne
  e.contractibleSpace

end StarConvex

section Covering

variable {E : Type*} [TopologicalSpace E] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Let `p : E → V` be a covering map over a convex subset `W` of a real normed
space, and let the fibre of `p` over some `x₀ ∈ W` be finite of cardinality `k`.
Then `p ⁻¹' W` is homotopy equivalent to `Fin k` with its discrete topology. -/
theorem nonempty_homotopyEquiv_fin_of_isCoveringMapOn_convex {p : E → V} {W : Set V}
    (hW : Convex ℝ W) (hcov : IsCoveringMapOn p W) {x₀ : V} (hx₀ : x₀ ∈ W)
    {k : ℕ} (hfin : (p ⁻¹' {x₀}).Finite) (hk : (p ⁻¹' {x₀}).ncard = k) :
    Nonempty (p ⁻¹' W ≃ₕ Fin k) := by
  let q : p ⁻¹' W → W := W.restrictPreimage p
  have hq : IsCoveringMap q := hcov.isCoveringMap_restrictPreimage
  have : ContractibleSpace W := hW.contractibleSpace ⟨x₀, hx₀⟩
  have : LocallyPathConnectedSpace W := hW.locallyPathConnectedSpace
  let a₀ : W := ⟨x₀, hx₀⟩
  have := hfin.to_subtype
  let enum : p ⁻¹' {x₀} ≃ Fin k :=
    Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, hk])
  have henum : ∀ i, p (enum.symm i : E) = x₀ := fun i ↦ (enum.symm i).2
  let e : Fin k → p ⁻¹' W := fun i ↦ ⟨enum.symm i, show p _ ∈ W from (henum i).symm ▸ hx₀⟩
  have he : ∀ i, q (e i) = ContinuousMap.id W a₀ := fun i ↦ Subtype.ext (henum i)
  choose s hs _ using fun i ↦
    hq.existsUnique_continuousMap_lifts (ContinuousMap.id W) a₀ _ (he i)
  -- Two lifts of the identity of `W` agreeing at one point coincide.
  have hsec : ∀ {t t' : C(W, p ⁻¹' W)}, q ∘ t = ContinuousMap.id W →
      q ∘ t' = ContinuousMap.id W → ∀ a, t a = t' a → t = t' := fun {t t'} ht ht' a h ↦
    ContinuousMap.ext (congrFun (hq.eq_of_comp_eq t.continuous t'.continuous
      (ht.trans ht'.symm) a h))
  have hemb : ∀ i, IsOpenEmbedding (s i) := fun i ↦
    hq.isLocalHomeomorph.isOpenEmbedding_of_comp
      (by rw [(hs i).2]; exact IsOpenEmbedding.id) (s i).continuous
  refine nonempty_homotopyEquiv_fin_of_disjoint_contractible (fun i ↦ Set.range (s i))
    (fun i ↦ (hemb i).isOpen_range) ?_ ?_ fun i ↦ (hemb i).isEmbedding.toHomeomorph.symm
      |>.contractibleSpace
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    obtain rfl : b = a := by
      have h₁ := congrFun (hs j).2 b
      have h₂ := congrFun (hs i).2 a
      simp only [Function.comp_apply, ContinuousMap.id_apply] at h₁ h₂
      rw [← h₁, ← h₂, hb]
    have := congrArg (· a₀) (hsec (hs j).2 (hs i).2 b hb)
    simp only [(hs i).1, (hs j).1] at this
    exact hij (enum.symm.injective
      (Subtype.ext (congrArg (Subtype.val : p ⁻¹' W → E) this))).symm
  · refine Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ?_
    obtain ⟨t, ⟨hty, htq⟩, -⟩ :=
      hq.existsUnique_continuousMap_lifts (ContinuousMap.id W) (q y) y rfl
    have ht₀ : (t a₀ : E) ∈ p ⁻¹' {x₀} :=
      congrArg Subtype.val (congrFun htq a₀)
    refine ⟨enum ⟨t a₀, ht₀⟩, q y, ?_⟩
    rw [← hsec htq (hs _).2 a₀ ?_, hty]
    rw [(hs _).1]
    exact Subtype.ext (by simp [e])

end Covering

end OnLeConjecture.DifferentialTopology
