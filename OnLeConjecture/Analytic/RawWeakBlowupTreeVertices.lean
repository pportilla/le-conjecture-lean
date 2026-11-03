/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-!
# Finite vertices of a projective weak-blowup tree

The vertices are the root together with the disjoint union of the vertices
of its child trees. The labels retain the unmodified analytic generators,
their exact orders, and the literal projective chart used on each edge.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

universe u
variable {ι : Type u}

@[expose, reducible] def Vertex : {F : ι → Germ 2} → RawProjectiveWeakBlowupTree F → Type
  | _, .node _ _ _ _ _ _ points _ _ children =>
      Unit ⊕ (Σ t : points, Vertex (children t))

instance instFiniteVertex {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    Finite T.Vertex := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      change Finite (Unit ⊕ (Σ t : points, Vertex (children t)))
      let : ∀ t : points, Finite (Vertex (children t)) := ih
      infer_instance

noncomputable instance instFintypeVertex {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    Fintype T.Vertex := Fintype.ofFinite _

noncomputable instance instDecidableEqVertex {F : ι → Germ 2}
    (T : RawProjectiveWeakBlowupTree F) : DecidableEq T.Vertex := Classical.decEq _

@[expose] def root : {F : ι → Germ 2} → (T : RawProjectiveWeakBlowupTree F) → T.Vertex
  | _, .node _ _ _ _ _ _ _ _ _ _ => Sum.inl ()

@[expose] noncomputable def generators : {F : ι → Germ 2} → (T : RawProjectiveWeakBlowupTree F) →
    T.Vertex → ι → Germ 2
  | _, .node F _ _ _ _ _ _ _ _ children => fun v =>
      match v with
      | Sum.inl _ => F
      | Sum.inr ⟨t, p⟩ => (children t).generators p

@[expose] noncomputable def multiplicity : {F : ι → Germ 2} → (T : RawProjectiveWeakBlowupTree F) →
    T.Vertex → ℕ
  | _, .node _ m _ _ _ _ _ _ _ children => fun v =>
      match v with
      | Sum.inl _ => m
      | Sum.inr ⟨t, p⟩ => (children t).multiplicity p

@[expose] noncomputable def generation : {F : ι → Germ 2} → (T : RawProjectiveWeakBlowupTree F) →
    T.Vertex → ℕ
  | _, .node _ _ _ _ _ _ _ _ _ children => fun v =>
      match v with
      | Sum.inl _ => 0
      | Sum.inr ⟨t, p⟩ => 1 + (children t).generation p

@[expose] noncomputable def predecessor : {F : ι → Germ 2} →
    (T : RawProjectiveWeakBlowupTree F) → T.Vertex → T.Vertex
  | _, .node _ _ _ _ _ _ _ _ _ children => fun v =>
      match v with
      | Sum.inl _ => Sum.inl ()
      | Sum.inr ⟨t, p⟩ =>
          if p = (children t).root then Sum.inl () else Sum.inr ⟨t, (children t).predecessor p⟩

@[expose] noncomputable def chartPoint : {F : ι → Germ 2} →
    (T : RawProjectiveWeakBlowupTree F) → T.Vertex → Option ℂ
  | _, .node _ _ _ _ _ _ _ _ _ children => fun v =>
      match v with
      | Sum.inl _ => some 0
      | Sum.inr ⟨t, p⟩ =>
          if p = (children t).root then t.val else (children t).chartPoint p

@[simp] theorem generators_root {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    T.generators T.root = F := by cases T; simp [generators, root]

@[simp] theorem generation_root {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    T.generation T.root = 0 := by cases T; simp [generation, root]

@[simp] theorem predecessor_root {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    T.predecessor T.root = T.root := by cases T; simp [predecessor, root]

theorem multiplicity_pos {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    ∀ p, 0 < T.multiplicity p := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p
      cases p with
      | inl p => simpa only [multiplicity] using hm
      | inr p => simpa only [multiplicity] using ih p.1 p.2

theorem generator_mem {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    ∀ p i, T.generators p i ∈ maximalIdeal 2 ^ T.multiplicity p := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p i
      cases p with
      | inl p => simpa only [generators, multiplicity] using horder i
      | inr p => simpa only [generators, multiplicity] using ih p.1 p.2 i

theorem generator_exact {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    ∀ p, ∃ i, T.generators p i ∉ maximalIdeal 2 ^ (T.multiplicity p + 1) := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p
      cases p with
      | inl p => simpa only [generators, multiplicity] using hexact
      | inr p => simpa only [generators, multiplicity] using ih p.1 p.2

theorem generation_eq_predecessor_add_one {F : ι → Germ 2}
    (T : RawProjectiveWeakBlowupTree F) :
    ∀ p, p ≠ T.root → T.generation p = T.generation (T.predecessor p) + 1 := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p hp
      cases p with
      | inl p =>
          cases p
          exact (hp rfl).elim
      | inr p =>
          rcases p with ⟨t, p⟩
          by_cases hroot : p = (children t).root
          · subst p
            simp only [predecessor, ↓reduceIte, generation, generation_root,
              Nat.add_zero, Nat.zero_add]
          · have h := ih t p hroot
            simp only [predecessor]
            rw [if_neg hroot]
            simp only [generation]
            omega

theorem generation_decreases {F : ι → Germ 2}
    (T : RawProjectiveWeakBlowupTree F) (p : T.Vertex) (hp : p ≠ T.root) :
    T.generation (T.predecessor p) < T.generation p := by
  rw [T.generation_eq_predecessor_add_one p hp]
  omega

theorem transform_identity {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    ∀ p, p ≠ T.root → ∀ i,
      (pointBlowupChartGerm (projectiveChartCenter (T.chartPoint p))).pullbackRingHom
        ((projectiveChartSource (T.chartPoint p)).forward.pullbackRingHom
          (T.generators (T.predecessor p) i)) =
      coordinate (1 : Fin 2) ^ T.multiplicity (T.predecessor p) * T.generators p i := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p hp i
      cases p with
      | inl p =>
          cases p
          exact (hp rfl).elim
      | inr p =>
          rcases p with ⟨t, p⟩
          by_cases hroot : p = (children t).root
          · subst p
            simp only [predecessor, chartPoint, ↓reduceIte, generators, generators_root,
              multiplicity]
            exact pointBlowupTransform_factor (projectiveChartCenter t.val) m _
              ((projectiveChartSource t.val).forward.pullback_mem_maximalIdeal_pow (horder i))
          · simpa only [predecessor, chartPoint, if_neg hroot, generators, multiplicity]
              using ih t p hroot i

theorem realizes_common_zero {F : ι → Germ 2} (T : RawProjectiveWeakBlowupTree F) :
    ∀ (p : T.Vertex) (t : Option ℂ),
      (∀ i, projectiveWeakGenerators (T.multiplicity p) (T.generators p)
        (T.generator_mem p) t i ∈ maximalIdeal 2) →
      ∃ q, q ≠ T.root ∧ T.predecessor q = p ∧ T.chartPoint q = t := by
  induction T with
  | node F m hm horder hexact hfinite points hcard hcomplete children ih =>
      intro p s hs
      cases p with
      | inl p =>
          cases p
          have hsmem : s ∈ points := by
            apply (hcomplete s).mpr
            simpa only [projectiveExceptionalBasepointSet, projectiveWeakGenerators,
              Set.mem_ofPred_eq, multiplicity, generators] using hs
          refine ⟨Sum.inr ⟨⟨s, hsmem⟩, (children ⟨s, hsmem⟩).root⟩, ?_, ?_, ?_⟩
          · simp [root]
          · simp only [predecessor, ↓reduceIte]
          · simp only [chartPoint, ↓reduceIte]
      | inr p =>
          rcases p with ⟨t, p⟩
          obtain ⟨q, hq, hpred, hchart⟩ := ih t p s
            (by simpa only [multiplicity, generators] using hs)
          refine ⟨Sum.inr ⟨t, q⟩, ?_, ?_, ?_⟩
          · simp [root]
          · simp only [predecessor, if_neg hq, hpred]
          · simpa only [chartPoint, if_neg hq] using hchart

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
