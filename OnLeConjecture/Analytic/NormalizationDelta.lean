/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.BranchDelta
public import OnLeConjecture.PlaneCurve.IrreducibleFiniteIntersection
public import OnLeConjecture.PlaneCurve.AnalyticBranchCount

/-!
# The normalization of a reduced plane curve and its delta invariant

The irreducible branches of a plane germ `f` are the associate classes of
its normalized irreducible factors. For each class we fix an equation and a
locally injective parametrization `γ_b`. The normalization ring is
`Ã_f = ∏_b ℂ{t}`, and the pullbacks give a complex algebra map
`ℂ{x, y} → Ã_f` vanishing on `f`. The induced map
`A_f = ℂ{x, y}/(f) → Ã_f` is the normalization map. The delta invariant
`δ(f)` is the complex dimension of the quotient vector space `Ã_f/A_f`.

For reduced `f` the normalization map is injective, the quotient is finite
dimensional, and `Ã_f` is a finite `A_f`-module whose factors are discrete
valuation rings. The dimension does not depend on the chosen equations and
parametrizations. Adding one branch `p` to a set of branches with product
`F` changes the dimension by `δ(p) + (p · F)`, where `(p · F)` is the local
intersection multiplicity.
-/

@[expose] public section

namespace OnLeConjecture.PlaneCurve

open OnLeConjecture.Analytic OnLeConjecture.Analytic.Germ Module UniqueFactorizationMonoid

/-! ### Chosen equations and parametrizations of branches -/

/-- A chosen equation in an associate class of plane germs. -/
noncomputable def branchEquation (b : Associates (Germ 2)) : Germ 2 :=
  Quot.out b

theorem associates_mk_branchEquation (b : Associates (Germ 2)) :
    Associates.mk (branchEquation b) = b :=
  Associates.quot_out b

/-- A chosen locally injective parametrization of the branch `b`. For a
class without irreducible equation, the hyperplane inclusion is used. -/
noncomputable def branchParametrization (b : Associates (Germ 2)) : PointedMapGerm 1 2 := by
  classical
  exact if h : Irreducible (branchEquation b) then
    Classical.choose (exists_injective_parametrization_of_irreducible (branchEquation b) h)
  else hyperplaneInclusionGerm 1

theorem branchParametrization_spec (b : Associates (Germ 2))
    (h : Irreducible (branchEquation b)) :
    (branchParametrization b).IsInjectiveParametrizationOf (branchEquation b) := by
  classical
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec
    (exists_injective_parametrization_of_irreducible (branchEquation b) h)
  unfold branchParametrization
  rw [dif_pos h]
  exact ⟨h3, h1, h2⟩

/-- The irreducible branches of `f`: the associate classes of its distinct
normalized irreducible factors. -/
noncomputable def branchSet (f : Germ 2) : Finset (Associates (Germ 2)) := by
  classical
  exact (normalizedFactors (Associates.mk f)).toFinset

theorem card_branchSet (f : Germ 2) : (branchSet f).card = irreducibleBranchCount f :=
  rfl

theorem mem_branchSet {f : Germ 2} {b : Associates (Germ 2)} :
    b ∈ branchSet f ↔ b ∈ normalizedFactors (Associates.mk f) := by
  classical
  unfold branchSet
  convert Multiset.mem_toFinset

theorem irreducible_branchEquation_of_mem {f : Germ 2} {b : Associates (Germ 2)}
    (hb : b ∈ branchSet f) : Irreducible (branchEquation b) := by
  have h := irreducible_of_normalized_factor b (mem_branchSet.mp hb)
  rwa [← associates_mk_branchEquation b, Associates.irreducible_mk] at h

theorem branchEquation_dvd_of_mem {f : Germ 2} {b : Associates (Germ 2)}
    (hb : b ∈ branchSet f) : branchEquation b ∣ f := by
  have h := dvd_of_mem_normalizedFactors (mem_branchSet.mp hb)
  rwa [← associates_mk_branchEquation b, Associates.mk_dvd_mk] at h

/-- The product of the chosen equations of a finite set of branches. -/
noncomputable def branchProduct (s : Finset (Associates (Germ 2))) : Germ 2 :=
  ∏ b ∈ s, branchEquation b

/-! ### Products of branch pullbacks -/

/-- The product of the pullbacks along the chosen parametrizations. -/
noncomputable def branchProductMap (s : Finset (Associates (Germ 2))) :
    Germ 2 →ₐ[ℂ] (s → Germ 1) :=
  AlgHom.pi fun b : s => (branchParametrization b.1).pullbackAlgHom

theorem branchProductMap_apply (s : Finset (Associates (Germ 2))) (g : Germ 2) (b : s) :
    branchProductMap s g b = (branchParametrization b.1).pullbackRingHom g :=
  rfl

/-- The complex codimension of the image of `branchProductMap s`. -/
noncomputable def branchCodim (s : Finset (Associates (Germ 2))) : ℕ :=
  finrank ℂ ((s → Germ 1) ⧸ LinearMap.range (branchProductMap s).toLinearMap)

/-! ### The normalization -/

/-- The normalization ring `Ã_f`, one copy of `ℂ{t}` for each branch. -/
abbrev NormalizationRing (f : Germ 2) : Type := branchSet f → Germ 1

/-- The pullback from `ℂ{x, y}` to the normalization ring. -/
noncomputable def normalizationMap (f : Germ 2) : Germ 2 →ₐ[ℂ] NormalizationRing f :=
  branchProductMap (branchSet f)

theorem normalizationMap_self (f : Germ 2) : normalizationMap f f = 0 := by
  funext b
  obtain ⟨q, hq⟩ := branchEquation_dvd_of_mem b.2
  change (branchParametrization b.1).pullbackRingHom f = 0
  rw [show (branchParametrization b.1).pullbackRingHom f =
      (branchParametrization b.1).pullbackRingHom (branchEquation b.1 * q) from congrArg _ hq,
    map_mul, (branchParametrization_spec b.1 (irreducible_branchEquation_of_mem b.2)).2.1,
    zero_mul]

/-- The normalization map `A_f = ℂ{x, y}/(f) → Ã_f`. -/
noncomputable def normalizationQuotientMap (f : Germ 2) :
    (Germ 2 ⧸ Ideal.span {f}) →ₐ[ℂ] NormalizationRing f :=
  Ideal.Quotient.liftₐ (Ideal.span {f}) (normalizationMap f) (by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, normalizationMap_self, mul_zero])

/-- The delta invariant `δ(f) = dim_ℂ (Ã_f/A_f)`, computed in the quotient
of complex vector spaces. -/
noncomputable def deltaInvariant (f : Germ 2) : ℕ :=
  finrank ℂ (NormalizationRing f ⧸ LinearMap.range (normalizationQuotientMap f).toLinearMap)

theorem range_normalizationQuotientMap (f : Germ 2) :
    LinearMap.range (normalizationQuotientMap f).toLinearMap =
      LinearMap.range (normalizationMap f).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨Ideal.Quotient.mk _ g, rfl⟩

theorem deltaInvariant_eq_branchCodim (f : Germ 2) :
    deltaInvariant f = branchCodim (branchSet f) := by
  rw [deltaInvariant, range_normalizationQuotientMap]
  rfl

/-! ### Adding one branch -/


/-- Splitting off one branch from the product of one-variable rings. -/
noncomputable def insertEquiv [DecidableEq (Associates (Germ 2))]
    {s : Finset (Associates (Germ 2))} {p : Associates (Germ 2)}
    (hp : p ∉ s) : (↥(insert p s) → Germ 1) ≃ₗ[ℂ] Germ 1 × (s → Germ 1) :=
  (LinearEquiv.funCongrLeft ℂ (Germ 1) (Finset.subtypeInsertEquivOption hp).symm).trans
    (LinearEquiv.piOptionEquivProd ℂ)

theorem insertEquiv_comp [DecidableEq (Associates (Germ 2))]
    {s : Finset (Associates (Germ 2))} {p : Associates (Germ 2)}
    (hp : p ∉ s) :
    (insertEquiv hp).toLinearMap ∘ₗ (branchProductMap (insert p s)).toLinearMap =
      (branchParametrization p).pullbackAlgHom.toLinearMap.prod
        (branchProductMap s).toLinearMap := by
  refine LinearMap.ext fun g => Prod.ext ?_ ?_
  · rfl
  · funext b
    rfl

theorem not_dvd_branchProduct_of_not_mem [DecidableEq (Associates (Germ 2))]
    {s : Finset (Associates (Germ 2))}
    {p : Associates (Germ 2)} (hp : p ∉ s)
    (hs : ∀ b ∈ insert p s, Irreducible (branchEquation b)) :
    ¬ branchEquation p ∣ branchProduct s := by
  intro h
  have hirrp := hs p (Finset.mem_insert_self p s)
  obtain ⟨b, hb, hdvd⟩ := (hirrp.prime.dvd_finsetProd_iff _).mp h
  have hassoc := hirrp.associated_of_dvd (hs b (Finset.mem_insert_of_mem hb)) hdvd
  have hpb : p = b := by
    rw [← associates_mk_branchEquation p, ← associates_mk_branchEquation b]
    exact Associates.mk_eq_mk_iff_associated.mpr hassoc
  exact hp (hpb ▸ hb)

theorem span_singleton_inf_span_singleton_of_prime {p q : Germ 2} (hp : Prime p)
    (hpq : ¬ p ∣ q) : Ideal.span {p} ⊓ Ideal.span {q} = Ideal.span {p * q} := by
  ext g
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨hpg, r, rfl⟩
    obtain ⟨t, rfl⟩ := (hp.dvd_or_dvd hpg).resolve_left hpq
    exact ⟨t, by ring⟩
  · rintro ⟨t, rfl⟩
    exact ⟨⟨q * t, by ring⟩, ⟨p * t, by ring⟩⟩

/-- The complex quotient by `(g) + (h)` is the local intersection algebra. -/
theorem finiteDimensional_and_finrank_quotient_span_sup {g h : Germ 2}
    (hfin : HasFiniteIntersection g h) :
    FiniteDimensional ℂ (Germ 2 ⧸
        ((Ideal.span {g}).restrictScalars ℂ ⊔ (Ideal.span {h}).restrictScalars ℂ)) ∧
      finrank ℂ (Germ 2 ⧸
        ((Ideal.span {g}).restrictScalars ℂ ⊔ (Ideal.span {h}).restrictScalars ℂ)) =
        intersectionMultiplicity g h hfin := by
  have heq : (Ideal.span {g}).restrictScalars ℂ ⊔ (Ideal.span {h}).restrictScalars ℂ =
      (pairIdeal g h).restrictScalars ℂ := by
    rw [← Submodule.restrictScalars_sup, pairIdeal, Ideal.span_insert]
  let e := (Submodule.quotEquivOfEq _ _ heq).trans
    (Submodule.Quotient.restrictScalarsEquiv ℂ (pairIdeal g h))
  have : Module.Finite ℂ (Germ 2 ⧸ pairIdeal g h) := hfin
  exact ⟨e.symm.finiteDimensional, e.finrank_eq⟩

/-- Adding a branch `p` to a set `s` of branches. The kernel becomes the
ideal of the new product of equations, finite dimensionality is preserved,
and the codimension grows by the codimension of `p` plus the intersection
multiplicity of `p` with the product over `s`. -/
theorem branchProductMap_insert [DecidableEq (Associates (Germ 2))]
    {s : Finset (Associates (Germ 2))} {p : Associates (Germ 2)}
    (hp : p ∉ s) (hs : ∀ b ∈ insert p s, Irreducible (branchEquation b))
    (hkers : LinearMap.ker (branchProductMap s).toLinearMap =
      (Ideal.span {branchProduct s}).restrictScalars ℂ)
    (hfds : FiniteDimensional ℂ ((s → Germ 1) ⧸ LinearMap.range (branchProductMap s).toLinearMap)) :
    LinearMap.ker (branchProductMap (insert p s)).toLinearMap =
        (Ideal.span {branchProduct (insert p s)}).restrictScalars ℂ ∧
      FiniteDimensional ℂ
        ((↥(insert p s) → Germ 1) ⧸ LinearMap.range (branchProductMap (insert p s)).toLinearMap) ∧
      ∃ hfin : HasFiniteIntersection (branchEquation p) (branchProduct s),
        branchCodim (insert p s) =
          finrank ℂ (Germ 1 ⧸ (branchParametrization p).pullbackImage) + branchCodim s +
            intersectionMultiplicity (branchEquation p) (branchProduct s) hfin := by
  let α := (branchParametrization p).pullbackAlgHom.toLinearMap
  let β := (branchProductMap s).toLinearMap
  have hirrp : Irreducible (branchEquation p) := hs p (Finset.mem_insert_self p s)
  have hspec := branchParametrization_spec p hirrp
  have hkerα : LinearMap.ker α = (Ideal.span {branchEquation p}).restrictScalars ℂ :=
    PointedMapGerm.ker_pullbackAlgHom_toLinearMap hirrp hspec
  have hfdα : FiniteDimensional ℂ (Germ 1 ⧸ LinearMap.range α) :=
    (PointedMapGerm.finiteDimensional_and_two_mul_finrank_of_irreducible hirrp hspec).1
  have hnot := not_dvd_branchProduct_of_not_mem hp hs
  have hfin := hasFiniteIntersection_of_irreducible_not_dvd _ _ hirrp hnot
  obtain ⟨hXfd, hXrank⟩ := finiteDimensional_and_finrank_quotient_span_sup hfin
  obtain ⟨hfdprod, hrankprod⟩ :=
    DeltaLinearAlgebra.finiteDimensional_and_finrank_quotient_range_prod α β hfdα hfds
      (by rw [hkerα, hkers]; exact hXfd)
  have hcomp := insertEquiv_comp hp
  have hmap : (LinearMap.range (branchProductMap (insert p s)).toLinearMap).map
      ((insertEquiv hp : _ ≃ₗ[ℂ] _) : (↥(insert p s) → Germ 1) →ₗ[ℂ] Germ 1 × (s → Germ 1)) =
        LinearMap.range (α.prod β) := by
    rw [← LinearMap.range_comp]
    exact congrArg LinearMap.range hcomp
  let e := Submodule.Quotient.equiv _ _ (insertEquiv hp) hmap
  refine ⟨?_, e.symm.finiteDimensional, hfin, ?_⟩
  · have hker : LinearMap.ker (branchProductMap (insert p s)).toLinearMap =
        LinearMap.ker (α.prod β) := by
      rw [← hcomp, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    rw [hker, LinearMap.ker_prod, hkerα, hkers, ← Submodule.restrictScalars_inf,
      span_singleton_inf_span_singleton_of_prime hirrp.prime hnot,
      show branchProduct (insert p s) = branchEquation p * branchProduct s from
        Finset.prod_insert hp]
  · rw [branchCodim, e.finrank_eq, hrankprod, hkerα, hkers, hXrank]
    rfl

/-- For a finite set of irreducible branches, the kernel of the product of
pullbacks is generated by the product of the equations, and the quotient
of the product of one-variable rings by the image is finite dimensional. -/
theorem ker_branchProductMap_and_finiteDimensional (s : Finset (Associates (Germ 2)))
    (hs : ∀ b ∈ s, Irreducible (branchEquation b)) :
    LinearMap.ker (branchProductMap s).toLinearMap =
        (Ideal.span {branchProduct s}).restrictScalars ℂ ∧
      FiniteDimensional ℂ ((s → Germ 1) ⧸ LinearMap.range (branchProductMap s).toLinearMap) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · rw [branchProduct, Finset.prod_empty, Ideal.span_singleton_one]
      ext g
      simp only [LinearMap.mem_ker, Submodule.restrictScalars_top, Submodule.mem_top, iff_true]
      funext b
      exact absurd b.2 (Finset.notMem_empty _)
    · infer_instance
  | @insert p s hp ih =>
    obtain ⟨hkers, hfds⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    obtain ⟨hker, hfd, -⟩ := branchProductMap_insert hp hs hkers hfds
    exact ⟨hker, hfd⟩

/-- Hironaka's additivity formula for the codimension of a set of branches. -/
theorem branchCodim_insert [DecidableEq (Associates (Germ 2))]
    {s : Finset (Associates (Germ 2))} {p : Associates (Germ 2)}
    (hp : p ∉ s) (hs : ∀ b ∈ insert p s, Irreducible (branchEquation b)) :
    ∃ hfin : HasFiniteIntersection (branchEquation p) (branchProduct s),
      branchCodim (insert p s) =
        finrank ℂ (Germ 1 ⧸ (branchParametrization p).pullbackImage) + branchCodim s +
          intersectionMultiplicity (branchEquation p) (branchProduct s) hfin := by
  obtain ⟨hkers, hfds⟩ := ker_branchProductMap_and_finiteDimensional s
    fun b hb => hs b (Finset.mem_insert_of_mem hb)
  exact (branchProductMap_insert hp hs hkers hfds).2.2

/-! ### Normalization properties -/

theorem squarefree_associates_mk {f : Germ 2} (hf : Squarefree f) :
    Squarefree (Associates.mk f) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Associates.mk_surjective x
  rw [Associates.mk_mul_mk, Associates.mk_dvd_mk] at hx
  exact Associates.isUnit_mk.mpr (hf y hx)

/-- A reduced germ is associated to the product of the chosen equations of
its branches. -/
theorem associated_branchProduct_branchSet {f : Germ 2} (hf : Squarefree f) :
    Associated (branchProduct (branchSet f)) f := by
  classical
  rw [← Associates.mk_eq_mk_iff_associated]
  have hne : Associates.mk f ≠ 0 := Associates.mk_ne_zero.mpr hf.ne_zero
  have hnodup : (normalizedFactors (Associates.mk f)).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hne).mp (squarefree_associates_mk hf)
  have hval : (branchSet f).val = normalizedFactors (Associates.mk f) := by
    unfold branchSet
    rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
  have hprod : Associates.mk (branchProduct (branchSet f)) =
      (normalizedFactors (Associates.mk f)).prod := by
    rw [branchProduct, ← Associates.mkMonoidHom_apply, map_prod]
    simp only [Associates.mkMonoidHom_apply, associates_mk_branchEquation]
    rw [Finset.prod_eq_multiset_prod, hval, Multiset.map_id']
  rw [hprod]
  exact associated_iff_eq.mp (prod_normalizedFactors hne)

/-- The kernel of `ℂ{x, y} → Ã_f` is the ideal `(f)` for reduced `f`. -/
theorem ker_normalizationMap {f : Germ 2} (hf : Squarefree f) :
    RingHom.ker (normalizationMap f) = Ideal.span {f} := by
  obtain ⟨hker, -⟩ := ker_branchProductMap_and_finiteDimensional (branchSet f)
    fun b hb => irreducible_branchEquation_of_mem hb
  ext g
  rw [RingHom.mem_ker, ← Ideal.span_singleton_eq_span_singleton.mpr
    (associated_branchProduct_branchSet hf)]
  have h := congrArg (g ∈ ·) hker
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem, eq_iff_iff] at h
  exact h

/-- The normalization map `A_f → Ã_f` is injective for reduced `f`. -/
theorem normalizationQuotientMap_injective {f : Germ 2} (hf : Squarefree f) :
    Function.Injective (normalizationQuotientMap f) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_normalizationMap hf, RingHom.mem_ker]
  exact ha

/-- The normalization quotient `Ã_f/A_f` is finite dimensional. -/
theorem finiteDimensional_normalizationQuotient (f : Germ 2) :
    FiniteDimensional ℂ
      (NormalizationRing f ⧸ LinearMap.range (normalizationQuotientMap f).toLinearMap) := by
  rw [range_normalizationQuotientMap]
  exact (ker_branchProductMap_and_finiteDimensional (branchSet f)
    fun b hb => irreducible_branchEquation_of_mem hb).2

/-- The normalization ring `Ã_f` is a finite `A_f`-module. -/
theorem normalizationQuotientMap_finite (f : Germ 2) :
    (normalizationQuotientMap f).toRingHom.Finite := by
  let R := Germ 2 ⧸ Ideal.span {f}
  let S := NormalizationRing f
  let _ : Algebra R S := (normalizationQuotientMap f).toRingHom.toAlgebra
  have htower : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq fun c =>
    ((normalizationQuotientMap f).commutes c).symm
  let N : Submodule R S := LinearMap.range (Algebra.linearMap R S)
  have hN : N.restrictScalars ℂ = LinearMap.range (normalizationQuotientMap f).toLinearMap := by
    ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
    rfl
  have hfd : Module.Finite ℂ (S ⧸ N) := by
    have h := finiteDimensional_normalizationQuotient f
    rw [← hN] at h
    exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv ℂ N)
  have hNfin : Module.Finite R N := Module.Finite.range _
  have hQfin : Module.Finite R (S ⧸ N) := Module.Finite.of_restrictScalars_finite ℂ R (S ⧸ N)
  exact Module.Finite.of_submodule_quotient N

/-- Each factor `ℂ{t}` of the normalization ring is a discrete valuation
ring, in particular integrally closed. -/
theorem isDiscreteValuationRing_normalizationFactor :
    IsDiscreteValuationRing (Germ 1) ∧ IsIntegrallyClosed (Germ 1) :=
  ⟨inferInstance, inferInstance⟩

/-! ### Independence of the chosen data -/

/-- Injective parametrizations of associated irreducible equations are
related by a complex algebra automorphism of `ℂ{t}`. -/
theorem exists_algEquiv_pullback_eq {f f' : Germ 2} (hf : Irreducible f) (hff' : Associated f f')
    {γ γ' : PointedMapGerm 1 2} (hγ : γ.IsInjectiveParametrizationOf f)
    (hγ' : γ'.IsInjectiveParametrizationOf f') :
    ∃ e : Germ 1 ≃ₐ[ℂ] Germ 1, ∀ g, e (γ.pullbackRingHom g) = γ'.pullbackRingHom g := by
  have hf' : Irreducible f' := hff'.irreducible hf
  have hker : RingHom.ker γ.pullbackRingHom = RingHom.ker γ'.pullbackRingHom := by
    rw [parametrization_kernel_eq_span_singleton f hf γ hγ.2.1 hγ.2.2,
      parametrization_kernel_eq_span_singleton f' hf' γ' hγ'.2.1 hγ'.2.2,
      Ideal.span_singleton_eq_span_singleton.mpr hff']
  obtain ⟨e, he⟩ := γ.exists_normalization_ringEquiv γ'
    (γ.isFiniteAtOrigin_of_injective_curve hγ.1) (γ'.isFiniteAtOrigin_of_injective_curve hγ'.1)
    (γ.isBirationalAtOrigin_of_injective_curve hγ.1)
    (γ'.isBirationalAtOrigin_of_injective_curve hγ'.1) hker
  refine ⟨AlgEquiv.ofRingEquiv (f := e) (fun c => ?_), he⟩
  have h := he (constRingHom 2 c)
  rwa [γ.pullback_constRingHom, γ'.pullback_constRingHom] at h

/-- Independence of the delta invariant from the chosen branch equations,
their indexing, and their parametrizations. Let `f` be reduced, let
`p : ι → ℂ{x, y}` be pairwise non-associated irreducible equations whose
product is associated to `f`, and let `γ i` be an injective parametrization
of `p i`. Then the quotient of `∏_i ℂ{t}` by the image of `ℂ{x, y}` is
linearly isomorphic to `Ã_f/A_f`. -/
theorem nonempty_normalizationQuotient_equiv {ι : Type*} [Fintype ι] {f : Germ 2}
    (hf : Squarefree f) (p : ι → Germ 2) (hp : ∀ i, Irreducible (p i))
    (hpij : ∀ i j, Associated (p i) (p j) → i = j) (hprod : Associated (∏ i, p i) f)
    (γ : ι → PointedMapGerm 1 2) (hγ : ∀ i, (γ i).IsInjectiveParametrizationOf (p i)) :
    Nonempty (((ι → Germ 1) ⧸
        LinearMap.range (LinearMap.pi fun i => (γ i).pullbackAlgHom.toLinearMap)) ≃ₗ[ℂ]
      (NormalizationRing f ⧸ LinearMap.range (normalizationQuotientMap f).toLinearMap)) := by
  have hne : Associates.mk f ≠ 0 := Associates.mk_ne_zero.mpr hf.ne_zero
  have hmkf : Associates.mk f = ∏ i, Associates.mk (p i) := by
    rw [← Associates.mk_eq_mk_iff_associated.mpr hprod, ← Associates.mkMonoidHom_apply, map_prod]
    rfl
  have hmem : ∀ i, Associates.mk (p i) ∈ branchSet f := by
    intro i
    have hdvd : Associates.mk (p i) ∣ Associates.mk f := by
      rw [hmkf]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨q, hq, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hne
      (Associates.irreducible_mk.mpr (hp i)) hdvd
    rw [associated_iff_eq.mp hassoc]
    exact mem_branchSet.mpr hq
  let σ : ι → branchSet f := fun i => ⟨Associates.mk (p i), hmem i⟩
  have hσinj : Function.Injective σ := by
    intro i j hij
    exact hpij i j (Associates.mk_eq_mk_iff_associated.mp (congrArg Subtype.val hij))
  have hσsurj : Function.Surjective σ := by
    rintro ⟨b, hb⟩
    have hbirr : Irreducible b := irreducible_of_normalized_factor b (mem_branchSet.mp hb)
    have hbdvd : b ∣ ∏ i, Associates.mk (p i) := by
      rw [← hmkf]
      exact dvd_of_mem_normalizedFactors (mem_branchSet.mp hb)
    obtain ⟨i, -, hi⟩ := (hbirr.prime.dvd_finsetProd_iff _).mp hbdvd
    refine ⟨i, Subtype.ext ?_⟩
    exact (associated_iff_eq.mp
      (hbirr.associated_of_dvd (Associates.irreducible_mk.mpr (hp i)) hi)).symm
  let eσ : ι ≃ branchSet f := Equiv.ofBijective σ ⟨hσinj, hσsurj⟩
  have hassoc : ∀ i, Associated (p i) (branchEquation (eσ i).1) := by
    intro i
    rw [← Associates.mk_eq_mk_iff_associated, associates_mk_branchEquation]
    rfl
  choose e he using fun i => exists_algEquiv_pullback_eq (hp i) (hassoc i) (hγ i)
    (branchParametrization_spec (eσ i).1 (irreducible_branchEquation_of_mem (eσ i).2))
  let L : (ι → Germ 1) ≃ₗ[ℂ] NormalizationRing f :=
    (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv).trans
      (LinearEquiv.funCongrLeft ℂ (Germ 1) eσ.symm)
  have hcomp : (L : (ι → Germ 1) →ₗ[ℂ] NormalizationRing f) ∘ₗ
      LinearMap.pi (fun i => (γ i).pullbackAlgHom.toLinearMap) =
        (normalizationMap f).toLinearMap := by
    refine LinearMap.ext fun g => funext fun b => ?_
    change e (eσ.symm b) ((γ (eσ.symm b)).pullbackRingHom g) =
      (branchParametrization b.1).pullbackRingHom g
    rw [he, Equiv.apply_symm_apply]
  have hmap : (LinearMap.range (LinearMap.pi fun i => (γ i).pullbackAlgHom.toLinearMap)).map
      (L : (ι → Germ 1) →ₗ[ℂ] NormalizationRing f) =
        LinearMap.range (normalizationQuotientMap f).toLinearMap := by
    rw [← LinearMap.range_comp, hcomp, range_normalizationQuotientMap]
  exact ⟨Submodule.Quotient.equiv _ _ L hmap⟩

/-- The delta invariant computed from any admissible choice of branch
equations and injective parametrizations. -/
theorem finrank_eq_deltaInvariant {ι : Type*} [Fintype ι] {f : Germ 2}
    (hf : Squarefree f) (p : ι → Germ 2) (hp : ∀ i, Irreducible (p i))
    (hpij : ∀ i j, Associated (p i) (p j) → i = j) (hprod : Associated (∏ i, p i) f)
    (γ : ι → PointedMapGerm 1 2) (hγ : ∀ i, (γ i).IsInjectiveParametrizationOf (p i)) :
    finrank ℂ ((ι → Germ 1) ⧸
        LinearMap.range (LinearMap.pi fun i => (γ i).pullbackAlgHom.toLinearMap)) =
      deltaInvariant f := by
  obtain ⟨e⟩ := nonempty_normalizationQuotient_equiv hf p hp hpij hprod γ hγ
  exact e.finrank_eq

end OnLeConjecture.PlaneCurve
