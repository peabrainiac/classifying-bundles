/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.FiberBundle.Constructions

/-! # An `IsFiberBundle`-predicate for bundles
In this file we define a typeclass `IsFiberBundle` similar to the existing `FiberBundle`: instead
of carrying a bundle atlas / choices of trivialisations, it just guarantees that the bundle is a
fibre bundle / that enough trivialisations exist. The advantage of this over `FiberBundle` is that
since it is `Prop`-valued, we do not need to be careful when defining instances of this to avoid
diamonds and instances with bad bundle atlases: for example, we can easily provide an instance
of `IsFiberBundle` for pullback bundles, while for `FiberBundle` this isn't nicely possible because
the construction of the bundle atlas depends on a case distinction between the case where the
fibres are nonempty and the case where they are not.
-/

open TopologicalSpace Filter Set Bundle Topology

variable {ι B F X : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace F]
  (E : B → Type*) [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

variable (F)

/-- We say that a map `f : Z → B` is a fibre bundle map with standard fibre `F` if it can be
locally trivialised in the sense that for every `b : B`, there exists a `Trivialization F f`
around `b`. -/
structure IsFiberBundleMap {Z : Type*} [TopologicalSpace Z] (f : Z → B) : Prop where
  exists_trivialization' : ∀ b, ∃ e : Trivialization F f, b ∈ e.baseSet

variable {F} in
lemma IsFiberBundleMap.exists_trivialization {Z : Type*} [TopologicalSpace Z] {f : Z → B}
    (hf : IsFiberBundleMap F f) (b : B) : ∃ e : Trivialization F f, b ∈ e.baseSet :=
  hf.exists_trivialization' b

/-- We say that a bundle `E` is a fibre bundle if `π F E : TotalSpace F E → B` is a fibre bundle
in the sense of `IsFiberBundleMap`, and the fibres `E b` carry topologies that are compatible with
the topology on `TotalSpace F E`. -/
class IsFiberBundle extends IsFiberBundleMap F (π F E) where
  totalSpaceMk_isInducing' : ∀ b : B, IsInducing (@TotalSpace.mk B F E b)

instance FiberBundle.isFiberBundle [FiberBundle F E] : IsFiberBundle F E where
  totalSpaceMk_isInducing' b := FiberBundle.totalSpaceMk_isInducing' b
  exists_trivialization' b := ⟨_, FiberBundle.mem_baseSet_trivializationAt F E b⟩

namespace IsFiberBundle

variable [IsFiberBundle F E]

lemma exists_trivialization (b : B) :
    ∃ e : Trivialization F (π F E), b ∈ e.baseSet :=
  ‹IsFiberBundle F E›.exists_trivialization' b

lemma totalSpaceMk_isInducing (b : B) :
    IsInducing (@TotalSpace.mk B F E b) :=
  IsFiberBundle.totalSpaceMk_isInducing' b

theorem continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x) :=
  (totalSpaceMk_isInducing F E x).continuous

theorem totalSpaceMk_isEmbedding (x : B) : IsEmbedding (@TotalSpace.mk B F E x) :=
  ⟨totalSpaceMk_isInducing F E x, TotalSpace.mk_injective x⟩

variable {E} in
theorem map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj :=
  (exists_trivialization F E x.proj).choose.map_proj_nhds <|
    (exists_trivialization F E x.proj).choose.mem_source.2 <|
      (exists_trivialization F E x.proj).choose_spec

/-- The projection from a fiber bundle to its base is continuous. -/
@[fun_prop]
theorem continuous_proj : Continuous (π F E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le

/-- The projection from a fiber bundle to its base is an open map. -/
theorem isOpenMap_proj : IsOpenMap (π F E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge

/-- The projection from a fiber bundle with a nonempty fiber to its base is a surjective
map. -/
theorem surjective_proj [Nonempty F] : Function.Surjective (π F E) := by
  intro b
  have ⟨e, he⟩ := exists_trivialization F E b
  have ⟨p, _, hpb⟩ := e.proj_surjOn_baseSet he
  exact ⟨p, hpb⟩

/-- The projection from a fiber bundle with a nonempty fiber to its base is a quotient
map. -/
@[fun_prop]
theorem isQuotientMap_proj [Nonempty F] : IsQuotientMap (π F E) :=
  (isOpenMap_proj F E).isQuotientMap (continuous_proj F E) (surjective_proj F E)

/-- An arbitrary homeomorphism between any fiber and the model fiber.
This is useful to transfer topological properties of the model fiber. -/
noncomputable def homeomorphAt (b : B) : E b ≃ₜ F :=
  ((totalSpaceMk_isEmbedding F E b).toHomeomorph.trans <|
    Homeomorph.setCongr <| TotalSpace.range_mk b).trans <|
      (exists_trivialization F E b).choose.preimageSingletonHomeomorph <|
        (exists_trivialization F E b).choose_spec

instance [IsEmpty F] : IsEmpty (TotalSpace F E) :=
  ⟨fun x ↦ IsEmpty.elim  ‹_› (homeomorphAt F E x.1 x.snd)⟩

instance [IsEmpty (TotalSpace F E)] {B' : Type*} [TopologicalSpace B'] {f : C(B', B)} :
    IsEmpty (TotalSpace F (f *ᵖ E)) :=
  (Pullback.lift f).isEmpty

/-- Pullbacks of fibre bundles are fibre bundles. -/
instance {B' : Type*} [TopologicalSpace B'] {f : C(B', B)} :
    IsFiberBundle F (f *ᵖ E) where
  totalSpaceMk_isInducing' x := by
    refine (IsFiberBundle.totalSpaceMk_isInducing F E (f x)).of_comp
      ?_ (Pullback.continuous_lift F E f)
    simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
      induced_inf, Function.comp_def, induced_const, top_inf_eq, pullbackTopology_def]
    exact (IsFiberBundle.totalSpaceMk_isInducing F E (f x)).eq_induced.le
  exists_trivialization' b := by
    · by_cases! IsEmpty F
      · exact ⟨Trivialization.mk (Homeomorph.empty.toOpenPartialHomeomorph)
          univ (by simp) (by simp) (by simp) (fun x ↦ IsEmpty.elim inferInstance x), trivial⟩
      · have ⟨e, he⟩ := IsFiberBundle.exists_trivialization F E (f b)
        have _ b : Zero (E b) := ⟨(homeomorphAt F E b).nonempty.some⟩
        exact ⟨e.pullback f, he⟩

end IsFiberBundle

/-! Code for equivariance of local trivialisations. We place this here because
like `IsFiberBundleMap`, it takes in just a map and not a bundle given as a family of types.

TODO: find a better home for this. -/
section SMul

variable {F} in
/-- Typeclass stating that a local trivialization of a bundle map is equivariant with respect
to actions on its total space and the model fiber. -/
class Bundle.Trivialization.IsEquivariant {Z : Type*} [TopologicalSpace Z] {proj : Z → B}
    (e : Trivialization F proj) (G : Type*) [SMul G F] [SMul G Z] where
  /-- `e.source` is `G`-invariant -/
  smul_mem_source {g : G} {x : Z} (hx : x ∈ e.source) : g • x ∈ e.source
  /-- `e`  is `G`-equivariant -/
  map_smul {g : G} {x : Z} (hx : x ∈ e.source) : e (g • x) = ((e x).1, g • (e x).2)

variable {Z : Type*} [TopologicalSpace Z] {proj : Z → B} {G : Type*} [SMul G F] [SMul G Z]

@[simp]
lemma Bundle.Trivialization.smul_mem_source {G : Type*} [Group G] [SMul G F] [MulAction G Z]
    (e : Trivialization F proj) [e.IsEquivariant G] {g : G} {x : Z} :
    g • x ∈ e.source ↔ x ∈ e.source := by
  refine ⟨fun h ↦ ?_, IsEquivariant.smul_mem_source⟩
  simpa using IsEquivariant.smul_mem_source (e := e) (g := g⁻¹) h

/-- Since `e.target` is always `G`-invariant, to prove that `e` is equivariant in the sense of
`e.IsEquivariant G` it suffices to prove that the inverse map of `e` is equivariant. -/
lemma Bundle.Trivialization.isEquivariant_iff_symm (e : Trivialization F proj) :
    e.IsEquivariant G ↔ ∀ b ∈ e.baseSet, ∀ (g : G) (x : F),
      e.toOpenPartialHomeomorph.symm (b, g • x) = g • e.toOpenPartialHomeomorph.symm (b, x) := by
  refine ⟨fun h b hb g x ↦ ?_, fun h ↦ ?_⟩
  · rw [Eq.comm, e.eq_symm_apply (h.smul_mem_source <| e.map_target <| by simp [e.target_eq, hb])
      (by simp [e.target_eq, hb]), e.coe_coe, h.map_smul
        (e.map_target <| by simp [e.target_eq, hb]), e.apply_symm_apply (by simp [e.target_eq, hb])]
  · suffices h : ∀ (g : G) (x : Z) (hx : x ∈ e.source),
        g • x ∈ e.source ∧ e (g • x) = ((e x).1, g • (e x).2) from
      ⟨fun {g x} hx ↦ (h g x hx).1, fun {g x} hx ↦ (h g x hx).2⟩
    intro g x hx
    replace h := @h (proj x) (by simpa [e.source_eq] using hx) g (e x).2
    simp only [hx, symm_apply_mk_proj] at h
    rw [← h]
    refine ⟨e.map_target <| by simpa [e.source_eq, e.target_eq] using hx, ?_⟩
    rw [e.apply_symm_apply (by simpa [e.source_eq, e.target_eq] using hx), e.coe_fst hx]

lemma Bundle.Trivialization.IsEquivariant.transFiberHomeomorph {e : Trivialization F proj}
    (he : e.IsEquivariant G) {F' : Type*} [TopologicalSpace F'] [SMul G F'] {e' : F ≃ₜ F'}
    (h : ∀ (g : G) x, e' (g • x) = g • e' x) :
    (e.transFiberHomeomorph e').IsEquivariant G where
  smul_mem_source := IsEquivariant.smul_mem_source (e := e)
  map_smul hx := by simp [IsEquivariant.map_smul (e := e) hx, h]

lemma Bundle.Trivialization.IsEquivariant.compHomeomorph {e : Trivialization F proj}
    (he : e.IsEquivariant G) {Z' : Type*} [TopologicalSpace Z'] [SMul G Z'] {e' : Z' ≃ₜ Z}
    (he' : ∀ (g : G) x, e' (g • x) = g • e' x) :
    (e.compHomeomorph e').IsEquivariant G where
  smul_mem_source {g x} hx := by
    simpa [Trivialization.compHomeomorph, he'] using he.smul_mem_source (g := g) (x := e' x) hx
  map_smul {g x} hx := by
    simp [Trivialization.compHomeomorph, ← he.map_smul (g := g) (x := e' x) hx, he']

lemma Bundle.Trivialization.IsEquivariant.homeomorphComp {e : Trivialization F proj}
    (he : e.IsEquivariant G) {B' : Type*} [TopologicalSpace B'] {e' : B ≃ₜ B'} :
    (e.homeomorphComp e').IsEquivariant G where
  smul_mem_source := IsEquivariant.smul_mem_source (e := e)
  map_smul hx := by simp [Trivialization.homeomorphComp, IsEquivariant.map_smul (e := e) hx]

end SMul
