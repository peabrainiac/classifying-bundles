/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
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
