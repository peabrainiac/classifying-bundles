/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousBundleIso
import ClassifyingBundles.RealInduction
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle
import Mathlib.Topology.Order.NhdsSet

/-! # An `IsTrivial` / `IsTrivialOn` predicate for bundles -/

open Topology

namespace Bundle

variable (F : Type*) {B : Type*} (E : B → Type*) [TopologicalSpace F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  (F' : Type*) {B' : Type*} (E' : B' → Type*) [TopologicalSpace F'] [TopologicalSpace B']
  [TopologicalSpace (TotalSpace F' E')]

/-- A bundle is trivial if it is isomorphic to a trivial bundle.

This is equivalent to the existing `IsHomeomorphicTrivialFiberBundle` in mathlib, but is formulated
in terms of actual bundle isomorphisms instead of homeomorphisms that respect the fibres. -/
def IsTrivial : Prop := Nonempty (E ≃ₜᶠ[F, F] Trivial B F)

/-- A bundle is trivial iff there exists a homeomorphism `TotalSpace F E ≃ₜ B × F` that respects
the fibres. -/
lemma isTrivial_iff_isHomeomorphicTrivialFiberBundle :
    IsTrivial F E ↔ IsHomeomorphicTrivialFiberBundle F (π F E) := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨e, h⟩ ↦ ⟨?_⟩⟩
  · exact ⟨e.toHomeomorph.trans (Trivial.homeomorphProd _ _), fun x ↦ rfl⟩
  · refine .ofHomeomorph (e.trans (Trivial.homeomorphProd _ _).symm) fun x ↦ ?_
    simp [h]

/-- A bundle is trivial iff there exists a global `Trivialization`. -/
lemma isTrivial_iff_exists_trivialization :
    IsTrivial F E ↔ ∃ e : Trivialization F (π F E), e.baseSet = .univ := by
  rw [isTrivial_iff_isHomeomorphicTrivialFiberBundle]
  refine ⟨fun ⟨e, h⟩ ↦ ?_, fun ⟨e, h⟩ ↦ ?_⟩
  · exact ⟨Trivialization.mk e.toOpenPartialHomeomorph
      _ isOpen_univ (by simp) (by simp) fun x hx ↦ by simp [h], rfl⟩
  · refine ⟨e.toHomeomorphOfSourceEqUnivTargetEqUniv (by simp [e.source_eq, h])
      (by simp [e.target_eq, h]), fun x ↦ ?_⟩
    simpa using e.proj_toFun x <| by simp [e.source_eq, h]

-- TODO: find home
instance [IsEmpty B] : IsEmpty (TotalSpace F E) :=
  TotalSpace.proj.isEmpty

lemma isTrivial_of_empty [IsEmpty (TotalSpace F E)] [IsEmpty (B × F)] : IsTrivial F E := by
  rw [isTrivial_iff_isHomeomorphicTrivialFiberBundle]
  exact ⟨Homeomorph.empty, fun x ↦ IsEmpty.elim inferInstance x⟩

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- To show that a bundle is trivial it suffices to give an isomorphism to any trivial bundle, not
just a bundle with the same base space and standard fibre. This works only if the bundle is already
known to be a fibre bundle, because otherwise the standard fibre `F` could be anything. -/
lemma isTrivial_of_continuousBundleIso {e : B ≃ₜ B'} (e' : E ≃ₜᶠ[e; F, F'] Trivial B' F') :
    IsTrivial F E := by
  refine (isEmpty_or_nonempty B).rec (fun _ ↦ isTrivial_of_empty F E) fun _ ↦ ⟨?_⟩
  have e'' : F ≃ₜ F' :=
    (FiberBundle.homeomorphAt F E _).symm.trans (e'.homeomorphAt (Classical.arbitrary _))
  have : CompTriple (e : Equiv B B') (e : Equiv B B').symm (Equiv.refl B) := ⟨by simp⟩
  exact e'.trans <| (ContinuousBundleIso.trivialCongr e e'').symm

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
lemma _root_.ContinuousBundleIso.isTrivial {e : B ≃ₜ B'} (e' : E ≃ₜᶠ[e; F, F'] E')
    (h : IsTrivial F' E') : IsTrivial F E := by
  obtain ⟨e''⟩ := h
  have : CompTriple (e : Equiv B B') (Equiv.refl B') (e : Equiv B B') := ⟨by simp⟩
  exact isTrivial_of_continuousBundleIso F E F' (e'.trans e'')

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] in
lemma _root_.ContinuousBundleIso.isTrivial_iff {e : B ≃ₜ B'} (e' : E ≃ₜᶠ[e; F, F'] E') :
    IsTrivial F E ↔ IsTrivial F' E' :=
  ⟨e'.symm.isTrivial (e := e.symm) _ _ _ _, e'.isTrivial _ _ _ _⟩

/-- Pullbacks of trivial bundles are trivial. -/
lemma IsTrivial.pullback {f : C(B', B)} (h : IsTrivial F E) : IsTrivial F (f *ᵖ E) := by
  obtain ⟨e⟩ := h
  rw [show Equiv.refl B = Homeomorph.refl B from rfl] at e
  have : CompTriple (Homeomorph.refl B' : Equiv _ _) (Equiv.refl B') (Equiv.refl B') := ⟨rfl⟩
  exact ⟨(e.pullbackCongr f f (.refl _) (by simp)).trans (.pullbackTrivialIso _)⟩

/-- The inclusion of a subset of a topological space, as a continuous map.
TODO: move to some more fitting place. -/
@[simps]
def _root_.ContinuousMap.subtypeVal {X : Type*} [TopologicalSpace X] {s : Set X} :
    C(s, X) where
  toFun := (↑)

/-- TODO: find home, add missing API lemmas for `.subtypeVal` and `.inclusion`. -/
@[simp]
lemma _root_.ContinuousMap.subtypeVal_comp_inclusion {X : Type*} [TopologicalSpace X] {s t : Set X}
    (h : s ⊆ t) : ContinuousMap.subtypeVal.comp (.inclusion h) = .subtypeVal := by
  ext; simp [ContinuousMap.subtypeVal, ContinuousMap.inclusion]

/-- A bundle is trivial on `u` if its pullback to `u` is trivial. -/
def IsTrivialOn (u : Set B) : Prop :=
  IsTrivial F (ContinuousMap.subtypeVal (s := u) *ᵖ E)

lemma isTrivialOn_empty : IsTrivialOn F E ∅ := by
  rw [IsTrivialOn, isTrivial_iff_isHomeomorphicTrivialFiberBundle]
  exact ⟨Homeomorph.empty, fun x ↦ IsEmpty.elim inferInstance x⟩

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [∀ b, Zero (E b)] in
/-- TODO: generalise, clean up -/
@[gcongr]
lemma IsTrivialOn.mono {u v : Set B} (huv : u ⊆ v) (h : IsTrivialOn F E v) : IsTrivialOn F E u := by
  unfold IsTrivialOn
  rw [← ContinuousMap.subtypeVal_comp_inclusion huv]
  have : ∀ b, Zero (((ContinuousMap.subtypeVal (s := v)) *ᵖ E) b) := fun b ↦
    inferInstanceAs (Zero (E b))
  have e := ContinuousBundleIso.pullbackPullbackIso (ContinuousMap.subtypeVal)
    (ContinuousMap.inclusion huv) (E := E) (F := F)
  rw [show Equiv.refl u = Homeomorph.refl u from rfl] at e
  exact e.isTrivial_iff.1 <| IsTrivial.pullback _ _ h

variable [∀ b, TopologicalSpace (E b)]

omit [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B'] [(b : B) → TopologicalSpace (E b)] in
/-- TODO: find home -/
lemma _root_.Function.Injective.pullbackLift {f : B' → B} (hf : f.Injective) :
    (Pullback.lift f : TotalSpace F (f *ᵖ E) → TotalSpace F E).Injective := by
  intro ⟨b, x⟩ ⟨b', x'⟩ h
  simp [hf.eq_iff] at h
  simpa

omit [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [TopologicalSpace B'] [(b : B) → TopologicalSpace (E b)] in
@[simp]
lemma _root_.Pullback.range_lift {f : B' → B} :
    Set.range (Pullback.lift f (F := F) (E := E)) = TotalSpace.proj ⁻¹' Set.range f := by
  ext x
  refine ⟨by rintro ⟨x', rfl⟩; simp, ?_⟩
  obtain ⟨b, x⟩ := x
  rintro ⟨b, rfl⟩
  exact ⟨⟨b, x⟩, rfl⟩

/-- TODO: find home
Note that this requires a fibre bundle because otherwise we have no assumptions on the relation
between the topology of `TotalSpace F E` and `B`. -/
lemma _root_.Topology.IsInducing.pullbackLift [FiberBundle F E] {f : B' → B} (hf : IsInducing f) :
    IsInducing (Pullback.lift f : TotalSpace F (f *ᵖ E) → TotalSpace F E) := by
  rw [isInducing_iff, Pullback.TotalSpace.topologicalSpace, pullbackTopology, inf_eq_right,
    hf.eq_induced, induced_compose,
    show f ∘ TotalSpace.proj = TotalSpace.proj ∘ Pullback.lift f by rfl, ← induced_compose]
  gcongr
  exact (FiberBundle.continuous_proj _ _).le_induced

/-- TODO: find home
Note that this requires a fibre bundle because otherwise we have no assumptions on the relation
between the topology of `TotalSpace F E` and `B`. -/
lemma _root_.Topology.IsEmbedding.pullbackLift [FiberBundle F E] {f : B' → B} (hf : IsEmbedding f) :
    IsEmbedding (Pullback.lift f : TotalSpace F (f *ᵖ E) → TotalSpace F E) :=
  ⟨hf.1.pullbackLift _ _, hf.2.pullbackLift _ _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma Trivialization.isTrivialOn_baseSet [FiberBundle F E] (e : Trivialization F (π F E)) :
    IsTrivialOn F E e.baseSet := by
  refine (isTrivial_iff_isHomeomorphicTrivialFiberBundle _ _).2 ?_
  use (IsEmbedding.toHomeomorph (.pullbackLift _ _ .subtypeVal)
    |>.trans (Homeomorph.setCongr
      (show Set.range (Pullback.lift (Subtype.val : e.baseSet → _)) = _ by
        simp [e.source_eq]))
    |>.trans e.toHomeomorphSourceTarget
    |>.trans (.setCongr (t := e.baseSet ×ˢ .univ) (by simp [e.target_eq]))
    |>.trans (Homeomorph.Set.prod _ _)
    |>.trans (.prodCongr (.refl _) (Homeomorph.Set.univ _)):)
  intro ⟨⟨b, hb⟩, x⟩
  dsimp [Homeomorph.setCongr]
  erw [Subtype.mk.injEq, e.proj_toFun]
  simpa [e.source_eq]

open Classical in
/-- The `OpenPartialHomeomorph` given by a homeomorphism between two open subsets. -/
noncomputable def _root_.Homeomorph.toOpenPartialHomeomorph' {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [Nonempty Y] {u : Set X} {v : Set Y}
    (e : u ≃ₜ v) (hu : IsOpen u) (hv : IsOpen v) :
    OpenPartialHomeomorph X Y where
  toFun x := if hx : x ∈ u then e ⟨x, hx⟩ else Classical.arbitrary _
  invFun y := if hy : y ∈ v then e.symm ⟨y, hy⟩ else Classical.arbitrary _
  source := u
  target := v
  map_source' x hx := by simp [hx]
  map_target' y hy := by simp [hy]
  left_inv' x hx := by simp [hx]
  right_inv' y hy := by simp [hy]
  open_source := hu
  open_target := hv
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_subtype_val.comp e.continuous).congr fun _ ↦ by simp
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    exact (continuous_subtype_val.comp e.symm.continuous).congr fun _ ↦ by simp

-- TODO: find home
instance [FiberBundle F E] [Nonempty B] [Nonempty F] :
    Nonempty (TotalSpace F E) :=
  ⟨⟨_, (FiberBundle.homeomorphAt F E (Classical.arbitrary B)).symm (Classical.arbitrary F)⟩⟩

instance [FiberBundle F E] [IsEmpty F] : IsEmpty (TotalSpace F E) :=
  ⟨fun x ↦ IsEmpty.elim  ‹_› (FiberBundle.homeomorphAt F E x.1 x.snd)⟩

lemma _root_.FiberBundle.isEmpty_totalSpace_iff [FiberBundle F E] :
    IsEmpty (TotalSpace F E) ↔ IsEmpty B ∨ IsEmpty F := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    obtain ⟨_, _⟩ := h
    infer_instance
  · obtain _ | _ := h <;> infer_instance

lemma isTrivialOn_iff_exists_trivialization [FiberBundle F E] {u : Set B} (hu : IsOpen u) :
    IsTrivialOn F E u ↔ ∃ e : Trivialization F (π F E), e.baseSet = u := by
  refine ⟨fun h ↦ ?_, fun ⟨e, h⟩ ↦ h ▸ e.isTrivialOn_baseSet⟩
  by_cases! h : IsEmpty B ∨ IsEmpty F
  · have _ := isEmpty_prod.2 h
    have _ := (FiberBundle.isEmpty_totalSpace_iff F E).2 h
    use {
      toOpenPartialHomeomorph := Homeomorph.empty.toOpenPartialHomeomorph
      baseSet := u
      open_baseSet := hu
      source_eq := Subsingleton.elim _ _
      target_eq := Subsingleton.elim _ _
      proj_toFun x := IsEmpty.elim inferInstance x }
  · obtain ⟨_, _⟩ := h
    have ⟨e, he⟩ := (isTrivial_iff_isHomeomorphicTrivialFiberBundle _ _).1 h
    let e' := (IsEmbedding.subtypeVal.pullbackLift F E (B' := u)).toHomeomorph.symm.trans e
      |>.trans (.prodCongr (.refl _) (Homeomorph.Set.univ _).symm)
      |>.trans (Homeomorph.Set.prod _ _).symm
    use {
      toOpenPartialHomeomorph := e'.toOpenPartialHomeomorph'
        (by simpa using hu.preimage (FiberBundle.continuous_proj _ _)) (hu.prod isOpen_univ)
      baseSet := u
      open_baseSet := hu
      source_eq := by simp [Homeomorph.toOpenPartialHomeomorph']
      target_eq := by simp [Homeomorph.toOpenPartialHomeomorph']
      proj_toFun := by
        intro p hp
        obtain ⟨p', rfl⟩ : p ∈ Set.range (Pullback.lift (Subtype.val : u → _)) := by
          simpa [Homeomorph.toOpenPartialHomeomorph'] using hp
        suffices ((e p').1 : B) = ↑p'.proj by simpa [Homeomorph.toOpenPartialHomeomorph', e']
        congr
        exact he _ }

lemma exists_mem_nhds_isTrivialOn [FiberBundle F E] (b : B) : ∃ u ∈ 𝓝 b, IsTrivialOn F E u :=
  ⟨_, (trivializationAt F E b).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F E b),
    (trivializationAt F E b).isTrivialOn_baseSet⟩

@[simp]
lemma isTrivialOn_univ [FiberBundle F E] : IsTrivialOn F E .univ ↔ IsTrivial F E := by
  rw [isTrivial_iff_exists_trivialization,
    isTrivialOn_iff_exists_trivialization F E isOpen_univ]

lemma IsTrivial.isTrivialOn [FiberBundle F E] [∀ b, Zero (E b)] (h : IsTrivial F E) {s : Set B} :
    IsTrivialOn F E s :=
  ((isTrivialOn_univ F E).2 h).mono F E (by grind)

/-- If `E` is trivial on `u`, the pullback of `f *ᵖ E` is trivial on `f ⁻¹' u`. -/
lemma IsTrivialOn.pullback [FiberBundle F E] [∀ b, Zero (E b)] {u : Set B}
    (h : IsTrivialOn F E u) (f : C(B', B)) :
    IsTrivialOn F (f *ᵖ E) (f ⁻¹' u) := by
  have : ∀ b, Zero ((f *ᵖ E) b) := fun b ↦ inferInstanceAs (Zero (E (f b)))
  have e := ContinuousBundleIso.pullbackPullbackIso (F := F) (E := E) f
    (.subtypeVal (s := f ⁻¹' u))
  rw [show Equiv.refl (f ⁻¹' u) = Homeomorph.refl (f ⁻¹' u) from rfl] at e
  refine e.isTrivial _ _ _ _ ?_
  rw [show f.comp .subtypeVal = .comp .subtypeVal (f.restrictPreimage u) by rfl]
  unfold IsTrivialOn at h
  replace e := ContinuousBundleIso.pullbackPullbackIso (F := F) (E := E) .subtypeVal
    (f.restrictPreimage u)
  rw [show Equiv.refl (f ⁻¹' u) = Homeomorph.refl (f ⁻¹' u) from rfl] at e
  refine e.symm'.isTrivial _ _ _ _ ?_
  exact h.pullback

section DisjointUnion

/-- If a bundle is trivial on two disjoint open sets, it is also trivial on their union.
TODO: generalise to non-open sets that are separated by open neighbourhoods
TODO: generalise to indexed unions -/
lemma IsTrivialOn.disjointUnion [FiberBundle F E] {s t : Set B} (hs : IsTrivialOn F E s)
    (ht : IsTrivialOn F E t) (hs' : IsOpen s) (ht' : IsOpen t) (h : Disjoint s t) :
    IsTrivialOn F E (s ∪ t) := by
  rw [isTrivialOn_iff_exists_trivialization _ _ (by assumption)] at hs ht
  obtain ⟨e, he⟩ := hs
  obtain ⟨e', he'⟩ := ht
  refine (isTrivialOn_iff_exists_trivialization _ _ (hs'.union ht')).2 ?_
  use e.disjointUnion e' (by simp_all)
  simp [Trivialization.disjointUnion, he, he']

/-- The homeomorphism between a disjoint union of sets and a disjoint union of the corresponding
subtypes when each set has a neighbourhood that is disjoint from all other sets.

This condition is the precise condition needed for the bijection to be a homeomorphism:
see `inducing_sigma`. A weaker condition like any two sets in the family having disjoint
neighbourhoods is not enough, as the example of infinite collections of singletons in
Hausdorff spaces shows. -/
@[simps! symm_apply_coe]
noncomputable def _root_.Homeomorph.Set.iUnion {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} (hs : ∀ i, ∃ u ∈ 𝓝ˢ (s i), ∀ j ≠ i, Disjoint u (s j)) :
    ⋃ i, s i ≃ₜ Σ i, s i := by
  refine ((Set.unionEqSigmaOfDisjoint fun i j h ↦ ?_).symm.toHomeomorphOfIsInducing ?_).symm
  · have ⟨u, hu, hu'⟩ := hs i
    exact (hu' j h.symm).mono_left (subset_of_mem_nhdsSet hu)
  · refine inducing_sigma.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · simp [Function.comp_def, ← IsInducing.subtypeVal.of_comp_iff, IsInducing.subtypeVal]
    · have ⟨u, hu, hu'⟩ := hs i
      have ⟨v, hvu, hv, hv'⟩ := mem_nhdsSet.1 hu
      refine ⟨(↑) ⁻¹' v, hv.preimage_val, fun x ↦ ⟨fun h ↦ ?_, ?_⟩⟩
      · simp only [Set.mem_preimage, Set.coe_unionEqSigmaOfDisjoint_symm_apply] at h
        contrapose! h
        exact Set.notMem_subset hvu <| (hu' _ h).notMem_of_mem_right x.snd.2
      · intro rfl
        simpa using hv' x.snd.2

@[simp]
lemma _root_.Homeomorph.Set.iUnion_apply_snd_coe {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} (hs : ∀ i, ∃ u ∈ 𝓝ˢ (s i), ∀ j ≠ i, Disjoint u (s j)) {x : ⋃ i, s i} :
    ((Homeomorph.Set.iUnion hs x).snd : X) = x := by
  simp [Homeomorph.Set.iUnion]

/-- The canonical homeomorphism between the total space of any bundle on a disjoint union and the
disjoint union of the total spaces of the restrictions. -/
@[simps!]
def TotalSpace.homeomorphSigma {ι : Type*} {B : ι → Type*} [∀ i, TopologicalSpace (B i)]
    (E : (Σ i, B i) → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] :
    TotalSpace F E ≃ₜ Σ i, (TotalSpace F (ContinuousMap.sigmaMk i *ᵖ E)) := by
  refine .symm <| Equiv.toHomeomorphOfIsInducing
    { toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩, invFun x := ⟨x.1.1, x.1.2, x.2⟩ } ?_
  refine inducing_sigma.2 ⟨fun i ↦ IsEmbedding.sigmaMk.isInducing.pullbackLift F E, fun i ↦ ?_⟩
  exact ⟨_, (isOpen_sigma_fst_preimage {i}).preimage <| FiberBundle.continuous_proj F E, by simp⟩

/-- The homeomorphism between two sigma types induced by homeomorphisms between the summands. -/
@[simps!]
def _root_.Homeomorph.sigmaCongrRight {ι : Type*} {X : ι → Type*} {X' : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (X' i)] (F : (i : ι) → X i ≃ₜ X' i) :
    (Σ i, X i) ≃ₜ Σ i, X' i where
  toEquiv := Equiv.sigmaCongrRight (fun i ↦ F i)
  continuous_toFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp (map_continuous (F i))
  continuous_invFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp (map_continuous (F i).symm)

lemma isTrivial_sigma_iff {ι : Type*} {B : ι → Type*} [∀ i, TopologicalSpace (B i)]
    (E : (Σ i, B i) → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] : IsTrivial F E ↔ ∀ i, IsTrivial F (ContinuousMap.sigmaMk i *ᵖ E) := by
  refine ⟨fun h i ↦ h.pullback _ _, fun h ↦ ?_⟩
  simp only [isTrivial_iff_isHomeomorphicTrivialFiberBundle] at h ⊢
  choose e he using h
  refine ⟨(TotalSpace.homeomorphSigma F E).trans (.sigmaCongrRight e) |>.trans
    Homeomorph.sigmaProdDistrib.symm, fun x ↦ ?_⟩
  ext
  · rfl
  · simp [Homeomorph.sigmaProdDistrib, Equiv.sigmaProdDistrib, TotalSpace.homeomorphSigma, he]; rfl

/-- A fiber bundle that is trivial on a family of disjoint sets is also trivial on their union, as
long as each set admits a neighbourhood separating it from the rest.

TODO: get rid of the unnecessary `[∀ b, Zero (E b)]` assumption. -/
lemma IsTrivialOn.disjointIUnion [FiberBundle F E] [∀ b, Zero (E b)] {ι : Type*} {s : ι → Set B}
    (hs : ∀ i, ∃ u ∈ 𝓝ˢ (s i), ∀ j ≠ i, Disjoint u (s j)) (h : ∀ i, IsTrivialOn F E (s i)) :
    IsTrivialOn F E (⋃ i, s i) := by
  unfold IsTrivialOn at h ⊢
  rw [show ContinuousMap.subtypeVal = .comp (.sigma fun _ ↦ .subtypeVal)
    (Homeomorph.Set.iUnion hs : C(⋃ i, s i, Σ i, s i)) by ext; simp]
  have e := ContinuousBundleIso.pullbackPullbackIso (E := E) (F := F)
    (.sigma fun _ ↦ .subtypeVal) (Homeomorph.Set.iUnion hs : C(⋃ i, s i, Σ i, s i))
  rw [show Equiv.refl _ = (Homeomorph.refl (⋃ i, s i) : Equiv (⋃ i, s i) (⋃ i, s i)) from rfl] at e
  have _ b : Zero ((ContinuousMap.sigma (fun i ↦ .subtypeVal (s := s i)) *ᵖ E) b) :=
    inferInstanceAs (Zero (E b.snd))
  refine (e.isTrivial_iff _ _).1 <| IsTrivial.pullback F _ <| (isTrivial_sigma_iff F _).2 fun i ↦ ?_
  have e := ContinuousBundleIso.pullbackPullbackIso (E := E) (F := F)
    (.sigma fun _ ↦ .subtypeVal) (ContinuousMap.sigmaMk i : C(_, Σ i, s i))
  rw [show Equiv.refl _ = (Homeomorph.refl (s i) : Equiv (s i) (s i)) from rfl] at e
  refine e.isTrivial _ _ _ _ ?_
  convert h i <;> ext <;> rfl

end DisjointUnion

open Classical in
/-- The union of two open partial homeomorphisms that agree on the intersection of their domains. -/
@[simps! source target]
noncomputable def _root_.OpenPartialHomeomorph.union {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e e' : OpenPartialHomeomorph X Y) (h : (e.source ∩ e'.source).EqOn e e')
    (h' : e'.IsImage e.source e.target) :
    OpenPartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv e.source e.target
    e.isImage_source_target h'
  open_source := by simpa using e.open_source.union e'.open_source
  open_target := by simpa using e.open_target.union e'.open_target
  continuousOn_toFun := by
    suffices ContinuousOn (e.source.piecewise e e') (e.source ∪ e'.source) by simpa
    refine .union_of_isOpen ?_ ?_ e.open_source e'.open_source
    · refine .congr e.continuousOn_toFun ?_
      simp [Set.eqOn_piecewise, Set.eqOn_refl]
    · refine .congr e'.continuousOn_toFun <| ?_
      simp [Set.eqOn_piecewise, Set.eqOn_refl, Set.inter_comm _ _ ▸ h]
  continuousOn_invFun := by
    suffices ContinuousOn (e.target.piecewise e.symm e'.symm) (e.target ∪ e'.target) by simpa
    refine .union_of_isOpen ?_ ?_ e.open_target e'.open_target
    · refine .congr e.continuousOn_invFun ?_
      simp [Set.eqOn_piecewise, Set.eqOn_refl]
    · refine .congr e'.continuousOn_invFun <| ?_
      suffices Set.EqOn e.symm e'.symm (e'.target ∩ e.target) by
        simpa [Set.eqOn_piecewise, Set.eqOn_refl]
      intro y ⟨hy', hy⟩
      obtain ⟨x, hx', rfl⟩ : ∃ x, x ∈ e'.source ∧ e' x = y := ⟨e'.symm y, by simp [hy']⟩
      have hx := (h' hx').1 hy
      rw [e'.left_inv hx', ← @h x ⟨hx, hx'⟩, e.left_inv hx]

lemma _root_.OpenPartialHomeomorph.union_eqOn_left {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} : e.source.EqOn (e.union e' h h') e := by
  classical
  exact e.source.piecewise_eqOn e e'

lemma _root_.OpenPartialHomeomorph.union_eqOn_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} : e'.source.EqOn (e.union e' h h') e' := by
  classical
  exact e.source.piecewise_eqOn e e' |>.mono Set.inter_subset_left |>.trans h |>.union
    (e.source.piecewise_eqOn_compl e e') |>.mono (by grind)

lemma _root_.OpenPartialHomeomorph.union_apply_of_mem_left {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} {x : X} (hx : x ∈ e.source) : e.union e' h h' x = e x :=
  e.union_eqOn_left hx

lemma _root_.OpenPartialHomeomorph.union_apply_of_mem_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} {x : X} (hx : x ∈ e'.source) :
    e.union e' h h' x = e' x :=
  e.union_eqOn_right hx

/-- The union of two trivializations that agree on the intersection of their domains. -/
@[simps! baseSet]
noncomputable def Trivialization.union {B F Z : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z] {proj : Z → B} (e e' : Trivialization F proj)
    (h : (proj ⁻¹' (e.baseSet ∩ e'.baseSet)).EqOn e e') : Trivialization F proj where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.union e'.toOpenPartialHomeomorph
    (fun x hx ↦ h <| by simpa [Trivialization.source_eq] using hx)
    (fun z hz ↦ by simp [Trivialization.source_eq, Trivialization.target_eq, e'.coe_fst hz])
  baseSet := e.baseSet ∪ e'.baseSet
  open_baseSet := e.open_baseSet.union e'.open_baseSet
  source_eq := by simp [Trivialization.source_eq]
  target_eq := by simp [Trivialization.target_eq]
  proj_toFun p hp := by
    rw [OpenPartialHomeomorph.union_source, Set.mem_union] at hp
    obtain h | h := hp <;> simp [e.union_apply_of_mem_left, e.union_apply_of_mem_right, h]

open unitInterval

lemma Trivialization.continuousOn_coordChange {B F Z X : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z] [TopologicalSpace X] {proj : Z → B}
    (e₁ e₂ : Trivialization F proj) {f : X → B} {g : X → F} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hs : s.MapsTo f (e₁.baseSet ∩ e₂.baseSet)) :
    ContinuousOn (fun x ↦ e₁.coordChange e₂ (f x) (g x)) s := by
  have h x (hx : x ∈ s) : (f x, g x) ∈ e₁.target := by simp [e₁.target_eq, (hs hx).1]
  refine continuous_snd.comp_continuousOn <| e₂.continuousOn_toFun.comp
    (e₁.continuousOn_invFun.comp (hf.prodMk hg) h) fun x hx ↦ ?_
  simp [e₂.source_eq, (hs hx).2, e₁.proj_symm_apply (h x hx)]

/-- To prove that a bundle `E` on `B × I` is trivial on `u ×ˢ univ`, it suffices to prove that
every `t` has a neighbourhood `w` for which `E` is trivial on `u ×ˢ w`. -/
lemma isTrivialOn_prod_unitInterval (E : B × I → Type*) [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [∀ b, Zero (E b)] {u : Set B} (hu : IsOpen u)
    (hu' : ∀ t, ∃ w ∈ 𝓝 t, IsTrivialOn F E (u ×ˢ w)) :
    IsTrivialOn F E (u ×ˢ Set.univ) := by
  /- Using induction, we can reduce this to proving that certain sets `v₁ v₂ : Set I` for which
  which `u ×ˢ v₁` / `u ×ˢ v₂` is trivial can be glued. -/
  refine (unitInterval.induction' (fun t ↦ ?_) ?_
    (motive := fun v ↦ IsOpen v ∧ IsTrivialOn F E (u ×ˢ v))).2
  · have ⟨v, hv⟩ := hu' t
    have ⟨v', hv'⟩ := mem_nhds_iff.1 hv.1
    exact ⟨v', hv'.2.1.mem_nhds hv'.2.2, hv'.2.1, hv.2.mono _ _ (by grind)⟩
  · intro t t' ht v₁ hv₁' ⟨hv₁, h₁⟩ v₂ hv₂' ⟨hv₂, h₂⟩
    replace hv₁' := subset_of_mem_nhdsSet hv₁'; replace hv₂' := subset_of_mem_nhdsSet hv₂'
    refine ⟨Set.Iio t' ∪ v₂, (isOpen_Iio.union hv₂).mem_nhdsSet.2 (by grind),
      isOpen_Iio.union hv₂, ?_⟩
    rw [isTrivialOn_iff_exists_trivialization _ _
      (by grind [IsOpen.prod, IsOpen.union, isOpen_Iio])] at h₁ h₂ ⊢
    obtain ⟨e₁, he₁⟩ := h₁; obtain ⟨e₂, he₂⟩ := h₂
    -- It suffices to modify `e₂` so it agrees with `e₁` on `u ×ˢ (Set.Iio t' ∩ v₂)`.
    suffices h : ∃ e₂' : Trivialization F (π F E), e₂'.baseSet = u ×ˢ v₂ ∧
        ((π F E) ⁻¹' u ×ˢ (Set.Iio t' ∩ v₂)).EqOn e₁ e₂' by
      obtain ⟨e₂', he₂', h⟩ := h
      have := e₁.restrOpen (u ×ˢ Set.Iio t') (hu.prod isOpen_Iio)
      refine ⟨(e₁.restrOpen (u ×ˢ Set.Iio t') (hu.prod isOpen_Iio)).union e₂' fun x hx ↦ ?_, ?_⟩
      · refine h ?_
        simp only [Trivialization.restrOpen, he₁, he₂'] at hx ⊢
        grind
      · simp [Trivialization.restrOpen, he₁, he₂', ← Set.prod_inter,
          Set.inter_eq_right.2 <| Set.Iio_subset_Iic_self.trans hv₁']
    refine ⟨{
      toFun x := Prod.map id (e₂.coordChange e₁ (x.1.1, t' ⊓ x.1.2)) (e₂ x)
      invFun x := e₂.invFun <| Prod.map id (e₁.coordChange e₂ (x.1.1, t' ⊓ x.1.2)) x
      source := e₂.source
      target := e₂.target
      map_source' x hx := by simpa [e₂.source_eq, e₂.target_eq, e₂.coe_fst hx] using hx
      map_target' x hx := e₂.map_target <| by simpa [e₂.target_eq] using hx
      left_inv' x hx := by
        simp (disch := grind [e₂.source_eq]) [Prod.map, e₂.coordChange_coordChange]
      right_inv' x hx := by
        simp (disch := grind [e₂.target_eq]) [Prod.map, e₁.coordChange_coordChange]
      open_source := e₂.open_source
      open_target := e₂.open_target
      continuousOn_toFun := by
        refine .congr (.comp ?_ e₂.continuousOn e₂.mapsTo
            (g := fun x ↦ Prod.map id (e₂.coordChange e₁ (x.1.1, min t' x.1.2)) x))
          fun x hx ↦ by simp [hx]
        exact .prodMk (by fun_prop) <| e₂.continuousOn_coordChange _ (by fun_prop) (by fun_prop)
          fun x hx ↦ by grind [e₂.target_eq]
      continuousOn_invFun := by
        refine e₂.continuousOn_invFun.comp ?_ fun x hx ↦ by grind [e₂.target_eq]
        exact .prodMk (by fun_prop) <| e₁.continuousOn_coordChange _ (by fun_prop) (by fun_prop)
          fun x hx ↦ by grind [e₂.target_eq]
      baseSet := e₂.baseSet
      open_baseSet := e₂.open_baseSet
      source_eq := e₂.source_eq
      target_eq := e₂.target_eq
      proj_toFun x hx := by simp [hx] }, he₂, fun x hx ↦ ?_⟩
    simp [Prod.ext_iff, show x ∈ e₁.source by grind [e₁.source_eq],
      show x ∈ e₂.source by grind [e₂.source_eq], show x.1.2 ≤ t' by grind,
      show x.proj ∈ e₂.baseSet by grind]

/-- Any fibre bundle on `B × I` is trivial not just locally on `B × I` but also on `B`, in the sense
that every `b : B` has a neighbourhood `u` such that the bundle is trivial on
`u ×ˢ (univ : Set I)`. -/
lemma exists_isTrivialOn_prod_unitInterval (E : B × I → Type*) [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [∀ b, Zero (E b)] (b : B) :
    ∃ u ∈ 𝓝 b, IsOpen u ∧ IsTrivialOn F E (u ×ˢ .univ) := by
  suffices h : ∃ u ∈ 𝓝 b, IsOpen u ∧ ∀ t ∈ Set.univ, ∃ w ∈ 𝓝 t, IsTrivialOn F E (u ×ˢ w) by
    obtain ⟨u, hu, hu', h⟩ := h
    exact ⟨u, hu, hu', isTrivialOn_prod_unitInterval _ _ hu' <| by simpa using h⟩
  refine unitInterval.induction' (fun t ↦ ?_) ?_
    (motive := fun v ↦ ∃ u ∈ 𝓝 b, IsOpen u ∧ ∀ t ∈ v, ∃ w ∈ 𝓝 t, IsTrivialOn F E (u ×ˢ w))
  · have ⟨u, hu⟩ := exists_mem_nhds_isTrivialOn F E (b, t)
    have ⟨u', v, hu', hbu', hv, hv', h⟩ := mem_nhds_prod_iff'.1 hu.1
    exact ⟨v, hv.mem_nhds hv', u', hu'.mem_nhds hbu', hu', fun t' ht' ↦
      ⟨v, hv.mem_nhds ht', hu.2.mono F E h⟩⟩
  · intro t t' ht v₁ hv₁ ⟨u₁, hu₁, hu₁', h₁⟩ v₂ hv₂ ⟨u₂, hu₂, hu₂', h₂⟩
    refine ⟨v₁ ∪ v₂, nhdsSet_mono (by grind) (union_mem_nhdsSet hv₁ hv₂), ?_⟩
    refine ⟨u₁ ∩ u₂, Filter.inter_mem hu₁ hu₂, hu₁'.inter hu₂', ?_⟩
    grw [← u₁.inter_subset_left (t := u₂)] at h₁
    grw [← u₁.inter_subset_right (t := u₂)] at h₂
    grind

end Bundle
