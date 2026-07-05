/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.ContinuousBundleIso
import Mathlib.Topology.Algebra.Group.Torsor
import Mathlib.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-! ## An `IsTrivial` / `IsTrivialOn` predicate for bundles -/

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

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- To show that a bundle is trivial it suffices to give an isomorphism to any trivial bundle, not
just a bundle with the same base space and standard fibre. This works only if the bundle is already
known to be a fibre bundle, because otherwise the standard fibre `F` could be anything. -/
lemma isTrivial_of_continuousBundleIso {e : B ≃ₜ B'} (e' : E ≃ₜᶠ[e; F, F'] Trivial B' F') :
    IsTrivial F E := by
  obtain _ | _ := isEmpty_or_nonempty B
  · rw [isTrivial_iff_isHomeomorphicTrivialFiberBundle]
    exact ⟨Homeomorph.empty, fun x ↦ IsEmpty.elim inferInstance x⟩
  · refine ⟨?_⟩
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
lemma isTrivialOn_mono {u v : Set B} (huv : u ⊆ v) (h : IsTrivialOn F E v) : IsTrivialOn F E u := by
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

lemma isTrivialOn_iff_exists_trivialization [FiberBundle F E]
    {u : Set B} (hu : IsOpen u) (hu' : u.Nonempty) :
    IsTrivialOn F E u ↔ ∃ e : Trivialization F (π F E), e.baseSet = u := by
  refine ⟨fun h ↦ ?_, fun ⟨e, h⟩ ↦ h ▸ e.isTrivialOn_baseSet⟩
  obtain _ | _ := isEmpty_or_nonempty F
  · use {
      toOpenPartialHomeomorph := Homeomorph.empty.toOpenPartialHomeomorph
      baseSet := u
      open_baseSet := hu
      source_eq := Subsingleton.elim _ _
      target_eq := Subsingleton.elim _ _
      proj_toFun x := IsEmpty.elim inferInstance x }
  · have : Nonempty B := hu'.to_type
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

end Bundle
