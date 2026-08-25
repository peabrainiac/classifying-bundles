/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.IsFiberBundle
import Mathlib.Topology.Homeomorph.TransferInstance

/-! # Constructing fibre bundles from fibre bundle maps
In this file we set up API for turning fibre bundle maps `E → B` into fibre bundles `B → Type _`.
-/

open TopologicalSpace Filter Set Bundle Topology

namespace Bundle

variable {E B : Type*} [TopologicalSpace B] [TopologicalSpace E]

/-- The bundle `B → Type _` given by a map `E → B`, defined as a type synonym for
`fun b ↦ f ⁻¹' {b}`. -/
def OfMap (f : E → B) (b : B) : Type _ := f ⁻¹' {b}

namespace OfMap

/-- The bijection between `TotalSpace F (OfMap f)` and `E` for a bundle map `f : E → B`. -/
@[simps apply symm_apply]
def totalSpaceEquiv (F : Type*) (f : E → B) : TotalSpace F (OfMap f) ≃ E where
  toFun x := x.2.1
  invFun x := ⟨f x, x, rfl⟩
  left_inv x := by dsimp; rw! [show f x.snd.1 = x.proj from x.snd.2]; simp

attribute [-simp] totalSpaceEquiv_apply totalSpaceEquiv_symm_apply

instance {f : E → B} {b : B} : TopologicalSpace (OfMap f b) :=
  inferInstanceAs (TopologicalSpace (f ⁻¹' {b}))

instance {F : Type*} {f : E → B} : TopologicalSpace (TotalSpace F (OfMap f)) :=
  (totalSpaceEquiv F f).topologicalSpace

/-- The homeomorphism between `TotalSpace F (OfMap f)` and `E` for a bundle map `f : E → B`. -/
@[simps! apply symm_apply]
def totalSpaceHomeomorph (F : Type*) (f : E → B) : TotalSpace F (OfMap f) ≃ₜ E :=
  (totalSpaceEquiv F f).homeomorph

attribute [-simp] totalSpaceHomeomorph_apply totalSpaceHomeomorph_symm_apply

/-- If `f` is a fibre bundle map, `Bundle.OfMap f` is a fibre bundle. -/
lemma _root_.IsFiberBundleMap.isFiberBundle_ofMap {F : Type*} [TopologicalSpace F] {f : E → B}
    (hf : IsFiberBundleMap F f) : IsFiberBundle F (OfMap f) where
  totalSpaceMk_isInducing' b := by
    rw [← (totalSpaceHomeomorph F f).isInducing.of_comp_iff]
    simp only [Function.comp_def, totalSpaceHomeomorph_apply]
    exact IsInducing.subtypeVal
  exists_trivialization' b := by
    have ⟨e, he⟩ := hf.exists_trivialization b
    rw [show π F (OfMap f) = f ∘ totalSpaceHomeomorph F f by
      ext x; simp [totalSpaceHomeomorph_apply, show f x.snd.1 = x.proj from x.snd.2]]
    exact ⟨e.compHomeomorph (totalSpaceHomeomorph F f), he⟩

/-- `Bundle.OfMap f` is a fibre bundle if and only if `f` is a fibre bundle map. -/
lemma isFiberBundle_iff {F : Type*} [TopologicalSpace F] {f : E → B} :
    IsFiberBundle F (OfMap f) ↔ IsFiberBundleMap F f := by
  refine ⟨fun hf ↦ ⟨fun b ↦ ?_⟩, fun hf ↦ hf.isFiberBundle_ofMap⟩
  have ⟨e, he⟩ := hf.exists_trivialization _ _ b
  exact ⟨e.compHomeomorph (totalSpaceHomeomorph F f).symm, he⟩

end OfMap

end Bundle
