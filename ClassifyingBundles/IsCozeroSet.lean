/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.ContinuousMap.Ordered
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.PerfectlyNormal

/-! # Cozero sets
In this file cozero sets as sets that are the support of a continuous function to `ℝ`.
-/

open Set Function

open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {u : Set X}

/-- A set is a cozero set if it is the support of some continuous function to `ℝ`. -/
def IsCozeroSet (u : Set X) : Prop := ∃ f : C(X, ℝ), support f = u

-- TODO: move
@[simp]
lemma Function.support_abs {α β : Type*} [AddGroup α] [LinearOrder α] [AddLeftMono α]
    [AddRightMono α] {f : β → α} : support |f| = support f := by
  ext; simp

/-- The function that a cozero set is the support of can be chosen to be nonnegative. -/
lemma IsCozeroSet.exists_nonneg (hu : IsCozeroSet u) :
    ∃ f ≥ (0 : C(X, ℝ)), support f = u := by
  obtain ⟨f, rfl⟩ := hu
  exact ⟨|f|, by simp⟩

/-- Every cozero set is open. -/
lemma IsCozeroSet.isOpen (hu : IsCozeroSet u) : IsOpen u := by
  obtain ⟨f, rfl⟩ := hu
  exact (map_continuous f).isOpen_support

/-- Every open set in a perfectly normal space is a cozero set. -/
lemma IsOpen.isCozeroSet [PerfectlyNormalSpace X] (hu : IsOpen u) : IsCozeroSet u := by
  have ⟨f, hf⟩ := perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.1 ‹_› _ hu.isClosed_compl
  refine ⟨f, ?_⟩
  rw [compl_eq_comm] at hf
  grind [support]

lemma IsCozeroSet.preimage (hu : IsCozeroSet u) {f : Y → X} (hf : Continuous f) :
    IsCozeroSet (f ⁻¹' u) := by
  obtain ⟨g, rfl⟩ := hu
  exact ⟨g.comp ⟨f, hf⟩, by simp [support_comp_eq_preimage]⟩

lemma Continuous.isCozeroSet_support [T6Space Y] [Zero Y] {f : X → Y}
    (hf : Continuous f) : IsCozeroSet (support f) := by
  rw [support_eq_preimage]
  exact .preimage isOpen_compl_singleton.isCozeroSet hf

lemma isCozeroSet_empty : IsCozeroSet (∅ : Set X) := ⟨0, by simp⟩

lemma isCozeroSet_univ : IsCozeroSet (univ : Set X) := ⟨1, by simp⟩

lemma IsCozeroSet.inter (hu : IsCozeroSet u) {v : Set X} (hv : IsCozeroSet v) :
    IsCozeroSet (u ∩ v) := by
  obtain ⟨f, rfl⟩ := hu
  obtain ⟨g, rfl⟩ := hv
  exact ⟨f * g, by simp⟩

-- TODO: move
lemma Function.support_add_of_nonneg {α β : Type*} [AddZeroClass β] [PartialOrder β] [AddLeftMono β]
    [AddLeftStrictMono β] {f g : α → β} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    support (f + g) = support f ∪ support g := by
  refine le_antisymm (support_add _ _) ?_
  rintro x (hx | hx)
  · exact (add_pos_of_pos_of_nonneg ((hf x).lt_of_ne' hx) (hg x)).ne'
  · exact (add_pos_of_nonneg_of_pos (hf x) ((hg x).lt_of_ne' hx)).ne'

lemma IsCozeroSet.union (hu : IsCozeroSet u) {v : Set X} (hv : IsCozeroSet v) :
    IsCozeroSet (u ∪ v) := by
  obtain ⟨f, hf, rfl⟩ := hu.exists_nonneg
  obtain ⟨g, hg, rfl⟩ := hv.exists_nonneg
  exact ⟨f + g, support_add_of_nonneg hf hg⟩

-- TODO: move
lemma finsum_eq_zero_iff {α M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] {f : α → M} (hf : ∀ i, 0 ≤ f i) (hf' : HasFiniteSupport f) :
    ∑ᶠ i, f i = 0 ↔ ∀ i, f i = 0:= by
  refine ⟨fun h ↦ ?_, finsum_eq_zero_of_forall_eq_zero⟩
  contrapose! h
  obtain ⟨i, hi⟩ := h
  exact (finsum_pos hf ⟨i, (hf i).lt_of_ne' hi⟩ hf').ne'

/-- Unions of locally finite families of cozero sets are cozero sets. -/
lemma isCozeroSet_iUnion {ι : Type*} {u : ι → Set X}
    (hu : ∀ i, IsCozeroSet (u i)) (hu' : LocallyFinite u) : IsCozeroSet (⋃ i, u i) := by
  choose f hf hf' using fun i ↦ (hu i).exists_nonneg
  use ⟨_, continuous_finsum (fun i ↦ map_continuous (f i)) (by simpa [hf'])⟩
  ext x
  suffices h : ∑ᶠ i, f i x = 0 ↔ ∀ i, f i x = 0 by simpa [← hf'] using not_iff_not.2 h
  refine finsum_eq_zero_iff (fun i ↦ hf i x) ?_
  simpa [HasFiniteSupport, support, ← hf'] using hu'.point_finite x
