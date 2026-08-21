/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.Homotopy.Contractible

/-! # Contractibility of sets
In this file we define a predicate `IsContractibleIn s t` for contractibility of sets within other
sets. This is less directly relevant to this repository and more something that would generally
be nice to have in mathlib.

TODO: upstream to mathlib, use in the definition of `LocallyContractibleSpace`
-/

open Set

variable {X : Type*} [TopologicalSpace X]

/-- The inclusion of a subset of a topological space, as a continuous map.
TODO: move to some more fitting place. -/
@[simps]
def ContinuousMap.subtypeVal {s : Set X} :
    C(s, X) where
  toFun := (↑)

@[simp]
lemma ContinuousMap.coe_subtypeVal {s : Set X} : ⇑(ContinuousMap.subtypeVal (s := s)) = (↑) := rfl

/-- TODO: find home, add missing API lemmas for `.subtypeVal` and `.inclusion`. -/
@[simp]
lemma ContinuousMap.subtypeVal_comp_inclusion {s t : Set X}
    (h : s ⊆ t) : ContinuousMap.subtypeVal.comp (.inclusion h) = .subtypeVal := by
  ext; simp [ContinuousMap.subtypeVal, ContinuousMap.inclusion]

@[simp]
lemma ContinuousMap.inclusion_eq_id {s : Set X} :
    ContinuousMap.inclusion (subset_refl s) = .id s := rfl

/-- TODO: move -/
@[simp]
lemma Homeomorph.Set.univ_toContinuousMap {X : Type*} [TopologicalSpace X] :
    toContinuousMap (Homeomorph.Set.univ X) = .subtypeVal :=
  rfl

/-- TODO: move -/
@[simps]
def ContinuousMap.codRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {s : Set Y} (hf : range f ⊆ s) : C(X, s) where
  toFun := s.codRestrict f (range_subset_iff.1 hf)

lemma ContinuousMap.Homotopy.range_left_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f f' : C(X, Y)} (F : f.Homotopy f') : range f ⊆ range F :=
  range_subset_iff.2 fun x ↦ ⟨(0, x), by simp⟩

lemma ContinuousMap.Homotopy.range_right_subset {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f f' : C(X, Y)} (F : f.Homotopy f') : range f' ⊆ range F :=
  range_subset_iff.2 fun x ↦ ⟨(1, x), by simp⟩

/-- TODO: move -/
def ContinuousMap.Homotopy.codRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f f' : C(X, Y)} (F : f.Homotopy f') {s : Set Y} (hf : range F ⊆ s) :
    (f.codRestrict (F.range_left_subset.trans hf)).Homotopy
      (f'.codRestrict (F.range_right_subset.trans hf)) where
  toContinuousMap := F.toContinuousMap.codRestrict hf
  map_zero_left _ := by ext; simp
  map_one_left _ := by ext; simp

/-- We say that `s` is contractible in `t` if the inclusion `s → X` is nullhomotopic within `t`,
that is, if there exists a homotopy from it to a constant map whose range is contained in `t`. -/
def IsContractibleIn (s t : Set X) : Prop :=
  ∃ x ∈ t, ∃ F : (ContinuousMap.subtypeVal (s := s)).Homotopy (.const _ x), range F ⊆ t

lemma IsContractibleIn.subset {s t : Set X} (h : IsContractibleIn s t) : s ⊆ t := by
  obtain ⟨x, hx, F, hF⟩ := h
  simpa using F.range_left_subset.trans hF

lemma IsContractibleIn.inclusion_nullhomotopic {s t : Set X} (h : IsContractibleIn s t) :
    (ContinuousMap.inclusion h.subset).Nullhomotopic := by
  obtain ⟨x, hx, F, hF⟩ := h
  exact ⟨⟨x, hx⟩, ⟨F.codRestrict hF⟩⟩

lemma IsContractibleIn.subtypeVal_nullhomotopic {s t : Set X} (h : IsContractibleIn s t) :
    (ContinuousMap.subtypeVal (s := s)).Nullhomotopic :=
  h.inclusion_nullhomotopic.comp_right .subtypeVal

lemma isContractibleIn_iff_inclusion {s t : Set X} (h : s ⊆ t) :
    IsContractibleIn s t ↔ (ContinuousMap.inclusion h).Nullhomotopic := by
  refine ⟨fun h ↦ h.inclusion_nullhomotopic, fun ⟨x, ⟨F⟩⟩ ↦ ?_⟩
  exact ⟨x, x.2, .comp (.refl .subtypeVal) F,
    (range_comp_subset_range F ContinuousMap.subtypeVal).trans (by simp)⟩

lemma IsContractibleIn.mono_left {s s' t : Set X} (h : IsContractibleIn s t) (h' : s' ⊆ s) :
    IsContractibleIn s' t := by
  refine (isContractibleIn_iff_inclusion (h'.trans h.subset)).2 ?_
  exact h.inclusion_nullhomotopic.comp_left (.inclusion h')

lemma IsContractibleIn.mono_right {s t t' : Set X} (h : IsContractibleIn s t) (h' : t ⊆ t') :
    IsContractibleIn s t' := by
  obtain ⟨x, hx, F, hF⟩ := h
  exact ⟨x, h' hx, F, hF.trans h'⟩

lemma IsContractibleIn.mono {s s' t t' : Set X}
    (h : IsContractibleIn s t) (h' : s' ⊆ s) (h'' : t ⊆ t') : IsContractibleIn s' t' :=
  (h.mono_left h').mono_right h''

lemma isContractibleIn_univ_iff {s : Set X} :
    IsContractibleIn s univ ↔ (ContinuousMap.subtypeVal (s := s)).Nullhomotopic := by
  simp [IsContractibleIn, ContinuousMap.Nullhomotopic, ContinuousMap.Homotopic]

lemma isContractibleIn_self_iff {s : Set X} : IsContractibleIn s s ↔ ContractibleSpace s := by
  simp [isContractibleIn_iff_inclusion, contractible_iff_id_nullhomotopic]

lemma isContractibleIn_univ_univ_iff :
    IsContractibleIn (univ : Set X) univ ↔ ContractibleSpace X := by
  simp [isContractibleIn_self_iff, (Homeomorph.Set.univ X).contractibleSpace_iff]

lemma isContractibleIn_univ [ContractibleSpace X] {s : Set X} : IsContractibleIn s univ :=
  (isContractibleIn_univ_univ_iff.2 ‹_›).mono_left (by simp)

lemma IsContractibleIn.nonempty {s t : Set X} (h : IsContractibleIn s t) : t.Nonempty := by
  obtain ⟨x, hx, _⟩ := h
  exact ⟨x, hx⟩
