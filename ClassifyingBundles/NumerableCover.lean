/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.PartitionOfUnity
import Mathlib.Topology.ContinuousMap.Lattice

/-! # Numerable covers
In this file we define numerable covers of topological spaces.
-/

open Set

open scoped Topology

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {u : ι → Set X}

/-- A numerable cover is a cover that admits a subordinate partition of unity. -/
def NumerableCover (u : ι → Set X) : Prop := ∃ f : PartitionOfUnity ι X, f.IsSubordinate u

/-- A numerable cover is indeed a cover. -/
lemma NumerableCover.cover (hu : NumerableCover u) : ⋃ i, u i = .univ := by
  obtain ⟨f, hf⟩ := hu
  refine eq_univ_of_forall fun x ↦ ?_
  have ⟨i, hi⟩ := f.exists_pos (mem_univ x)
  exact mem_iUnion_of_mem i <| hf.mem_of_pos hi

lemma NumerableCover.exists_partitionOfUnity (hu : NumerableCover u) :
    ∃ f : PartitionOfUnity ι X, f.IsSubordinate u :=
  hu

lemma PartitionOfUnity.IsSubordinate.numerableCover {f : PartitionOfUnity ι X}
    (hf : f.IsSubordinate u) : NumerableCover u :=
  ⟨f, hf⟩

/-- Every covering with a subordinate bump covering is numerable. -/
lemma BumpCovering.IsSubordinate.numerableCover {f : BumpCovering ι X} (hf : f.IsSubordinate u) :
    NumerableCover u :=
  hf.toPartitionOfUnity.numerableCover

lemma NumerableCover.exists_bumpCovering (hu : NumerableCover u) :
    ∃ f : BumpCovering ι X, f.IsSubordinate u := by
  obtain ⟨f, hf⟩ := hu
  exact ⟨_, hf.toBumpCovering⟩

/-- Every covering with a subordinate positive partition is numerable. -/
lemma PositivePartition.IsSubordinate.numerableCover {f : PositivePartition ι X}
  (hf : f.IsSubordinate u) : NumerableCover u := hf.toPartitionOfUnity.numerableCover

lemma NumerableCover.exists_positivePartition (hu : NumerableCover u) :
    ∃ f : PositivePartition ι X, f.IsSubordinate u := by
  obtain ⟨f, hf⟩ := hu
  exact ⟨_, hf.toPositivePartition⟩

@[simp]
lemma Function.support_abs {α β : Type*} [AddGroup α] [LinearOrder α] [AddLeftMono α]
    [AddRightMono α] {f : β → α} : support |f| = support f := by
  ext; simp

/-- Every locally finite cover consisting of cozero sets is numerable. -/
lemma NumerableCover.of_locallyFinite_cozero (h : LocallyFinite u) (h' : ⋃ i, u i = univ)
    (h'' : ∀ i, ∃ f : C(X, ℝ), Function.support f = u i) : NumerableCover u := by
  choose f hf using h''
  suffices h : ∃ f : PositivePartition ι X, ∀ i, Function.support (f i) = u i by
    obtain ⟨f', hf'⟩ := h
    have hf'' : f'.toPartitionOfUnity.toBumpCovering.shrink.IsSubordinate u := fun i ↦ by
      refine (BumpCovering.tsupport_shrink_subset _).trans_eq ?_
      simp [hf']
    exact hf''.numerableCover
  refine ⟨⟨fun i ↦ |f i|, by simp [hf, h], fun i ↦ by simp, fun x _ ↦ ?_⟩, by simp [hf]⟩
  refine (iUnion_eq_univ_iff.1 h' x).imp fun i ↦ ?_
  simp [← hf]

lemma NumerableCover.tfae :
    List.TFAE [NumerableCover u,
      ∃ f : PartitionOfUnity ι X, f.IsSubordinate u,
      ∃ f : BumpCovering ι X, f.IsSubordinate u,
      ∃ f : PositivePartition ι X, f.IsSubordinate u] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 1 → 3 := fun hu ↦ hu.exists_bumpCovering
  tfae_have 3 → 1 := fun ⟨_, hf⟩ ↦ hf.numerableCover
  tfae_have 1 → 4 := fun hu ↦ hu.exists_positivePartition
  tfae_have 4 → 1 := fun ⟨_, hf⟩ ↦ hf.numerableCover
  tfae_finish

/-- Any cover that is refined by a numerable cover is numerable. -/
lemma NumerableCover.mono (hu : NumerableCover u) {u' : ι → Set X} (h : ∀ i, u i ⊆ u' i) :
    NumerableCover u' :=
  hu.imp fun _ ↦ (.mono · h)

/-- A version of `NumerableCover.mono` for covers over different index types. -/
lemma NumerableCover.mono' (hu : NumerableCover u) {ι' : Type*} {u' : ι' → Set X}
    (h : ∀ i, ∃ i', u i ⊆ u' i') : NumerableCover u' := by
  obtain ⟨f, hf⟩ := hu
  choose g hg using h
  exact ⟨f.map g, hf.map hg⟩

lemma NumerableCover.of_paracompactSpace [ParacompactSpace X] [T2Space X]
    (hu : ∀ x, ∃ i, u i ∈ 𝓝 x) : NumerableCover u := by
  have ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun i ↦ interior (u i))
    (fun i ↦ isOpen_interior) (forall_imp (fun x ⟨i, hi⟩ _ ↦ mem_iUnion_of_mem i <|
      mem_interior_iff_mem_nhds.2 hi) hu)
  exact (hf.mono fun _ ↦ interior_subset).numerableCover

/-- Every numerable cover has a locally finite, open, also numerable refinement. -/
lemma NumerableCover.locallyFinite_open_refinement (hu : NumerableCover u) :
    ∃ u' : ι → Set X, LocallyFinite u' ∧ NumerableCover u' ∧ ∀ i, IsOpen (u' i) ∧ u' i ⊆ u i := by
  obtain ⟨f, hf⟩ := hu.exists_bumpCovering
  exact ⟨_, f.locallyFinite, f.isSubordinate_shrink.numerableCover,
    fun i ↦ ⟨(map_continuous (f i)).isOpen_support, .trans subset_closure (hf i)⟩⟩

/-- Every numerable cover has a locally finite, closed, also numerable refinement. -/
lemma NumerableCover.locallyFinite_closed_refinement (hu : NumerableCover u) :
    ∃ u' : ι → Set X, LocallyFinite u' ∧ NumerableCover u' ∧ ∀ i, IsClosed (u' i) ∧ u' i ⊆ u i := by
  obtain ⟨f, hf⟩ := hu.exists_bumpCovering
  exact ⟨_, f.locallyFinite_tsupport, f.isSubordinate_tsupport.numerableCover,
    fun i ↦ ⟨isClosed_tsupport _, hf i⟩⟩

/-- If the sets `u i` form a numerable cover, the sets `interior (u i)` do as well. -/
protected lemma NumerableCover.interior (hu : NumerableCover u) :
    NumerableCover fun i ↦ interior (u i) := by
  have ⟨u', hu', hu'', hu'''⟩ := hu.locallyFinite_open_refinement
  exact hu''.mono fun i ↦ (hu''' i).1.subset_interior_iff.2 (hu''' i).2
