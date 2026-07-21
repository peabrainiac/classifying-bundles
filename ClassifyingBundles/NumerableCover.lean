/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.PartitionOfUnity

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
