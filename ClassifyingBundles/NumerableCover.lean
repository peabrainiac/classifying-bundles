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

/-- The pullback of any numerable cover along a continuous map is numerable. -/
lemma NumerableCover.preimage (hu : NumerableCover u) {Y : Type*} [TopologicalSpace Y] {f : Y → X}
    (hf : Continuous f) : NumerableCover fun i ↦ f ⁻¹' (u i) := by
  have ⟨g, hg⟩ := hu
  simpa using (hg.pullback ⟨f, hf⟩ (t := .univ) (h := by simp)).numerableCover

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

-- TODO: move
lemma Finset.ne_iff_of_card_eq {α : Type*} {s t : Finset α} (h : s.card = t.card) :
    s ≠ t ↔ (∃ x ∈ s, x ∉ t) ∧ ∃ x ∈ t, x ∉ s := by
  refine ⟨fun h' ↦ ?_, fun _ ↦ by grind⟩
  wlog _ : ∃ x ∈ s, x ∉ t generalizing s t with h''
  · grind [h'' h.symm h'.symm (by grind)]
  refine ⟨‹_›, ?_⟩
  suffices ¬t ⊂ s by grind
  exact fun h ↦ by grind [Finset.card_lt_card h]

/-- For every numerable open cover, there exists a countable locally finite
replacement with the property that every set in the replacement is a disjoint union of open subsets
of sets in the original cover.

This can be useful for example to prove that a fibre bundle can be trivialised on a countable
locally finite cover. -/
def _root_.NumerableCover.countable_locallyFinite_replacement {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Nonempty ι] {u : ι → Set X} (hu : NumerableCover u) :
    ∃ v : ℕ → Set X, LocallyFinite v ∧ NumerableCover v ∧ ∀ i : ℕ, ∃ u' : Set (Set X), ⋃₀ u' = v i ∧
      (Pairwise fun s t : u' ↦ Disjoint (s : Set X) t) ∧ ∀ s ∈ u', IsOpen s ∧ ∃ i, s ⊆ u i := by
  /- Since numerable covers can be refined by open covers, we can wlog assume that `u` is open. -/
  wlog hu' : ∀ i, IsOpen (u i) generalizing u with h
  · have ⟨v, hv, hv', hv''⟩ := h hu.interior (by simp)
    refine ⟨v, hv, hv', fun i ↦ (hv'' i).imp ?_⟩
    grind [interior_subset]
  /- If `ι` is finite we can obtain the cover by extend `u` to a countable cover by adding
  empty sets, so in the rest of the proof we can assume that `ι` is infinite. -/
  wlog! _ : Infinite ι generalizing ι with h
  · have ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    let v := (Fin.val ∘ e).extend u (fun _ ↦ ∅)
    have hv : ∀ i (hi : i < n), v i = u (e.symm ⟨i, hi⟩) := fun i hi ↦ by
      rw [show v i = v (Fin.val <| e <| e.symm ⟨i, hi⟩) by simp]
      unfold v
      rw [Function.comp_def, Function.Injective.extend_apply]
      exact Fin.val_injective.comp e.injective
    have hv' : ∀ i ≥ n, v i = ∅ := fun i hi ↦ by grind [Function.extend_apply']
    refine ⟨v, fun _ ↦ ?_, ?_, fun i ↦ ?_⟩
    · refine ⟨_, Filter.univ_mem, .subset (Set.finite_Iio n) fun i hi ↦ ?_⟩
      grind [Set.inter_univ, Set.not_nonempty_empty]
    · refine hu.mono' fun i ↦ ⟨(Fin.val ∘ e) i, ?_⟩
      simp only [v, (Fin.val_injective.comp e.injective).extend_apply, subset_rfl]
    · refine ⟨{v i}, by simp, by simp, ?_⟩
      rintro _ rfl
      by_cases! hi : n ≤ i
      · simp [hv', hi]
      · grind
  -- since `u` is numerable, we can pick a subordinate partition of unity `f`
  have ⟨f, hf⟩ := hu.exists_partitionOfUnity
  /- for each `s : Finset ι`, we consider the set `v s` of points at which every `f i` with `i`
  in `s` is greater than every `f j` with `j` outside `s`. -/
  let v (s : Finset ι) : Set X := {x | ∀ i ∈ s, ∀ j ∉ s, f i x > f j x}
  have hv (s : Finset ι) : ∀ x ∈ v s, ∀ i ∈ s, 0 < f i x := fun x hx i hi ↦
    (f.nonneg _ _).trans_lt (hx i hi _ s.exists_notMem.choose_spec)
  have hv' : LocallyFinite v := by
    refine fun x ↦ (f.eventually_finsupport_subset x).exists_mem.imp fun s ↦ .imp_right fun hs ↦ ?_
    refine .subset (f.fintsupport x).powerset.finite_toSet fun s' hs' ↦ ?_
    suffices s' ⊆ f.fintsupport x by simpa
    obtain ⟨x', hx', hx''⟩ := hs'
    exact fun i hi ↦  hs x' hx'' (by simpa using (hv s' x' hx' i hi).ne')
  -- each `v s` is a cozero set, i.e. the support of a continuous function
  have hv'' (s : { s : Finset ι // s.Nonempty }) : ∃ f : C(X, ℝ), Function.support ⇑f = v s := by
    use 0 ⊔ (s.1.inf' s.2 (fun i ↦ f i) - ⟨_, f.continuous_cbiSup sᶜ⟩)
    ext x
    suffices (∀ j ∈ s.1, ⨆ i ∈ (s.1 : Set ι)ᶜ, (f i) x < (f j) x) ↔
        ∀ i ∈ s.1, ∀ j ∉ s.1, (f j) x < (f i) x by simpa [v]
    refine forall₂_congr fun j hj ↦ ?_
    rw [f.cbiSup_lt_iff (show Set.Nonempty (s : Set ι)ᶜ from s.1.exists_notMem)]
    simp
  /- we obtain the countable cover by taking the disjoint union of `v s` over all sets `s` with
  `n + 1` elements as the `n`th set -/
  use fun n ↦ {x | ∃ s : Finset ι, s.card = n + 1 ∧ x ∈ v s}
  refine ⟨fun x ↦ ?_, ?_, fun n ↦ ?_⟩
  · refine (f.locallyFinite x).imp (fun s ↦ .imp_right fun hs ↦ ?_)
    rw [Set.finite_iff_bddAbove]
    use Set.ncard {i | ((fun i ↦ Function.support ⇑(f i)) i ∩ s).Nonempty}
    intro n ⟨x, ⟨t, ht, ht'⟩, hxs⟩
    exact n.lt_add_one.le.trans <| ((Set.ncard_coe_finset _).trans ht).symm.trans_le <|
      Set.ncard_le_ncard (ht := hs) fun i hi ↦
        ⟨x, ((f.nonneg _ _).trans_lt <| ht' i hi _ t.exists_notMem.choose_spec).ne', hxs⟩
  · refine .mono' (ι := {s : Finset ι // s.Nonempty})
      (u := fun s ↦ v s) ?_ ?_
    · refine .of_locallyFinite_cozero (hv'.comp_injective Subtype.val_injective) ?_ hv''
      refine Set.iUnion_eq_univ_iff.2 fun x ↦ ⟨⟨f.finsupport x, f.finsupport_nonempty⟩, ?_⟩
      simp only [PartitionOfUnity.mem_finsupport, Function.mem_support, v]
      have := fun i ↦ f.nonneg i x
      grind
    · intro s
      have ⟨n, hn⟩ := Nat.exists_eq_add_one.2 s.2.card_pos
      exact ⟨n, fun x hx ↦ ⟨s, hn, hx⟩⟩
  · use {v' | ∃ s : Finset ι, s.card = n + 1 ∧ v' = v s}
    refine ⟨by ext; simp [v], fun v v' hv ↦ ?_, ?_⟩
    · have ⟨s, hs⟩ := v.2; have ⟨s', hs'⟩ := v'.2
      grind [Finset.ne_iff_of_card_eq (hs.1.trans hs'.1.symm) |>.1 (by grind)]
    · rintro v ⟨s, hs, rfl⟩
      replace hs := s.card_pos.1 (by lia)
      refine ⟨?_, ?_⟩
      · have ⟨f, hf⟩ := hv'' ⟨s, hs⟩
        rw [← hf]
        exact (map_continuous f).isOpen_support
      · obtain ⟨i, hi⟩ := hs
        refine ⟨i, fun x hx ↦ hf i <| subset_closure ?_⟩
        exact ((f.nonneg _ _).trans_lt <| hx i hi _ s.exists_notMem.choose_spec).ne'
