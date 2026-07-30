/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.PartitionOfUnity
import ClassifyingBundles.IsCozeroSet
import ClassifyingBundles.RealInduction
import Mathlib.Topology.GDelta.MetrizableSpace

/-! # Numerable covers
In this file we define numerable covers of topological spaces.
-/

universe u

open Set

open scoped Topology unitInterval

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

/-- Every locally finite cover consisting of cozero sets is numerable. -/
lemma NumerableCover.of_locallyFinite_isCozeroSet (h : LocallyFinite u) (h' : ⋃ i, u i = univ)
    (h'' : ∀ i, IsCozeroSet (u i)) : NumerableCover u := by
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

/-- For a family of sets `u i`, the following are equivalent:
* `u` is a numerable cover
* `u` admits a subordinate partition of unity
* `u` admits a subordinate bump covering
* `u` admits a sobordinate positive partition
* `u` is refined by a locally finite cover consisting of cozero sets. -/
lemma NumerableCover.tfae :
    List.TFAE [NumerableCover u,
      ∃ f : PartitionOfUnity ι X, f.IsSubordinate u,
      ∃ f : BumpCovering ι X, f.IsSubordinate u,
      ∃ f : PositivePartition ι X, f.IsSubordinate u,
      ∃ v : ι → Set X, LocallyFinite v ∧ ⋃ i, v i = univ ∧ ∀ i, IsCozeroSet (v i) ∧ v i ⊆ u i] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 1 → 3 := fun hu ↦ hu.exists_bumpCovering
  tfae_have 3 → 1 := fun ⟨_, hf⟩ ↦ hf.numerableCover
  tfae_have 1 → 4 := fun hu ↦ hu.exists_positivePartition
  tfae_have 4 → 1 := fun ⟨_, hf⟩ ↦ hf.numerableCover
  tfae_have 1 → 5 := fun ⟨f, hf⟩ ↦ ⟨_, f.locallyFinite,
    eq_univ_of_forall fun x ↦ mem_iUnion.2 <| (f.exists_pos (mem_univ x)).imp fun i hi ↦ hi.ne',
    fun i ↦ ⟨(map_continuous (f i)).isCozeroSet_support, subset_closure.trans (hf i)⟩⟩
  tfae_have 5 → 1 := fun ⟨v, hv, hv', hv''⟩ ↦
    .mono (.of_locallyFinite_isCozeroSet hv hv' fun i ↦ (hv'' i).1) (fun i ↦ (hv'' i).2)
  tfae_finish

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
def NumerableCover.countable_locallyFinite_replacement
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
    · refine .of_locallyFinite_isCozeroSet (hv'.comp_injective Subtype.val_injective) ?_ hv''
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

--TODO: move
lemma Set.Finite.sigma {ι : Type u_1} {α : ι → Type u_2} {s : Set ι} (hs : s.Finite)
    {t : (i : ι) → Set (α i)} (ht : ∀ i ∈ s, (t i).Finite) :
    (s.sigma t).Finite := by
  classical
  convert (hs.toFinset.sigma (fun i ↦ if h : i ∈ s then (ht i h).toFinset else .empty)).finite_toSet
  ext x
  by_cases h : x.1 ∈ s <;> simp [h]

/-- A variant of `NumerableCover.of_locallyFinite_isCozeroSet`: to prove that `u : ι → Set X` is a
numerable cover, it suffices to give instead of a single locally finite cover by cozero sets
refining `u` a countable family of locally finite families of cozero sets refining `u` that only
jointly cover `X`. -/
lemma NumerableCover.of_locallyFinite_isCozeroSet_refinements
    {κ : Type*} [Countable κ] {κ' : κ → Type u} {v : (k : κ) → κ' k → Set X}
    (hv : ∀ k, LocallyFinite (v k)) (hv' : ⋃ k, ⋃ k', v k k' = univ)
    (hv'' : ∀ k k', IsCozeroSet (v k k')) (hv''' : ∀ k k', ∃ i, v k k' ⊆ u i) :
    NumerableCover u := by
  -- since the index type `κ` is countable, we can wlog replace it with `ℕ`
  wlog! _ : Nonempty κ
  · have := Set.univ_eq_empty_iff.1 (.symm (by simpa using hv'))
    exact .of_paracompactSpace fun x ↦ IsEmpty.elim ‹_› x
  revert κ
  suffices h : ∀ {κ : ℕ → Type u} {v : (n : ℕ) → κ n → Set X}, (∀ (n : ℕ), LocallyFinite (v n)) →
      ⋃ n, ⋃ k, v n k = univ → (∀ (n : ℕ) (k : κ n), IsCozeroSet (v n k)) →
        (∀ (n : ℕ) (k : κ n), ∃ i, v n k ⊆ u i) → NumerableCover u by
    intro κ _ κ' v hv hv' hv'' hv''' _
    have ⟨f, hf⟩ := exists_surjective_nat κ
    refine h (fun n ↦ hv (f n)) ((hf.iUnion_comp _).trans hv') ?_ ?_
    <;> rwa [hf.forall] at hv'' hv'''
  intro κ v hv hv' hv'' hv'''
  /- for each `v n k`, choose a function `f n k` with values in the unit interval whose support
  is `v n k` -/
  replace hv'' := fun k k' ↦ (hv'' k k').exists_nonneg_le_one
  choose f hf hf' hf'' using hv''
  replace hv' x : ∃ n k, 0 < f n k x := by
    have ⟨n, k, h⟩ := iUnion₂_eq_univ_iff.1 hv' x
    exact ⟨n, k, (hf n k x).lt_of_ne' <| (hf'' n k).symm.subset h⟩
  -- let `F n` be the sum of all `f m k` for `m < n`
  let F n x := ∑ m < n, ∑ᶠ k, f m k x
  have hF n : Continuous (F n) := by
    refine continuous_finsetSum _ fun m _ ↦ continuous_finsum (fun _ ↦ map_continuous _) ?_
    simp [hf'', hv]
  have hF' n m (h : n ≤ m) : F n ≤ F m :=
    fun x ↦ Finset.sum_le_sum_of_subset_of_nonneg (by gcongr) fun _ _ _ ↦
      finsum_nonneg fun _ ↦ hf _ _ x
  have hF'' n : 0 ≤ F n := fun x ↦ by simpa [F] using hF' 0 n zero_le x
  -- let `g n k` be `f n k - n * F n`, or `0` if that is negative
  let g n k : C(X, ℝ) := 0 ⊔ (f n k - n * ⟨F n, hF n⟩)
  have hg n k : Function.support (g n k) ⊆ v n k := fun x hx ↦ by
    replace hx : 0 < (f n k) x :=
      (mul_nonneg (n.cast_nonneg) (hF'' n x)).trans_lt (by simpa [g] using hx)
    simpa [← hf''] using hx.ne'
  /- it now suffices to prove that the supports of the `g n k` form a locally finite cover
  refining `u` -/
  refine .mono' (u := Sigma.uncurry fun n k ↦ Function.support (g n k)) ?_
    fun k ↦ (hv''' k.1 k.2).imp fun i hi ↦ (hg k.1 k.2).trans hi
  refine .of_locallyFinite_isCozeroSet ?_ ?_ ?_
  · -- for each `x` there exists an `n` such that `1 ≤ n * F n` on a neighbourhood `u` of `x`
    intro x
    have ⟨n, hn⟩ : ∃ n, 1 < n * F n x := by
      suffices h : ∃ n, 0 < F n x by
        obtain ⟨n, hn⟩ := h
        use n ⊔ ⌈1 / F n x⌉₊ + 1
        push_cast
        grw [← hF' n (n ⊔ ⌈1 / F n x⌉₊ + 1) (by grind) x, ← Nat.le_ceil, ← Std.right_le_max]
        grind
      have ⟨n, k, h⟩ := hv' x
      refine ⟨n + 1, ?_⟩
      simp only [F, Nat.Iio_eq_range, Finset.sum_range_succ]
      refine add_pos_of_nonneg_of_pos (by simpa [F, Nat.Iio_eq_range] using hF'' n x) <|
        finsum_pos (fun _ ↦ hf n _ x) ⟨k, h⟩ ?_
      have h := (hv n).point_finite x
      simp only [← hf''] at h
      exact h
    replace hn := Filter.eventually_iff_exists_mem.1 <|
      continuousAt_const.eventually_lt (f := 1) (g := fun x ↦ n * F n x) (by fun_prop) hn
    obtain ⟨u, hu⟩ := hn
    -- for each `n`, let `u' n` be a neighbourhood of `x` on which `v n` is finite
    replace hv := fun n ↦ hv n x
    choose u' hu' using hv
    /- on the intersection of `u` and all `u' m` for `m ≤ n`, the cover given by the supports of
    the `g n k` is now also locally finite, because all `g m k` vanish on `u` for all `m > n`  -/
    refine ⟨u ∩ ⋂ m ≤ n, u' m, ?_, ?_⟩
    · exact Filter.inter_mem hu.1 <| (Filter.biInter_mem (finite_Iic _)).2 fun _ _ ↦ (hu' _).1
    · refine ((finite_Iic n).sigma fun n _ ↦ (hu' n).2).subset fun i hi ↦ ?_
      simp only [Sigma.uncurry, mem_sigma_iff, mem_Iic, mem_setOf_eq] at hi ⊢
      obtain ⟨x, hx⟩ := hi
      suffices hi : i.fst ≤ n from ⟨hi, x, hg _ _ hx.1, mem_iInter₂.1 hx.2.2 _ hi⟩
      have hx' := hu.2 x hx.2.1
      replace hx := hx.1
      contrapose! hx with hi
      simpa [g] using (hf' _ _ _).trans <| hx'.le.trans <| mul_le_mul (Nat.cast_le.2 hi.le)
        (hF' _ _ hi.le x) (hF'' n x) (by simp)
  · /- the supports of the `g n k` cover `X` because for each `x`, there exists an `n` that
    is minimal with the property that `0 < f n k x` for some `k`, and the corresponding `g n k`
    is then also positive on `x` -/
    refine iUnion_eq_univ_iff.2 fun x ↦ ?_
    have ⟨n, hn⟩ := WellFoundedLT.exists_minimal inferInstance {n | ∃ k, 0 < f n k x} (hv' x)
    suffices h : F n x = 0 by
      have ⟨k, hk⟩ := hn.prop
      exact ⟨⟨n, k⟩, by simp [Sigma.uncurry, g, h, hk]⟩
    refine Finset.sum_eq_zero fun m hm ↦ finsum_eq_zero_of_forall_eq_zero fun k ↦
      le_antisymm ?_ <| (ContinuousMap.le_def.1 (hf m k) x)
    grind [hn.not_prop_of_lt (Finset.mem_Iio.1 hm)]
  · exact fun k ↦ (map_continuous (g k.1 k.2)).isCozeroSet_support

attribute [local gcongr] Set.Finite.subset in
/-- For every numerable cover `u` of `X × I`, there exists a numerable cover `v` of `X` such that
each `v i ×ˢ univ` decomposes into sets of the form `v i ×ˢ w` contained in some `u i'`.

In the literature, this is occasionally called the stacking lemma or existence of stacked covers.

TODO: generalize this from the unit interval to arbitrary compact spaces. -/
lemma NumerableCover.exists_of_prod_unitInterval {ι : Type u} {u : ι → Set (X × I)}
    (hu : NumerableCover u) :
    ∃ ι' : Type u, ∃ v : ι' → Set X, NumerableCover v ∧
      ∀ i', ∀ x ∈ v i', ∀ t, ∃ w ∈ 𝓝 t, ∃ i, v i' ×ˢ w ⊆ u i := by
  -- since `u` is numerable, we can replace it with a locally finite cover by cozero sets
  wlog hu' : LocallyFinite u ∧ ∀ i, IsCozeroSet (u i) generalizing u with h
  · have ⟨v, hv, hv', hv''⟩ := (((NumerableCover.tfae (u := u)).out 0 4).1 hu:)
    grw [← fun i ↦ (hv'' i).2]
    exact h (.of_locallyFinite_isCozeroSet hv hv' (fun i ↦ (hv'' i).1)) ⟨hv, fun i ↦ (hv'' i).1⟩
  /- let `w n` for each `n` be a cover of `I` by `n + 1` overlapping closed intervals of size
  `2 / (n + 2)`. Proving that each point has a neighbourhood in one of these points unfortunately
  requires an ugly case distinction. -/
  let w n (k : Fin (n + 1)) : Set I :=
    Icc ⟨k / (n + 2), by apply unitInterval.div_mem <;> grind [(Nat.cast_le (α := ℝ)).2 k.2]⟩
    ⟨(k + 2) / (n + 2), by
      apply unitInterval.div_mem <;> grind [(Nat.cast_le (α := ℝ)).2 <| Nat.add_one_le_of_lt k.2]⟩
  have hw n t : ∃ k, w n k ∈ 𝓝 t := by
    by_cases! ht : t = 0
    · use 0
      simp only [ht, show (0 : I) = ⊥ from rfl, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        CharP.cast_eq_zero, zero_div, Icc.mk_zero, zero_add, Icc_bot, w]
      apply Iic_mem_nhds
      simp [← Subtype.coe_lt_coe]
      grind
    · by_cases! ht' : (n + 1 : ℝ) < t * (n + 2)
      · use ⟨n, by simp⟩
        simp only [w]
        rw! [div_self (by positivity), Icc.mk_one, show (1 : I) = ⊤ from rfl, Icc_top]
        apply Ici_mem_nhds
        rw [← Subtype.coe_lt_coe, Subtype.coe_mk, div_lt_iff₀ (by positivity)]
        grind
      · have ht'' : 1 ≤ ⌈t * (n + 2 : ℝ)⌉₊ := Nat.one_le_ceil_iff.2 <| by
          positivity [unitInterval.coe_pos.2 <| ht.lt_of_le' t.2.1]
        refine ⟨⟨⌈t * (n + 2 : ℝ) - 1⌉₊, by simpa⟩, Icc_mem_nhds ?_ ?_⟩
        · simp only [Nat.ceil_sub_one, ← Subtype.coe_lt_coe, Nat.cast_sub ht'', Nat.cast_one]
          rw [div_lt_iff₀ (by positivity), sub_lt_iff_lt_add]
          exact (Nat.ceil_lt_add_one (by positivity [t.2.1]))
        · grw [← Subtype.coe_lt_coe, lt_div_iff₀ (by positivity), ← Nat.le_ceil]
          grind
  /- For each `n : ℕ` and `i : Fin (n + 1) → ι`, let `v n i` be the largest set such that
  `v n i ×ˢ w n k` is contained in `u i` for all `k`. We now show that `Sigma.uncurry v` is the
  desired numerable cover, by proving that each `v n` is a locally finite family of cozero sets and
  that these families jointly cover `X`. -/
  let v n (i : Fin (n + 1) → ι) : Set X := ⋂ k : Fin (n + 1), {x | ∀ t ∈ w n k, (x, t) ∈ u (i k)}
  refine ⟨_, Sigma.uncurry v, ?_, ?_⟩
  · refine .of_locallyFinite_isCozeroSet_refinements (v := v) ?_ ?_ ?_ ?_
    · /- to prove that each `v n` is locally finite, it suffices to show that each `x` has a
      neighbourhood `u'` for which `u' ×ˢ univ` intersects only finitely many `u i`. -/
      intro n x
      suffices h : ∃ u' ∈ 𝓝 x, Set.Finite {i | (u i ∩ (u' ×ˢ univ)).Nonempty} by
        refine h.imp fun u'' ↦ .imp_right fun hu'' ↦ ?_
        refine .subset (.pi fun i : Fin (n + 1) ↦ hu'') fun i ⟨x, hx, hx'⟩ k _ ↦ ?_
        simp only [mem_iInter, v] at hx ⊢
        refine ⟨_, hx k _ (left_mem_Icc.2 ?_), by grind⟩
        simp only [← Subtype.coe_le_coe]; gcongr; grind
      -- this can be proven from local finiteness of `u` by induction
      refine unitInterval.induction' (fun t ↦ ?_) ?_
        (motive := fun w ↦ ∃ u' ∈ 𝓝 x, {i | (u i ∩ u' ×ˢ w).Nonempty}.Finite)
      · have ⟨v', hv'⟩ := hu'.1 (x, t)
        obtain ⟨u', hu', w, hw⟩ := mem_nhds_prod_iff.1 hv'.1
        exact ⟨w, hw.1, u', hu', by grw [hw.2]; exact hv'.2⟩
      · intro t t' ht v₁ hv₁ ⟨u₁, hu₁, hu₁'⟩ v₂ hv₂ ⟨u₂, hu₂, hu₂'⟩
        refine ⟨v₁ ∪ v₂, ?_, ?_⟩
        · rw [← Iic_union_Icc_eq_Iic ht.le]
          exact union_mem_nhdsSet hv₁ hv₂
        · simp only [prod_union, inter_union_distrib_left, union_nonempty, setOf_or, finite_union]
          refine ⟨u₁ ∩ u₂, Filter.inter_mem hu₁ hu₂, ?_, ?_⟩
          · grw [u₁.inter_subset_left]; exact hu₁'
          · grw [u₁.inter_subset_right]; exact hu₂'
    · /- to show that eahc `x` is contained in some `v n i`, it suffices to show that for each `x`
      there exists some `n` such that each `w n k` is contained in the preimage of some `u i`
      under `fun t ↦ (x, t)`. -/
      refine iUnion_eq_univ_iff.2 fun x ↦ ?_
      suffices h : ∃ n, ∀ k, ∃ i, w n k ⊆ (fun t ↦ (x, t)) ⁻¹' u i by
        obtain ⟨n, hn⟩ := h
        choose i hi using hn
        exact ⟨n, mem_iUnion_of_mem i <| mem_iInter.2 <| by grind⟩
      -- we can do this by applying Lebesgue's number lemma to `fun i ↦ (fun t ↦ (x, t)) ⁻¹' u i`.
      have ⟨δ, hδ, hδ'⟩ := lebesgue_number_lemma_of_metric (c := fun i ↦ (fun t ↦ (x, t)) ⁻¹' u i)
        isCompact_univ (fun i ↦ (hu'.2 i).isOpen.preimage <| .prodMk_right x)
        (by simp [← preimage_iUnion, hu.cover])
      refine ⟨⌈δ⁻¹⌉₊, fun k ↦ ?_⟩
      suffices h : ∃ t, w _ k ⊆ Metric.ball t δ by
        obtain ⟨t, ht⟩ := h; grw [ht]; exact hδ' t trivial
      simp_rw [← image_subset_image_iff Subtype.coe_injective, w, Subtype.image_ball,
        subset_inter_iff, setOf_mem_eq, Subtype.coe_image_subset, and_true,
        image_subtype_val_Icc, Real.Icc_eq_closedBall]
      refine ⟨⟨_, by positivity, ?_⟩, Metric.closedBall_subset_ball ?_⟩
      · grw [← add_div, k.2]
        grind
      · grw [← sub_div, add_sub_cancel_left, div_div_cancel_left' (by simp), ← Nat.le_ceil]
        grind [inv_lt_of_inv_lt₀]
    · /- each `v n i` is a cozero set because it is an intersection of coimages of cozero sets
      along a proper open map. -/
      refine fun n i ↦ isCozeroSet_iInter fun k ↦ ?_
      have : CompactSpace (w n k) := compactSpace_Icc _ _
      convert (hu'.2 (i k)).preimage (f := Prod.map id ((↑) : w n k → _)) (by fun_prop)
        |>.coimage isProperMap_fst_of_compactSpace isOpenMap_fst using 1
      ext x; simp
    · exact fun n i ↦ ⟨⟨n, i⟩, by simp [Sigma.uncurry]⟩
  · -- `Sigma.uncurry v` satisfies the other desired property by construction.
    intro ⟨n, i⟩ x hx t
    simp only [Sigma.uncurry] at hx
    obtain ⟨k, hk⟩ := hw n t
    refine ⟨_, hk, i k, ?_⟩
    simp only [v, Sigma.uncurry]
    grw [iInter_subset _ k]
    grind
