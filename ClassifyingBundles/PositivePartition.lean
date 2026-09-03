/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.PartitionOfUnity

/-! # Positive partitions
In this file, we define "positive partitions" of a space `X` as families of functions `f i : X → ℝ`
with the property that all functions `f i` are nonnegative, that the family
`fun i ↦ Function.support (f i)` is locally finite, and that for every `x` there exists at least
one `i` with `0 < f i x`. These are essentially partitions of unity, just without the requirement
that at all the functions sum to `1`; every partition of unity is a positive partition, and every
positive partition can be turned into a partition of unity by dividing all functions by their sum.

The benefit of positive partitions is that they are easier to construct, and that generalise both
partitions of unity and bump coverings, so that parts of their API could be deduplicated by
generalising it to positive partitions in the future. Since we can't modify definitions from
mathlib in this fork though, we however don't let partitions of unity and bump coverings extend
positive partitions yet.

The term "positive partition" is borrowed from https://arxiv.org/abs/2203.03120, though we
require positive partitions to be locally finite while that paper does not.

We also defined "generalised positive partitions" as a common generalisation of positive partitions
and generalised partitions of unity as defined in Tom Dieck's *algebraic topology*.
-/

open Set Function Filter

open scoped Topology

/-- A generalised positive partition is a positive partition that is only required to be
point-finite instead of locally finite, while still enforcing continuity of the sum.
In other words, a positive partition is a family of continuous nonnegative functions such that
at each point at least one and at most finitely many functions are positive, and the sum of all
functions (well-defined and positive by the previous assumption) is also continuous.

The main use case for this is to provide an even easier way to prove that covers are numerable:
every cover with a subordinate generalised positive partition is numerable, and hence also admits
subordinate partitions of unity. -/
structure GeneralizedPositivePartition (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collection of continuous functions underlying this partition of unity -/
  toFun : ι → C(X, ℝ)
  /-- At each point, at most finitely many functions are nonzero -/
  point_finite' x : {i | x ∈ support (toFun i)}.Finite
  /-- The sum of all functions is continuous -/
  continuous_finsum' : Continuous fun x ↦ ∑ᶠ i, toFun i x
  /-- The functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- At least one function is positive at every point in `s` -/
  exists_pos' : ∀ x ∈ s, ∃ i, 0 < toFun i x

/-- A continuous positive partition on a set `s : Set X` is a collection of continuous functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* at least one `f i x` is positive for each `x ∈ s`.

Every partition of unity is a positive partition, and every (global) positive partition can be
turned into a partition of unity by dividing all functions by their sum. The existence of
positive partitions and partitions of unity subordinate to any given cover is hence equivalent;
the utility of positive partitions is that they are easier to construct, and hence
allow you to obtain partitions of unity just by giving a positive partition.
-/
@[ext]
structure PositivePartition (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) extends
    GeneralizedPositivePartition ι X s where
  /-- The supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  point_finite' x := locallyFinite'.point_finite x
  continuous_finsum' := continuous_finsum (fun i ↦ map_continuous (toFun i)) locallyFinite'

namespace GeneralizedPositivePartition

variable {X ι : Type*} [TopologicalSpace X] {s : Set X} (f : GeneralizedPositivePartition ι X s)
    {u : ι → Set X}

instance : FunLike (GeneralizedPositivePartition ι X s) ι C(X, ℝ) where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp]
lemma coe_mk (toFun : ι → C(X, ℝ)) (point_finite' : ∀ x, {i | x ∈ support (toFun i)}.Finite)
    (continuous_finsum' : Continuous fun x ↦ ∑ᶠ i, (toFun i) x)
    (nonneg' : 0 ≤ toFun) (exists_pos' : ∀ x ∈ s, ∃ i, 0 < toFun i x) {i : ι} :
  GeneralizedPositivePartition.mk toFun point_finite' continuous_finsum' nonneg' exists_pos' i =
    toFun i := rfl

lemma point_finite (x : X) : {i | x ∈ support (f i)}.Finite := f.point_finite' x

@[fun_prop]
lemma continuous_sum : Continuous fun x ↦ ∑ᶠ i, f i x := f.continuous_finsum'

lemma nonneg (i : ι) (x : X) : 0 ≤ f i x := f.nonneg' i x

lemma exists_pos {x : X} (hx : x ∈ s) : ∃ i, 0 < f i x := f.exists_pos' _ hx

lemma sum_pos {x : X} (hx : x ∈ s) : 0 < ∑ᶠ i, f i x :=
  finsum_pos (f.nonneg · x) (f.exists_pos hx) (f.point_finite x)

/-- The set of indices `i` for which `f i` is nonzero at `x`, as a `Finset`.

Note that an analogous `fintsupport` can not be defined in this generality, because the number of
indices `i` for which `x` is contained in `tsupport (f i)` is still potentially infinite. -/
noncomputable def finsupport (x : X) : Finset ι := (f.point_finite x).toFinset

@[simp]
lemma mem_finsupport {x : X} {i : ι} : i ∈ f.finsupport x ↔ x ∈ support (f i) := by
  simp [finsupport]

@[simp]
lemma coe_finsupport {x : X} : (f.finsupport x : Set ι) = support fun i ↦ f i x := by
  ext; simp

lemma finsupport_nonempty {x : X} (hx : x ∈ s := by trivial) : (f.finsupport x).Nonempty :=
  (f.exists_pos hx).imp fun _ h ↦ by simpa using h.ne'

lemma _root_.finsum_mono_set {α M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    {f : α → M} (hf : HasFiniteSupport f) (h' : ∀ i, 0 ≤ f i) {s t : Set α} (h'' : s ⊆ t) :
    ∑ᶠ i ∈ s, f i ≤ ∑ᶠ i ∈ t, f i := by
  rw [finsum_mem_eq_sum _ (hf.inter_of_right _), finsum_mem_eq_sum _ (hf.inter_of_right _)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by gcongr) (fun _ _ _ ↦ h' _)

lemma _root_.le_finsum_of_mem {α M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {f : α → M} (hf : HasFiniteSupport f) (hf' : ∀ i, 0 ≤ f i) {s : Set α}
    {i : α} (hi : i ∈ s) : f i ≤ ∑ᶠ i ∈ s, f i := by
  simpa using finsum_mono_set hf hf' (singleton_subset_iff.2 hi)

lemma continuous_sum' {s : Set ι} : Continuous fun x ↦ ∑ᶠ i ∈ s, f i x := by
  classical
  refine continuous_iff_continuousAt.2 fun x ↦ .congr ?_ (.of_forall fun x' ↦ ?_)
    (f := fun x' ↦ ∑ᶠ i ∈ s \ f.finsupport x, f i x' + ∑ i ∈ f.finsupport x with i ∈ s, f i x')
  · refine .add ?_ (by fun_prop)
    rw [ContinuousAt, show ∑ᶠ i ∈ s \ f.finsupport x, f i x = 0 from
      finsum_mem_of_eqOn_zero <| by intro; simp]
    refine squeeze_zero (g := fun x' ↦ ∑ᶠ i ∈ Set.univ \ f.finsupport x, f i x')
      (by grind [finsum_nonneg, f.nonneg])
      (fun x ↦ finsum_mono_set (f.point_finite x) (fun i ↦ f.nonneg i x) (by simp)) ?_
    rw [← show ∑ᶠ (i : ι) (_ : i ∈ univ \ ↑(f.finsupport x)), (f i) x = 0 from
      finsum_mem_of_eqOn_zero <| by intro; simp]
    refine ContinuousAt.congr (f := fun x' ↦ ∑ᶠ i, f i x' - ∑ i ∈ f.finsupport x, f i x')
      (by fun_prop) <| .of_forall fun x' ↦ ?_
    simp only [← finsum_mem_finset_eq_sum, ← Finset.mem_coe, sub_eq_iff_eq_add]
    rw [← finsum_mem_union' (by grind) (.inter_of_right (by simp [← coe_finsupport]) _)
      (.inter_of_right (by simp [← coe_finsupport]) _)]
    simp
  · simp only [← finsum_mem_finset_eq_sum, ← Finset.mem_coe]
    rw [← finsum_mem_union' (by grind) (.inter_of_right (by simp [← coe_finsupport]) _)
      (.inter_of_left (Finset.finite_toSet _) _)]
    simp [show {i ∈ f.finsupport x | i ∈ s} = s ∩ f.finsupport x by grind]

lemma finsum_compl_finsupport_tendsto {x : X} :
    Tendsto (fun x' ↦ ∑ᶠ i ∈ (f.finsupport x : Set ι)ᶜ, f i x') (𝓝 x) (𝓝 0) := by
  rw [← show ∑ᶠ i ∈ (f.finsupport x : Set ι)ᶜ, f i x = 0 from
    finsum_mem_of_eqOn_zero fun i hi ↦ by simpa using hi]
  exact f.continuous_sum'.continuousAt

lemma _root_.Function.HasFiniteSupport.finite_range {α β : Type*} [Zero β] {f : α → β}
    (hf : HasFiniteSupport f) : (range f).Finite :=
  Finsupp.finite_range ⟨hf.toFinset, f, by simp⟩

lemma le_cbiSup_of_mem {s : Set ι} {i : ι} (hi : i ∈ s) {x : X} : f i x ≤ ⨆ i ∈ s, f i x := by
  refine le_ciSup₂ (f := fun i' (hi : i' ∈ s) ↦ f i' x) ?_ i hi
  refine (HasFiniteSupport.finite_range (f.point_finite x)).bddAbove.mono ?_
  grw [range_const_subset]
  simp

lemma cbiSup_nonneg {x : X} {s : Set ι} : 0 ≤ ⨆ i ∈ s, f i x :=
  (eq_empty_or_nonempty s).rec (fun h ↦ by simp [h]) fun ⟨i, hi⟩ ↦
    (f.nonneg i x).trans <| f.le_cbiSup_of_mem hi

lemma ciSup_pos {x : X} (hx : x ∈ s := by trivial) : 0 < ⨆ i, f i x := by
  have ⟨i, hi⟩ := f.exists_pos hx
  exact hi.trans_le <| le_ciSup (HasFiniteSupport.finite_range (f.point_finite x)).bddAbove i

open Classical in
lemma cbiSup_eq (f : GeneralizedPositivePartition ι X) {s : Set ι} {x : X}
    {s' : Finset ι} (hs' : f.finsupport x ⊆ s') :
    ⨆ i ∈ s, f i x =
      if h : Finset.Nonempty {i ∈ s' | i ∈ s} then Finset.sup' _ h fun i ↦ f i x else 0 := by
  refine s.eq_empty_or_nonempty.rec (fun h ↦ by simp [h]) fun hs ↦ ?_
  have h' : BddAbove (range fun i : s ↦ f i x) :=
    (HasFiniteSupport.finite_range (.comp_of_injective (by simp) <| f.point_finite x)).bddAbove
  rw [← csSup_image h' (le_ciSup_of_le h' _ <| by simpa using f.nonneg hs.to_subtype.some x)]
  obtain h | h := Finset.eq_empty_or_nonempty {i ∈ s' | i ∈ s}
  · simp only [h, Finset.not_nonempty_empty, ↓reduceDIte]
    suffices (fun i ↦ f i x) '' s = {0} by simp [*]
    suffices h : ∀ i ∈ s, f i x = 0 by
      refine subset_antisymm (fun _ ⟨i, hi⟩ ↦ hi.2 ▸ h i hi.1) fun x hx ↦ ?_
      exact ⟨_, hs.choose_spec, hx ▸ h _ hs.choose_spec⟩
    intro i hi
    replace h : Disjoint s s' := by
      rw [disjoint_iff_inter_eq_empty, inter_comm]
      simpa [← Finset.coe_inj, Set.inter_def] using h
    simp only [finsupport, Function.mem_support, Finite.toFinset_subset] at hs'
    grind
  · simp only [h, ↓reduceDIte]
    refine le_antisymm ?_ ?_
    · simp only [Finset.sup'_eq_csSup_image]
      refine csSup_le (hs.image _) ?_
      rintro _ ⟨i, hi, rfl⟩
      by_cases hi' : i ∈ s'
      · exact le_csSup ((HasFiniteSupport.finite_range (f.point_finite x)).subset
          (image_subset_range _ _)).bddAbove ⟨i, by simp [*], rfl⟩
      · simp only [show (f i) x = 0 by simpa using Finset.notMem_mono hs' hi']
        exact le_csSup_of_le ((HasFiniteSupport.finite_range (f.point_finite x)).subset
          (image_subset_range _ _)).bddAbove ⟨_, h.choose_spec, rfl⟩ <| f.nonneg _ _
    · rw [Finset.sup'_le_iff]
      exact fun i hi ↦ le_csSup ((HasFiniteSupport.finite_range (f.point_finite x)).subset
        (image_subset_range _ _)).bddAbove <| mem_image_of_mem _ (by simp_all)

lemma _root_.Finset.sup'_eq_cbiSup {ι : Type u_1} {α : Type u_2} [ConditionallyCompleteLattice α]
    (s : Finset ι) (hs : s.Nonempty) (f : ι → α) (h : ∃ i ∈ s, sSup ∅ ≤ f i) :
    (Finset.sup' s hs f) = ⨆ i ∈ s, f i := by
  rw [Finset.sup'_eq_csSup_image, csSup_image (finite_range _).bddAbove]
  · simp
  · obtain ⟨i, hi⟩ := h
    exact .trans (by exact hi.2) <| le_ciSup (finite_range _).bddAbove ⟨i, hi.1⟩

lemma cbiSup_eq_finset_sup' (f : GeneralizedPositivePartition ι X) {s : Finset ι} (hs : s.Nonempty)
    (x : X) : ⨆ i ∈ s, f i x = Finset.sup' s hs fun i ↦ f i x := by
  rw [Finset.sup'_eq_cbiSup]
  have ⟨i, hi⟩ := hs
  exact ⟨i, hi, by simp [f.nonneg]⟩

lemma ciSup_eq_finset_sup' (f : GeneralizedPositivePartition ι X) (x : X) :
    ⨆ i, f i x = (f.finsupport x).sup' f.finsupport_nonempty fun i ↦ f i x := by
  simpa [f.finsupport_nonempty] using f.cbiSup_eq (s := .univ) (s' := f.finsupport x) (x := x)

lemma exists_eq_cbiSup (f : GeneralizedPositivePartition ι X) {s : Set ι}
    (hs : s.Nonempty) (x : X) : ∃ i ∈ s, f i x = ⨆ i ∈ s, f i x := by
  simp only [f.cbiSup_eq subset_rfl]
  classical
  obtain h | h := Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ s}
  · refine hs.imp fun i hi ↦ ⟨hi, ?_⟩
    grind [Finset.filter_eq_empty_iff, mem_finsupport, mem_support]
  · have ⟨i, hi⟩ := Finset.exists_mem_eq_sup' h (f := fun i ↦ f i x)
    refine ⟨i, by grind, ?_⟩
    simp [h, ← hi.2]

lemma exists_eq_ciSup (f : GeneralizedPositivePartition ι X) (x : X) :
    ∃ i, f i x = ⨆ i, f i x := by
  rw [ciSup_eq_finset_sup']
  have ⟨i, hi⟩ := Finset.exists_mem_eq_sup' (f.finsupport_nonempty (x := x)) (f := fun i ↦ f i x)
  exact ⟨i, hi.2.symm⟩

lemma cbiSup_mono (f : GeneralizedPositivePartition ι X) {s t : Set ι} (h : s ⊆ t) {x : X} :
    ⨆ i ∈ s, f i x ≤ ⨆ i ∈ t, f i x := by
  rw [f.cbiSup_eq subset_rfl]
  classical
  obtain h' | h' := Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ s}
  · simp [h', f.cbiSup_nonneg]
  · rw [f.cbiSup_eq subset_rfl]
    simp only [h', ↓reduceDIte, h'.mono (t := {i ∈ f.finsupport x | i ∈ t}) (by grind)]
    grw [h]

lemma cbiSup_le_finsum (f : GeneralizedPositivePartition ι X) {s : Set ι} {x : X} :
    ⨆ i ∈ s, f i x ≤ ∑ᶠ i ∈ s, f i x := by
  refine s.eq_empty_or_nonempty.rec (fun h ↦ by simp [h]) fun h ↦ ?_
  have ⟨i, hi, hi'⟩ := f.exists_eq_cbiSup h x
  exact hi'.symm.trans_le <| le_finsum_of_mem (f.point_finite x) (by simp [f.nonneg]) hi

lemma cbiSup_union (f : GeneralizedPositivePartition ι X) {s t : Set ι} {x : X} :
    ⨆ i ∈ (s ∪ t), f i x = (⨆ i ∈ s, f i x) ⊔ ⨆ i ∈ t, f i x := by
  symm
  rw [f.cbiSup_eq subset_rfl]
  classical
  obtain hs | hs := Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ s}
  · simp only [hs, Finset.not_nonempty_empty, ↓reduceDIte, f.cbiSup_nonneg, sup_of_le_right]
    rw [f.cbiSup_eq subset_rfl, f.cbiSup_eq subset_rfl]
    obtain ht | ht := Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ t}
    · simp [ht, show {x ∈ f.finsupport x | x ∈ s ∨ x ∈ t} = ∅ by grind]
    · simp only [ht, ↓reduceDIte, mem_union,
        show Finset.Nonempty ({x ∈ f.finsupport x | x ∈ s ∨ x ∈ t}) by
          grind [Finset.filter_eq_empty_iff]]
      rw! [show {i ∈ f.finsupport x | i ∈ t} = {x ∈ f.finsupport x | x ∈ s ∨ x ∈ t} by
        grind [Finset.filter_eq_empty_iff]]
      rfl
  · simp only [hs, ↓reduceDIte]
    rw [f.cbiSup_eq subset_rfl, f.cbiSup_eq subset_rfl]
    have h : Finset.Nonempty {x ∈ f.finsupport x | x ∈ s ∨ x ∈ t} := by
      grind [Finset.filter_eq_empty_iff]
    obtain ht | ht := Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ t}
    · simp only [ht, Finset.not_nonempty_empty, ↓reduceDIte, mem_union, h]
      rw [sup_of_le_left (by grind [Finset.le_sup'_iff, f.nonneg])]
      rw! [show {i ∈ f.finsupport x | i ∈ s} = {x ∈ f.finsupport x | x ∈ s ∨ x ∈ t} by
        grind [Finset.filter_eq_empty_iff]]
      rfl
    · simp only [ht, ↓reduceDIte, mem_union, h, ← Finset.sup'_union]
      rw! [Finset.filter_or]; rfl

lemma continuous_cbiSup (f : GeneralizedPositivePartition ι X) (s : Set ι) :
    Continuous fun x ↦ ⨆ i ∈ s, f i x := by
  refine s.eq_empty_or_nonempty.rec (fun h ↦ by simp [continuous_const, h]) fun hs ↦ ?_
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  refine .congr (f := fun x' ↦ (⨆ i ∈ s \ f.finsupport x, (f i) x') ⊔
    ⨆ i ∈ s ∩ f.finsupport x, (f i) x') (.sup ?_ ?_) (.of_forall fun x' ↦ ?_)
  · rw [ContinuousAt, show ⨆ i ∈ s \ f.finsupport x, (f i) x = 0 by
      rw [f.cbiSup_eq subset_rfl, dite_eq_right_iff]
      exact fun h ↦ (Finset.sup'_congr h rfl (by simp)).trans <| Finset.sup'_const h 0]
    refine squeeze_zero (fun x ↦ f.cbiSup_nonneg) (fun x ↦ ?_) f.finsum_compl_finsupport_tendsto
    exact (f.cbiSup_mono (by grind)).trans f.cbiSup_le_finsum
  · classical
    rw [show s ∩ ↑(f.finsupport x) = ({i ∈ f.finsupport x | i ∈ s} : Finset ι) by grind]
    refine (Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ s}).rec
      (fun h ↦ by simp [h, continuousAt_const]) fun h ↦ ?_
    exact .congr (f := fun x' ↦ Finset.sup' _ h fun i ↦ f i x') (by fun_prop) <| .of_forall
      fun x' ↦ by simp only [Finset.mem_coe, cbiSup_eq_finset_sup', h]
  · simp only [← cbiSup_union, coe_finsupport, sdiff_union_inter]

@[fun_prop]
lemma continuous_ciSup (f : GeneralizedPositivePartition ι X) : Continuous fun x ↦ ⨆ i, f i x := by
  simpa using f.continuous_cbiSup .univ

end GeneralizedPositivePartition

namespace PositivePartition

variable {X ι : Type*} [TopologicalSpace X] {s : Set X} (f : PositivePartition ι X s)
    {u : ι → Set X}

instance : FunLike (PositivePartition ι X s) ι C(X, ℝ) where
  coe f := f.toGeneralizedPositivePartition
  coe_injective := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr

@[simp]
lemma coe_mk (toGeneralizedPositivePartition : GeneralizedPositivePartition ι X s)
    (locallyFinite' : LocallyFinite fun i => support (toGeneralizedPositivePartition.toFun i))
    {i : ι} :
  PositivePartition.mk toGeneralizedPositivePartition locallyFinite' i =
    toGeneralizedPositivePartition i := rfl

protected lemma locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

lemma locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

lemma nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

lemma exists_pos {x : X} (hx : x ∈ s) : ∃ i, 0 < f i x :=
  f.toGeneralizedPositivePartition.exists_pos hx

lemma sum_pos {x : X} (hx : x ∈ s) : 0 < ∑ᶠ i, f i x :=
  f.toGeneralizedPositivePartition.sum_pos hx

lemma continuous_sum : Continuous fun x ↦ ∑ᶠ i, f i x :=
  f.toGeneralizedPositivePartition.continuous_sum

/-- The partition of unity obtained from a positive partition by dividing all functions by their
sum. -/
noncomputable def toPartitionOfUnity (f : PositivePartition ι X) : PartitionOfUnity ι X where
  toFun i := ⟨_, (map_continuous (f i)).div f.continuous_sum fun x ↦ (f.sum_pos trivial).ne'⟩
  locallyFinite' := by
    suffices h : support (fun x ↦ ∑ᶠ (i : ι), f i x) = univ by simp [h, f.locallyFinite]
    exact eq_univ_of_forall fun x ↦ (f.sum_pos trivial).ne'
  nonneg' i x := by simpa using div_nonneg (f.nonneg i x) (f.sum_pos trivial).le
  sum_eq_one' := by
    simp [div_eq_mul_inv, ← finsum_mul, fun x ↦ (f.sum_pos (mem_univ x)).ne']
  sum_le_one' := by
    simp [div_eq_mul_inv, ← finsum_mul, fun x ↦ (f.sum_pos (mem_univ x)).ne']

-- TODO: move
@[simp]
lemma _root_.PartitionOfUnity.coe_mk (toFun : ι → C(X, ℝ))
    (locallyFinite' : LocallyFinite fun i => support (toFun i))
    (nonneg' : 0 ≤ toFun) (sum_eq_one' : ∀ x ∈ s, ∑ᶠ (i : ι), (toFun i) x = 1)
    (sum_le_one' : ∀ (x : X), ∑ᶠ (i : ι), (toFun i) x ≤ 1) {i : ι} :
  PartitionOfUnity.mk toFun locallyFinite' nonneg' sum_eq_one' sum_le_one' i = toFun i := rfl

@[simp]
lemma support_toPartitionOfUnity (f : PositivePartition ι X) {i : ι} :
    support (f.toPartitionOfUnity i) = support (f i) := by
  suffices h : support (fun x ↦ ∑ᶠ (i : ι), f i x) = univ by simp [toPartitionOfUnity, h]
  exact eq_univ_of_forall fun x ↦ (f.sum_pos trivial).ne'

@[simp]
lemma tsupport_toPartitionOfUnity (f : PositivePartition ι X) {i : ι} :
    tsupport (f.toPartitionOfUnity i) = tsupport (f i) := by
  simp [tsupport]

/-- The positive partition underlying a partition of unity.

TODO: when upstreaming positive partitions to mathlib, let `PartitionOfUnity` extend
`PositivePartition` instead of making this a definition. -/
def _root_.PartitionOfUnity.toPositivePartition (f : PartitionOfUnity ι X s) :
    PositivePartition ι X s where
  __ := f
  exists_pos' _ hx := f.exists_pos hx

@[simp]
lemma _root_.PartitionOfUnity.toPartitionOfUnity_toPositivePartition (f : PartitionOfUnity ι X) :
    f.toPositivePartition.toPartitionOfUnity = f := by
  cases f
  simp only [toPartitionOfUnity, PartitionOfUnity.toPositivePartition, coe_mk,
    PartitionOfUnity.mk.injEq]
  ext i x
  simp [*]

-- TODO: move
@[simp]
lemma _root_.PartitionOfUnity.toFun_eq_coe (f : PartitionOfUnity ι X s) : f.toFun = f := rfl

@[simp]
lemma _root_.PartitionOfUnity.support_toPositivePartition (f : PartitionOfUnity ι X s) {i : ι} :
    support (f.toPositivePartition i) = support (f i) := by
  simp [PartitionOfUnity.toPositivePartition]

@[simp]
lemma _root_.PartitionOfUnity.tsupport_toPositivePartition (f : PartitionOfUnity ι X s) {i : ι} :
    tsupport (f.toPositivePartition i) = tsupport (f i) := by
  simp [tsupport]

def IsSubordinate (u : ι → Set X) := ∀ i, tsupport (f i) ⊆ u i

lemma IsSubordinate.toPartitionOfUnity {f : PositivePartition ι X} (hf : f.IsSubordinate u) :
    f.toPartitionOfUnity.IsSubordinate u := by
  simpa [IsSubordinate, PartitionOfUnity.IsSubordinate] using hf

lemma _root_.PartitionOfUnity.IsSubordinate.toPositivePartition {f : PartitionOfUnity ι X s}
    (hf : f.IsSubordinate u) :
    f.toPositivePartition.IsSubordinate u := by
  simpa [IsSubordinate, PartitionOfUnity.IsSubordinate] using hf

end PositivePartition
