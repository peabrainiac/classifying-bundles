/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.PositivePartition

/-! # Partitions of unity
More API on continuous partitions of unity and bump coverings as already defined in mathlib.
-/

open Set

open scoped Topology

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {u : ι → Set X}

lemma PartitionOfUnity.IsSubordinate.mem_of_pos {f : PartitionOfUnity ι X} (hf : f.IsSubordinate u)
    {i : ι} {x : X} (hx : 0 < f i x) : x ∈ u i :=
  hf i <| subset_tsupport _ hx.ne'

lemma PartitionOfUnity.finsupport_nonempty {s : Set X} (f : PartitionOfUnity ι X s)
    {x : X} (hx : x ∈ s := by trivial) : (f.finsupport x).Nonempty :=
  (f.exists_pos hx).imp fun _ h ↦ by simpa using h.ne'

lemma PartitionOfUnity.fintsupport_nonempty {s : Set X} (f : PartitionOfUnity ι X s)
    {x : X} (hx : x ∈ s := by trivial) : (f.fintsupport x).Nonempty :=
  (f.finsupport_nonempty hx).mono (f.finsupport_subset_fintsupport x)

lemma PartitionOfUnity.ciSup_pos (f : PartitionOfUnity ι X) {x : X} : 0 < ⨆ i, f i x := by
  have ⟨i, hi⟩ := f.exists_pos (mem_univ x)
  exact hi.trans_le <| le_ciSup (f := fun i ↦ f i x) ⟨1, fun _ ⟨_, h⟩ ↦ h ▸ f.le_one _ _⟩ i

open Classical in
lemma PartitionOfUnity.cbiSup_eq (f : PartitionOfUnity ι X) {s : Set ι} {x : X}
    {s' : Finset ι} (hs' : f.finsupport x ⊆ s') :
    ⨆ i ∈ s, f i x =
      if h : Finset.Nonempty {i ∈ s' | i ∈ s} then Finset.sup' _ h fun i ↦ f i x else 0 := by
  refine s.eq_empty_or_nonempty.rec (fun h ↦ by simp [h]) fun hs ↦ ?_
  have h' : BddAbove (range fun i : s ↦ f i x) := ⟨1, fun _ ⟨_, h⟩ ↦ h ▸ f.le_one _ _⟩
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
      · exact le_csSup ⟨1, fun _ ⟨_, h⟩ ↦ h.2 ▸ f.le_one _ _⟩ ⟨i, by simp [*], rfl⟩
      · simp only [show (f i) x = 0 by simpa using Finset.notMem_mono hs' hi']
        exact le_csSup_of_le ⟨1, fun _ ⟨_, h⟩ ↦ h.2 ▸ f.le_one _ _⟩ ⟨_, h.choose_spec, rfl⟩ <|
          f.nonneg _ _
    · rw [Finset.sup'_le_iff]
      exact fun i hi ↦ le_csSup ⟨1, fun _ ⟨_, h⟩ ↦ h.2 ▸ f.le_one _ _⟩ <|
        mem_image_of_mem _ (by simp_all)

lemma PartitionOfUnity.ciSup_eq_finset_sup' (f : PartitionOfUnity ι X) (x : X) :
    ⨆ i, f i x = (f.finsupport x).sup' f.finsupport_nonempty fun i ↦ f i x := by
  simpa [f.finsupport_nonempty] using f.cbiSup_eq (s := .univ) (s' := f.finsupport x) (x := x)

lemma PartitionOfUnity.exists_eq_ciSup (f : PartitionOfUnity ι X) (x : X) :
    ∃ i, f i x = ⨆ i, f i x := by
  rw [ciSup_eq_finset_sup']
  have ⟨i, hi⟩ := Finset.exists_mem_eq_sup' (f.finsupport_nonempty (x := x)) (f := fun i ↦ f i x)
  exact ⟨i, hi.2.symm⟩

-- taken from mathlib PR #40745
-- TODO: remove upon next bumping mathlib
lemma Set.Nonempty.forall_const {α : Type*} {s : Set α} (h : s.Nonempty) {p : Prop} :
    (∀ x ∈ s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h ↦ h x hx, fun h _ _ ↦ h⟩

lemma PartitionOfUnity.cbiSup_lt_iff (f : PartitionOfUnity ι X) {s : Set ι} (hs : s.Nonempty)
    {x : X} {a : ℝ} : ⨆ i ∈ s, f i x < a ↔ ∀ i ∈ s, f i x < a := by
  rw [f.cbiSup_eq subset_rfl]
  classical
  obtain h | h := Finset.eq_empty_or_nonempty {i ∈ f.finsupport x | i ∈ s}
  · simp only [h, Finset.not_nonempty_empty, ↓reduceDIte]
    rw [← hs.forall_const (p := 0 < a), forall₂_congr]
    simp at h
    grind
  · simp only [h, ↓reduceDIte, Finset.sup'_lt_iff]
    refine ⟨fun h' i hi ↦ ?_, fun _ ↦ by grind⟩
    suffices ∀ i ∉ f.finsupport x, f i x < a by grind
    intro i hi
    simp only [mem_finsupport, Function.mem_support] at hi
    have ⟨j, hj⟩ := h
    have := (f.nonneg j x).trans_lt (h' _ hj)
    grind

lemma PartitionOfUnity.continuous_cbiSup (f : PartitionOfUnity ι X) (s : Set ι) :
    Continuous fun x ↦ ⨆ i ∈ s, f i x := by
  refine s.eq_empty_or_nonempty.rec (fun h ↦ by simp [continuous_const, h]) fun hs ↦ ?_
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  classical
  obtain h | h := Finset.eq_empty_or_nonempty {i ∈ f.fintsupport x | i ∈ s}
  · refine .congr_of_eventuallyEq (f := 0) continuousAt_const <|
      (f.eventually_finsupport_subset x).mono fun x' h' ↦ ?_
    simp [f.cbiSup_eq (s := s) h', h]
  · refine .congr_of_eventuallyEq (f := Finset.sup' {i ∈ f.fintsupport x | i ∈ s} h fun i ↦ f i)
      (.finset_sup' h (by fun_prop)) <| (f.eventually_finsupport_subset x).mono fun x' h' ↦ ?_
    simp [f.cbiSup_eq (s := s) h', h]

lemma PartitionOfUnity.continuous_ciSup (f : PartitionOfUnity ι X) :
    Continuous fun x ↦ ⨆ i, f i x := by
  simpa using f.continuous_cbiSup .univ

-- TODO: move
@[simp]
lemma ContinuousMap.coe_two {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NatCast Y] :
    ⇑(2 : C(X, Y)) = 2 :=
  rfl

/-- The bump covering obtained from a partition of unity `f` by dividing each function `f i`
by `fun x ↦ ⨆ i, f i x`, doubling the result and clamping it to at most one. -/
noncomputable def PartitionOfUnity.toBumpCovering (f : PartitionOfUnity ι X) :
    BumpCovering ι X where
  toFun i := 1 ⊓ 2 * ⟨_, (map_continuous (f i)).div f.continuous_ciSup fun x ↦ f.ciSup_pos.ne'⟩
  locallyFinite' := by
    simp_rw [ContinuousMap.coe_inf, ContinuousMap.coe_one,
      show ∀ f : X → ℝ, (1 ⊓ f).support = f.support by
        intro i; ext x; simp only [Function.mem_support, Pi.inf_apply, Pi.one_apply]; grind]
    suffices h : Function.support (fun x ↦ ⨆ i, (f i) x) = .univ by
      simp [h, f.locallyFinite, show Function.support (2 : X → ℝ) = .univ by ext; simp]
    exact eq_univ_of_forall fun x ↦ f.ciSup_pos.ne'
  nonneg' i x := by simpa using div_nonneg (f.nonneg i x) f.ciSup_pos.le
  le_one' i x := by simp
  eventuallyEq_one' x _ := by
    have ⟨i, hi⟩ := f.exists_eq_ciSup x
    suffices h : 1 ≤ᶠ[𝓝 x] (2 * ⟨_, (map_continuous (f i)).div f.continuous_ciSup
        fun x ↦ f.ciSup_pos.ne'⟩ : C(X, ℝ)) from ⟨i, h.mono fun x ↦ by simp⟩
    refine .mono ?_ (fun _ h ↦ LT.lt.le h)
    refine (continuousAt_const (y := 1)).eventually_lt (by fun_prop) ?_
    simp [hi, f.ciSup_pos.ne']

@[simp]
lemma PartitionOfUnity.support_toBumpCovering (f : PartitionOfUnity ι X) {i : ι} :
    Function.support (f.toBumpCovering i) = Function.support (f i) := by
  simp [toBumpCovering, ← BumpCovering.toFun_eq_coe,
    show ∀ f : X → ℝ, (1 ⊓ f).support = f.support by
      intro i; ext x; simp only [Function.mem_support, Pi.inf_apply, Pi.one_apply]; grind,
    show Function.support (2 : X → ℝ) = .univ by ext; simp, f.ciSup_pos.ne']

@[simp]
lemma PartitionOfUnity.tsupport_toBumpCovering (f : PartitionOfUnity ι X) {i : ι} :
    tsupport (f.toBumpCovering i) = tsupport (f i) := by
  simp [tsupport]

lemma PartitionOfUnity.IsSubordinate.toBumpCovering {f : PartitionOfUnity ι X}
    (hf : f.IsSubordinate u) : f.toBumpCovering.IsSubordinate u := by
  simpa [BumpCovering.IsSubordinate, PartitionOfUnity.IsSubordinate] using hf

lemma PartitionOfUnity.IsSubordinate.mono {f : PartitionOfUnity ι X} (hf : f.IsSubordinate u)
    {v : ι → Set X} (h : ∀ i, u i ⊆ v i) : f.IsSubordinate v :=
  fun i ↦ (hf i).trans (h i)

-- TODO: move
lemma finsum_fiberwise {α β : Type*} {M : Type*} [AddCommMonoid M] {f : α → M} {g : α → β}
    (hf : f.HasFiniteSupport) : ∑ᶠ i, ∑ᶠ j ∈ g ⁻¹' {i}, f j = ∑ᶠ i, f i := by
  classical
  rw [finsum_eq_sum f hf, ← finsum_sum_filter g hf.toFinset f]
  refine finsum_congr fun x ↦ finsum_cond_eq_sum_of_cond_iff _ ?_
  grind [Finite.mem_toFinset, Function.mem_support]

/-- The `ι'`-indexed partition of unity induced from an `ι`-indexed partition of unity by a map
`g : ι → ι'`, defined by summing functions over the fibre of each index in `ι'` under `g`. -/
noncomputable def PartitionOfUnity.map {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} (g : ι → ι') : PartitionOfUnity ι' X s where
  toFun i' := ⟨fun x ↦ ∑ᶠ i ∈ g ⁻¹' {i'}, f i x, by
    classical
    refine (f.continuous_finsum_smul (E := ℝ) (g := fun i _ ↦ if g i = i' then 1 else 0)
      (fun _ _ _  ↦ continuousAt_const)).congr fun x ↦ finsum_congr <| fun i ↦ ?_
    simp [finsum_eq_if]⟩
  locallyFinite' x := by
    refine (f.locallyFinite x).imp fun u ↦ .imp_right fun hu ↦ ?_
    convert hu.image g; ext i'
    suffices h : (Function.support fun x ↦ ∑ᶠ (i : ι) (_ : g i = i'), f i x) =
        ⋃ i ∈ g ⁻¹' {i'}, Function.support (f i) by
      simp [h, iUnion_inter, and_comm]
    ext x
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · replace h := exists_ne_zero_of_finsum_mem_ne_zero h
      simp only [mem_preimage, mem_singleton_iff, mem_iUnion, Function.mem_support,
        exists_prop] at h ⊢
      exact h
    · refine (finsum_cond_pos (fun i _ ↦ f.nonneg i x) ?_ ?_).ne'
      · simp only [mem_iUnion, Function.mem_support] at h
        grind [nonneg]
      · exact .inter_of_left (f.locallyFinite.point_finite x) _
  nonneg' _ _ := finsum_nonneg fun _ ↦ finsum_nonneg fun _ ↦ f.nonneg _ _
  sum_eq_one' x hx := (finsum_fiberwise <| f.locallyFinite.point_finite x).trans <| f.sum_eq_one hx
  sum_le_one' x := (finsum_fiberwise <| f.locallyFinite.point_finite x).trans_le <| f.sum_le_one x

lemma PartitionOfUnity.map_apply_eq_finsum {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} {g : ι → ι'} {i' : ι'} {x : X} :
    f.map g i' x = ∑ᶠ i ∈ g ⁻¹' {i'}, f i x :=
  rfl

open Classical in
lemma PartitionOfUnity.map_apply_eq_finset_sum {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} {g : ι → ι'} {i' : ι'} {x : X} {s' : Finset ι} (h : f.finsupport x ⊆ s') :
    f.map g i' x = ∑ i ∈ {i ∈ s' | g i = i'}, f i x := by
  rw [f.map_apply_eq_finsum, finsum_mem_eq_sum_of_inter_support_eq]
  suffices ∀ i, f i x ≠ 0 → i ∈ s' by grind [Function.mem_support]
  exact fun i hi ↦ @h i <| by simpa

@[simp]
lemma PartitionOfUnity.support_map {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} {g : ι → ι'} {i' : ι'} :
    Function.support (f.map g i') = ⋃ i ∈ g ⁻¹' {i'}, Function.support (f i) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · replace h := exists_ne_zero_of_finsum_mem_ne_zero h
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, Function.mem_support,
      exists_prop] at h ⊢
    exact h
  · refine (finsum_cond_pos (fun i _ ↦ f.nonneg i x) ?_ ?_).ne'
    · simp only [mem_iUnion, Function.mem_support] at h
      grind [nonneg]
    · exact .inter_of_left (f.locallyFinite.point_finite x) _

-- TODO: move
lemma LocallyFinite.closure_biUnion {f : ι → Set X} {s : Set ι} (hf : LocallyFinite f) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) := by
  simpa using (hf.comp_injective (ι' := s) Subtype.val_injective).closure_iUnion

@[simp]
lemma PartitionOfUnity.tsupport_map {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} {g : ι → ι'} {i' : ι'} :
    tsupport (f.map g i') = ⋃ i ∈ g ⁻¹' {i'}, tsupport (f i) := by
  simp only [tsupport, f.support_map, f.locallyFinite.closure_biUnion]

@[simp]
lemma PartitionOfUnity.finsupport_map {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} [DecidableEq ι'] {g : ι → ι'} {x : X} :
    (f.map g).finsupport x = (f.finsupport x).image g := by
  simp only [finsupport, support_map, mem_iUnion, ← Finset.coe_inj,
    Finite.coe_toFinset, Finset.coe_image]
  grind

@[simp]
lemma PartitionOfUnity.fintsupport_map {s : Set X} (f : PartitionOfUnity ι X s)
    {ι' : Type*} [DecidableEq ι'] {g : ι → ι'} {x : X} :
    (f.map g).fintsupport x = (f.fintsupport x).image g := by
  simp only [fintsupport, tsupport_map, mem_iUnion, ← Finset.coe_inj,
    Finite.coe_toFinset, Finset.coe_image]
  grind

lemma PartitionOfUnity.IsSubordinate.map {s : Set X} {f : PartitionOfUnity ι X s}
    (hf : f.IsSubordinate u) {ι' : Type*} {g : ι → ι'} {u' : ι' → Set X}
    (h : ∀ i, u i ⊆ u' (g i)) : (f.map g).IsSubordinate u' := by
  simp only [IsSubordinate, tsupport_map, Set.iUnion₂_subset_iff] at hf ⊢
  rintro _ i rfl
  exact (hf i).trans (h i)

/-- The pullback of a partition of unity along a continuous map. -/
@[simps!]
def PartitionOfUnity.pullback {s : Set X} (f : PartitionOfUnity ι X s) {Y : Type*}
    [TopologicalSpace Y] (g : C(Y, X)) (t : Set Y := univ) (h : MapsTo g t s := by simp) :
    PartitionOfUnity ι Y t where
  toFun i := (f i).comp g
  locallyFinite' := f.locallyFinite.preimage_continuous (map_continuous g)
  nonneg' _ _ := by simp [f.nonneg]
  sum_eq_one' _ _ := by simp [f.sum_eq_one (h ‹_›)]
  sum_le_one' := by simp [f.sum_le_one]

@[simp]
lemma PartitionOfUnity.support_pullback {s : Set X} (f : PartitionOfUnity ι X s) {Y : Type*}
    [TopologicalSpace Y] {g : C(Y, X)} {t : Set Y} {h : MapsTo g t s} {i : ι} :
    Function.support (f.pullback g t h i) = g ⁻¹' Function.support (f i) := by
  simp [PartitionOfUnity.pullback, Function.support_comp_eq_preimage]

@[simp]
lemma PartitionOfUnity.tsupport_pullback_subset {s : Set X} (f : PartitionOfUnity ι X s) {Y : Type*}
    [TopologicalSpace Y] {g : C(Y, X)} {t : Set Y} {h : MapsTo g t s} {i : ι} :
    tsupport (f.pullback g t h i) ⊆ g ⁻¹' tsupport (f i) := by
  simp [tsupport, (map_continuous g).closure_preimage_subset]

lemma PartitionOfUnity.IsSubordinate.pullback {s : Set X} {f : PartitionOfUnity ι X s}
    {u : ι → Set X} (hu : f.IsSubordinate u) {Y : Type*} [TopologicalSpace Y] (g : C(Y, X))
    {t : Set Y} {h : MapsTo g t s} : (f.pullback g t h).IsSubordinate (fun i ↦ g ⁻¹' u i) := by
  refine fun i ↦ f.tsupport_pullback_subset.trans ?_
  dsimp; gcongr; exact hu i

/-- Shrink a bump covering so that the closure of the support of the new functions are contained
in the supports of the old functions. -/
def BumpCovering.shrink (f : BumpCovering ι X) : BumpCovering ι X where
  toFun i := 0 ⊔ (2 * f i - 1)
  locallyFinite' := by
    refine f.locallyFinite.subset fun i x ↦ ?_
    simp only [ContinuousMap.coe_sup, ContinuousMap.coe_zero, ContinuousMap.coe_sub,
      ContinuousMap.coe_mul, ContinuousMap.coe_two, ContinuousMap.coe_one, Function.mem_support,
      Pi.sup_apply, Pi.sub_apply, Pi.mul_apply, Pi.ofNat_apply, ne_eq,
      sup_eq_left, tsub_le_iff_right, zero_add, not_le]
    grind
  nonneg' i := by simp
  le_one' i x := by simp [one_add_one_eq_two, f.le_one i x]
  eventuallyEq_one' x _ := by
    use f.ind x trivial
    refine (f.eventuallyEq_one x trivial).mono fun x' ↦ ?_
    simp only [ContinuousMap.sup_apply, ContinuousMap.zero_apply,
      ContinuousMap.sub_apply, ContinuousMap.mul_apply, ContinuousMap.coe_two, Pi.ofNat_apply,
      ContinuousMap.one_apply]
    grind

lemma BumpCovering.tsupport_shrink_subset (f : BumpCovering ι X) {i : ι} :
    tsupport (f.shrink i) ⊆ Function.support (f i) := by
  refine .trans (b := f i ⁻¹' Set.Ici (1 / 2)) ?_ fun x ↦ ?_
  · rw [tsupport, (isClosed_Ici.preimage (map_continuous (f i))).closure_subset_iff]
    intro x
    simp only [shrink, ← toFun_eq_coe, ContinuousMap.coe_sup, ContinuousMap.coe_zero,
      ContinuousMap.coe_sub, ContinuousMap.coe_mul, ContinuousMap.coe_two, ContinuousMap.coe_one,
      Function.mem_support, Pi.sup_apply, Pi.sub_apply, Pi.mul_apply, Pi.ofNat_apply]
    grind
  · simp only [one_div, mem_preimage, mem_Ici, Function.mem_support, ne_eq]
    grind

/-- For a bump covering `f`, `f.shrink` is subordinate to the covering by the supports of `f`.
Note that this is not true for `f` itself because `IsSubordinate` requires the topological supports
to be contained in the covering, not just the plain supports. -/
lemma BumpCovering.isSubordinate_shrink (f : BumpCovering ι X) :
    f.shrink.IsSubordinate fun i ↦ Function.support (f i) :=
  fun _ ↦ f.tsupport_shrink_subset

lemma BumpCovering.isSubordinate_tsupport (f : BumpCovering ι X) :
    f.IsSubordinate fun i ↦ tsupport (f i) :=
  fun _ ↦ subset_rfl
