/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

open Set

/-! # Open partial homeomorphisms
More API on open partial homeomorphisms as already defined in mathlib.
-/

open Classical in
/-- The `OpenPartialHomeomorph` given by a homeomorphism between two open subsets. -/
noncomputable def Homeomorph.toOpenPartialHomeomorph' {X Y : Type*} [TopologicalSpace X]
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

open Classical in
/-- The union of two open partial homeomorphisms that agree on the intersection of their domains.

Note: it probably makes sense to upstream this together with `Trivialization.union`,
found in another file. -/
@[simps! source target]
noncomputable def OpenPartialHomeomorph.union {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e e' : OpenPartialHomeomorph X Y) (h : (e.source ∩ e'.source).EqOn e e')
    (h' : e'.IsImage e.source e.target) :
    OpenPartialHomeomorph X Y where
  toPartialEquiv := e.toPartialEquiv.piecewise e'.toPartialEquiv e.source e.target
    e.isImage_source_target h'
  open_source := by simpa using e.open_source.union e'.open_source
  open_target := by simpa using e.open_target.union e'.open_target
  continuousOn_toFun := by
    suffices ContinuousOn (e.source.piecewise e e') (e.source ∪ e'.source) by simpa
    refine .union_of_isOpen ?_ ?_ e.open_source e'.open_source
    · refine .congr e.continuousOn_toFun ?_
      simp [Set.eqOn_piecewise, Set.eqOn_refl]
    · refine .congr e'.continuousOn_toFun <| ?_
      simp [Set.eqOn_piecewise, Set.eqOn_refl, Set.inter_comm _ _ ▸ h]
  continuousOn_invFun := by
    suffices ContinuousOn (e.target.piecewise e.symm e'.symm) (e.target ∪ e'.target) by simpa
    refine .union_of_isOpen ?_ ?_ e.open_target e'.open_target
    · refine .congr e.continuousOn_invFun ?_
      simp [Set.eqOn_piecewise, Set.eqOn_refl]
    · refine .congr e'.continuousOn_invFun <| ?_
      suffices Set.EqOn e.symm e'.symm (e'.target ∩ e.target) by
        simpa [Set.eqOn_piecewise, Set.eqOn_refl]
      intro y ⟨hy', hy⟩
      obtain ⟨x, hx', rfl⟩ : ∃ x, x ∈ e'.source ∧ e' x = y := ⟨e'.symm y, by simp [hy']⟩
      have hx := (h' hx').1 hy
      rw [e'.left_inv hx', ← @h x ⟨hx, hx'⟩, e.left_inv hx]

lemma OpenPartialHomeomorph.union_eqOn_left {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} : e.source.EqOn (e.union e' h h') e := by
  classical
  exact e.source.piecewise_eqOn e e'

lemma OpenPartialHomeomorph.union_eqOn_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} : e'.source.EqOn (e.union e' h h') e' := by
  classical
  exact e.source.piecewise_eqOn e e' |>.mono Set.inter_subset_left |>.trans h |>.union
    (e.source.piecewise_eqOn_compl e e') |>.mono (by grind)

lemma OpenPartialHomeomorph.union_apply_of_mem_left {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} {x : X} (hx : x ∈ e.source) : e.union e' h h' x = e x :=
  e.union_eqOn_left hx

lemma OpenPartialHomeomorph.union_apply_of_mem_right {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {e e' : OpenPartialHomeomorph X Y} {h : (e.source ∩ e'.source).EqOn e e'}
    {h' : e'.IsImage e.source e.target} {x : X} (hx : x ∈ e'.source) :
    e.union e' h h' x = e' x :=
  e.union_eqOn_right hx

open Classical in
/-- The partial equivalence obtained by glueing a family of partial equivalences that
agree on their overlaps.

TODO: move -/
@[simps! source target]
noncomputable def PartialEquiv.iUnion {X Y ι : Type*} [Nonempty ι] (e : ι → PartialEquiv X Y)
    (he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j))
    (he' : ∀ i j, (e i).IsImage (e j).source (e j).target) :
    PartialEquiv X Y where
  toFun x := e (if h : ∃ i, x ∈ (e i).source then h.choose else Classical.arbitrary ι) x
  invFun y := (e <| if h : ∃ i, y ∈ (e i).target then h.choose else Classical.arbitrary ι).symm y
  source := ⋃ i, (e i).source
  target := ⋃ i, (e i).target
  map_source' x hx := by
    simp only [mem_iUnion] at hx
    simp only [hx, ↓reduceDIte, mem_iUnion]
    exact ⟨_, (e _).map_source hx.choose_spec⟩
  map_target' y hy := by
    simp only [mem_iUnion] at hy
    simp only [hy, ↓reduceDIte, mem_iUnion]
    exact ⟨_, (e _).map_target hy.choose_spec⟩
  left_inv' x hx := by
    simp only [mem_iUnion] at hx
    have hx' : ∃ i, e hx.choose x ∈ (e i).target := ⟨_, (e _).map_source hx.choose_spec⟩
    simp only [hx, hx', ↓reduceDIte]
    change (e hx'.choose).symm ((e hx.choose) x) = x
    rw [congrArg ((e hx'.choose).symm) (he _ hx'.choose ⟨hx.choose_spec, ?_⟩), (e _).left_inv]
    all_goals exact (he' hx.choose hx'.choose hx.choose_spec).1 (hx'.choose_spec)
  right_inv' y hy := by
    simp only [mem_iUnion] at hy
    have hy' : ∃ i, (e hy.choose).symm y ∈ (e i).source := ⟨_, (e _).map_target hy.choose_spec⟩
    simp only [hy, hy', ↓reduceDIte]
    rw [he _ _ ⟨hy'.choose_spec, (e _).map_target hy.choose_spec⟩, (e _).right_inv hy.choose_spec]

lemma PartialEquiv.iUnion_eqOn {X Y ι : Type*} [Nonempty ι] (e : ι → PartialEquiv X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) :
    (e i).source.EqOn (iUnion e he he') (e i) := by
  intro x hx
  have hx' : ∃ i, x ∈ (e i).source := ⟨i, hx⟩
  simpa [iUnion, hx'] using he _ _ ⟨hx'.choose_spec, hx⟩

lemma PartialEquiv.iUnion_symm_eqOn {X Y ι : Type*} [Nonempty ι] (e : ι → PartialEquiv X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) :
    (e i).target.EqOn (iUnion e he he').symm (e i).symm := by
  intro x hx
  have hx' : ∃ i, x ∈ (e i).target := ⟨i, hx⟩
  simp_rw [iUnion, PartialEquiv.symm, hx', reduceDIte, invFun_as_coe]
  change (e hx'.choose).symm x = (e i).symm x
  refine (e i).injOn (((he' hx'.choose i).symm hx'.choose_spec).2 hx) ((e _).map_target hx) ?_
  rw [(e _).right_inv hx, he i hx'.choose ⟨?_, ?_⟩, (e _).right_inv hx'.choose_spec]
  · exact ((he' hx'.choose i).symm hx'.choose_spec).2 hx
  · exact (e _).map_target hx'.choose_spec

lemma PartialEquiv.iUnion_apply {X Y ι : Type*} [Nonempty ι] (e : ι → PartialEquiv X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) {x : X} (hx : x ∈ (e i).source) :
    iUnion e he he' x = e i x :=
  iUnion_eqOn e i hx

lemma PartialEquiv.iUnion_symm_apply {X Y ι : Type*} [Nonempty ι] (e : ι → PartialEquiv X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) {y : Y} (hy : y ∈ (e i).target) :
    (iUnion e he he').symm y = (e i).symm y :=
  iUnion_symm_eqOn e i hy

/-- The open partial homeomorphism obtained by glueing a family of open partial homeomorphism that
agree on their overlaps.

TODO: move -/
@[simps! source target]
noncomputable def OpenPartialHomeomorph.iUnion
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Nonempty ι] (e : ι → OpenPartialHomeomorph X Y)
    (he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j))
    (he' : ∀ i j, (e i).IsImage (e j).source (e j).target) :
    OpenPartialHomeomorph X Y where
  toPartialEquiv := PartialEquiv.iUnion (fun i ↦ (e i).toPartialEquiv) he he'
  open_source := isOpen_iUnion fun i ↦ (e i).open_source
  open_target := isOpen_iUnion fun i ↦ (e i).open_target
  continuousOn_toFun := by
    refine .iUnion_of_isOpen (fun i ↦ ?_) (fun i ↦ (e i).open_source)
    exact .congr (e i).continuousOn (PartialEquiv.iUnion_eqOn _ i)
  continuousOn_invFun := by
    refine .iUnion_of_isOpen (fun i ↦ ?_) (fun i ↦ (e i).open_target)
    rw [PartialEquiv.invFun_as_coe]
    exact .congr (e i).continuousOn_symm (PartialEquiv.iUnion_symm_eqOn _ i)

lemma OpenPartialHomeomorph.iUnion_eqOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Nonempty ι] (e : ι → OpenPartialHomeomorph X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) :
    (e i).source.EqOn (iUnion e he he') (e i) :=
  PartialEquiv.iUnion_eqOn _ _

lemma OpenPartialHomeomorph.iUnion_symm_eqOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Nonempty ι] (e : ι → OpenPartialHomeomorph X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) :
    (e i).target.EqOn (iUnion e he he').symm (e i).symm :=
  PartialEquiv.iUnion_symm_eqOn _ _

lemma OpenPartialHomeomorph.iUnion_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Nonempty ι] (e : ι → OpenPartialHomeomorph X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) {x : X} (hx : x ∈ (e i).source) :
    iUnion e he he' x = e i x :=
  iUnion_eqOn e i hx

lemma OpenPartialHomeomorph.iUnion_symm_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Nonempty ι] (e : ι → OpenPartialHomeomorph X Y)
    {he : ∀ i j, ((e i).source ∩ (e j).source).EqOn (e i) (e j)}
    {he' : ∀ i j, (e i).IsImage (e j).source (e j).target} (i : ι) {y : Y} (hy : y ∈ (e i).target) :
    (iUnion e he he').symm y = (e i).symm y :=
  iUnion_symm_eqOn e i hy
