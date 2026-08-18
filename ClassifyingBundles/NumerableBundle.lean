/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.IsTrivialOn
import ClassifyingBundles.NumerableCover
import Mathlib.Topology.Homotopy.Contractible

/-! # Numerable bundles
In this file we define numerable bundles, i.e. fibre bundles that can be trivialised on some
numerable covering.

The main result we prove is homotopy invariance: pullbacks of any numerable bundle along homotopic
maps are isomorphic. Note that for non-numerable bundles this isn't generally true.
-/

open Bundle unitInterval Set Function Topology

open scoped Topology

variable (F : Type*) {B : Type*} (E : B → Type*) [TopologicalSpace F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]
  (F' : Type*) {B' : Type*} (E' : B' → Type*) [TopologicalSpace F'] [TopologicalSpace B']
  [TopologicalSpace (TotalSpace F' E')]

/-- A numerable bundle is a bundle for which the subsets of the base space on which the bundle is
trivial form a numerable cover. We consider all sets on which the bundle is trivial, not just the
base sets of the trivialisations in a given bundle atlas, so this definition depends only on the
topology of the bundle and not any extra structure. -/
class NumerableBundle : Prop where
  numerableCover_isTrivialOn : NumerableCover ((↑) : {u | IsTrivialOn F E u} → Set B)

/-- Every fibre bundle on a paracompact Hausdorff space is numerable. -/
instance NumerableBundle.of_paracompactSpace [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [ParacompactSpace B] [T2Space B] : NumerableBundle F E where
  numerableCover_isTrivialOn := .of_paracompactSpace fun b ↦ by
      have ⟨u, hu, hu'⟩ := exists_mem_nhds_isTrivialOn F E b
      exact ⟨⟨u, hu'⟩, hu⟩

/-- If a bundle can be trivialised on a numerable cover, it is numerable. -/
lemma NumerableCover.numerableBundle {ι : Type*} {u : ι → Set B}
    (hu : NumerableCover u) (hu' : ∀ i, IsTrivialOn F E (u i)) : NumerableBundle F E :=
  ⟨hu.mono' fun i ↦ ⟨⟨u i, hu' i⟩, by simp⟩⟩

/-- Pullbacks of numerable bundles are numerable.

TODO: get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
instance NumerableBundle.pullback [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [(b : B) → Zero (E b)] [NumerableBundle F E] {B' : Type*} [TopologicalSpace B']
    (f : C(B', B)) : NumerableBundle F (f *ᵖ E) := by
  refine numerableCover_isTrivialOn (F := F) (E := E) |>.preimage (map_continuous f)
    |>.numerableBundle _ _ fun s ↦ s.2.pullback F E f

/-- Every numerable bundle can be trivialised on some countable locally finite numerable open cover.

TODO: get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma NumerableBundle.exists_countable_isTrivialOn_cover [∀ b, TopologicalSpace (E b)]
    [IsFiberBundle F E] [(b : B) → Zero (E b)] [NumerableBundle F E] :
    ∃ u : ℕ → Set B, LocallyFinite u ∧ NumerableCover u ∧
      ∀ i, IsOpen (u i) ∧ IsTrivialOn F E (u i) := by
  have _ : Nonempty {u | IsTrivialOn F E u} := ⟨⟨∅, isTrivialOn_empty F E⟩⟩
  have h := (numerableCover_isTrivialOn (F := F) (E := E)).countable_locallyFinite_replacement'
  refine h.imp fun u ↦ .imp_right <| .imp_right <| forall_imp fun i ⟨u', hu', hu'', hu'''⟩ ↦ ?_
  rw [← hu']
  refine ⟨isOpen_sUnion fun _ h ↦ (hu''' _ h).1, ?_⟩
  rw [sUnion_eq_iUnion]
  refine IsTrivialOn.disjointIUnion F E (fun v ↦ ?_) (fun v ↦ ?_)
  · exact ⟨v, (hu''' _ v.2).1.mem_nhdsSet_self, fun _ h ↦ hu'' h.symm⟩
  · have ⟨i, hi⟩ := (hu''' _ v.2).2
    exact .mono _ _ hi i.2

/-- Every numerable fibre bundle on `B × I` is trivial on sets of the form `u i ×ˢ univ` for
`u : ℕ → Set B` some countable locally finite numerable open cover.

TODO: get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma NumerableBundle.exists_countable_isTrivialOn_cover_prod_unitInterval (E : B × I → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [∀ b, Zero (E b)] [NumerableBundle F E] :
    ∃ u : ℕ → Set B, LocallyFinite u ∧ NumerableCover u ∧
      ∀ i, IsOpen (u i) ∧ IsTrivialOn F E (u i ×ˢ .univ) := by
  have ⟨ι, u, hu, hu'⟩ := (numerableCover_isTrivialOn (E := E) (F := F)).exists_of_prod_unitInterval
  have ⟨v, hv, hv', hv''⟩ := hu.countable_locallyFinite_replacement
  refine ⟨v, hv, hv', fun i ↦ ?_⟩
  obtain ⟨w, hw, hw', hw''⟩ := hv'' i
  rw [← hw]
  refine ⟨isOpen_sUnion fun _ h ↦ (hw'' _ h).1, ?_⟩
  rw [sUnion_eq_iUnion, iUnion_prod_const]
  refine IsTrivialOn.disjointIUnion F E (fun v ↦ ?_) (fun v ↦ ?_)
  · refine ⟨v.1 ×ˢ .univ, ((hw'' _ v.2).1.prod isOpen_univ).mem_nhdsSet_self, fun _ h ↦ ?_⟩
    exact Disjoint.set_prod_left (hw' h.symm) _ _
  · refine (hw'' _ v.2).2.rec (fun h ↦ by simp [h, isTrivialOn_empty]) fun ⟨i, hi⟩ ↦ ?_
    refine isTrivialOn_prod_unitInterval F E (hw'' v v.2).1 fun t ↦ ?_
    refine (hu' i t).imp fun w ↦ .imp_right <| fun ⟨i', hi'⟩ ↦ ?_
    grw [hi, hi']
    exact i'.2

/-- A set is open if and only if its intersection with every set in an open cover is.

TODO: move -/
lemma isOpen_iff_of_open_cover {X : Type*} [TopologicalSpace X] {ι : Type*} {u : ι → Set X}
    (hu : ∀ i, IsOpen (u i)) (hu' : ⋃ i, u i = univ) {v : Set X} :
    IsOpen v ↔ ∀ i, IsOpen (v ∩ u i) := by
  refine ⟨fun hv i ↦ hv.inter (hu i), fun hv ↦ isOpen_iff_mem_nhds.2 fun x hx ↦ ?_⟩
  have ⟨i, hi⟩ := iUnion_eq_univ_iff.1 hu' x
  exact Filter.mem_of_superset ((hv i).mem_nhds ⟨hx, hi⟩) inter_subset_left

/-- A map `f : X → Y` is inducing if and only if for any open cover `u` of `range f` whose preimages
under `f` are also open, it is on each `f ⁻¹' u i` equal to an inducing map `f'` for which
`f' ⁻¹' u i = f ⁻¹' u i`.

TODO: move -/
lemma isInducing_iff_of_open_cover {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} {u : ι → Set Y} (hu : ∀ i, IsOpen (u i)) {f : X → Y} (hu' : range f ⊆ ⋃ i, u i)
    (hf : ∀ i, IsOpen (f ⁻¹' u i)) :
    IsInducing f ↔ ∀ i, ∃ f', IsInducing f' ∧ (f ⁻¹' u i).EqOn f f' ∧ f' ⁻¹' u i = f ⁻¹' u i := by
  refine ⟨fun hf' i ↦ ⟨f, hf', eqOn_refl _ _, rfl⟩,
    fun hf' ↦ ?_⟩
  refine (isInducing_iff _).2 <| le_antisymm (continuous_iff_le_induced.1 ?_) fun v hv ↦ ?_
  · rw [← continuousOn_univ, ← preimage_range (f := f)]
    refine .mono ?_ <| preimage_mono hu'
    rw [preimage_iUnion]
    refine (continuousOn_iUnion_iff_of_isOpen hf).2 fun i ↦ ?_
    obtain ⟨f', hf'⟩ := hf' i
    exact hf'.1.continuous.continuousOn.congr hf'.2.1
  · rw [isOpen_induced_iff]
    replace hv := fun i ↦ hv.inter (hf i)
    choose f' hf' using hf'
    replace hv := fun i ↦  (hf' i).1.isOpen_iff.1 (hv i)
    choose w hw using hv
    refine ⟨⋃ i, u i ∩ w i, isOpen_iUnion fun i ↦ (hu i).inter (hw i).1, ?_⟩
    rw [preimage_iUnion, ← inter_univ v, ← show f ⁻¹' ⋃ i, u i = univ from ?_,
      preimage_iUnion, inter_iUnion]
    · refine iUnion_congr fun i ↦ ?_
      rw [preimage_inter, (hf' i).2.1.inter_preimage_eq (w i), (hw i).2, ← (hf' i).2.2]
      simp
    · rw [← univ_subset_iff, ← preimage_range (f := f)]
      exact preimage_mono hu'

/-- TODO: move -/
@[fun_prop]
lemma Topology.IsInducing.prodMk_of_left {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} (hf : IsInducing f) {g : X → Z} (hg : Continuous g) :
    IsInducing fun x ↦ (f x, g x) :=
  .of_comp (hf.continuous.prodMk hg) continuous_fst hf

/-- TODO: move -/
@[fun_prop]
lemma Topology.IsInducing.prodMk_of_right {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} (hf : Continuous f) {g : X → Z} (hg : IsInducing g) :
    IsInducing fun x ↦ (f x, g x) :=
  .of_comp (hf.prodMk hg.continuous) continuous_snd hg

/-- TODO: move -/
lemma Bundle.Trivialization.bijOn_preimage_proj {B F Z : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj) {s : Set B}
    (hs : s ⊆ e.baseSet) : (proj ⁻¹' s).BijOn e (Prod.fst ⁻¹' s) := by
  convert! e.bijOn.subset_right (r := Prod.fst ⁻¹' s) (by grind [e.target_eq])
  ext x
  refine ⟨fun hx ↦ ?_, fun ⟨hx, hx'⟩ ↦ ?_⟩
  · suffices h : x ∈ e.source by simpa [h]
    grw [hs] at hx
    simpa [e.source_eq]
  · simpa [hx] using hx'

/-- TODO: move -/
lemma Bundle.Trivialization.bijOn_symm_preimage_fst {B F Z : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj) {s : Set B}
    (hs : s ⊆ e.baseSet) : (Prod.fst ⁻¹' s).BijOn e.toOpenPartialHomeomorph.symm (proj ⁻¹' s) := by
  have h₁ : proj ⁻¹' s ⊆ e.source := by grind [e.source_eq]
  have h₂ : Prod.fst ⁻¹' s ⊆ e.target := by grind [e.target_eq]
  convert! e.toOpenPartialHomeomorph.symm.bijOn.subset_left (r := Prod.fst ⁻¹' s) (by
    grind [OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source, e.target_eq])
  have h := OpenPartialHomeomorph.IsImage.of_image_eq (e := e.toOpenPartialHomeomorph)
    (s := proj ⁻¹' s) (t := Prod.fst ⁻¹' s) <| by
      simp [inter_eq_right.2 h₁, inter_eq_right.2 h₂, (e.bijOn_preimage_proj hs).image_eq]
  simpa [inter_eq_right.2 h₁, inter_eq_right.2 h₂] using h.symm.image_eq.symm

/-- A variant of `IsInducing.of_comp` that only requires `g` to be continuous on the range of `f`
instead of globally.

TODO: move -/
lemma Topology.IsInducing.of_comp_of_continuousOn {X Y Z : Type*} {f : X → Y} {g : Y → Z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (hf : Continuous f) (hg : ContinuousOn g (range f)) (hgf : IsInducing (g ∘ f)) : IsInducing f :=
  subtypeVal.comp <| of_comp (hf.codRestrict (s := range f) (by simp))
    (continuousOn_iff_continuous_restrict.1 hg) hgf

/-- A relative version of `IsOpen.continuousOn_iff`.

TODO: move, clean up -/
lemma IsOpen.continuousOn_inter_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {u : Set X} (hu : IsOpen u) {f : X → Y} {s : Set X} :
    ContinuousOn f (s ∩ u) ↔ ∀ x ∈ s ∩ u, ContinuousWithinAt f s x :=
  forall₂_congr fun _ hx ↦ continuousWithinAt_congr_set <|
    (hu.eventually_mem hx.2).mono fun _ hx' ↦ Iff.eq ⟨fun hx'' ↦ hx''.1, fun hx'' ↦ ⟨hx'', hx'⟩⟩

/-- A relative version of `ContinuousOn.union_of_isOpen`.

TODO: move, clean up -/
lemma ContinuousOn.inter_union_of_isOpen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s u v} (hfu : ContinuousOn f (s ∩ u)) (hfv : ContinuousOn f (s ∩ v))
    (hu : IsOpen u) (hv : IsOpen v) : ContinuousOn f (s ∩ (u ∪ v)) := by
  rw [hu.continuousOn_inter_iff] at hfu
  rw [hv.continuousOn_inter_iff] at hfv
  rintro x ⟨hx, hx' | hx'⟩
  · exact (hfu x ⟨hx, hx'⟩).mono inter_subset_left
  · exact (hfv x ⟨hx, hx'⟩).mono inter_subset_left

attribute [local fun_prop] FiberBundle.continuous_proj in
/-- The covering homotopy theorem: every fibre bundle over `B × I` is isomorphic to the pullback of
itself along the map `B × I → B × I` sending `(b, t)` to `(b, 1)`. This version of the lemma takes
in an explicit choice of trivialisations as well as a predicate `P` that the transitions between
trivialisations are required to fulfill fibrewise, and produces an isomorphism that also fulfills
the predicate fibrewise. In this way the lemma can be specialised to fibre bundles to produce fibre
bundle isomorphisms, to principal bundles to produce principal bundle isomorphisms, to vector
bundles to produce vector bundle isomorphisms and so on.

The constructed isomorphism is not canonical; we wrap it in an existential statement to not surface
the details of its construction, and because nothing interesting could be said about this specific
choice of isomorphism anyway.

TODO: rename, get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma coveringHomotopyLemma_of_prop (E : B × I → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [∀ b, Zero (E b)] (P : ∀ x x', (E x → E x') → Prop)
    (hP : ∀ x x' x'' g g', P x x' g → P x' x'' g' → P x x'' (g' ∘ g))
    {u : ℕ → Set B} (hu : NumerableCover u)
    (e : ℕ → Trivialization F (π F E)) (he : ∀ n, (e n).baseSet = u n ×ˢ univ)
    (he' : ∀ n m, ∀ x ∈ (e n).baseSet, ∀ x' ∈ (e m).baseSet,
      P x x' (fun x : E x ↦ (e m).symm x' (e n x).2)) :
    ∃ e : E ≃ₜᶠ[F, F] (ContinuousMap.prodMap (.id B) (.const I 1)) *ᵖ E, ∀ x, P x _ (e x) := by
  /- It suffices to give a map `g : TotalSpace F E → TotalSpace F E` whose underlying map is
  `fun x ↦ (x, 1)` and that becomes an isomorphism when viewed as a map to the pullback. The
  advantage of this formulation is that the type of the map we need to give no longer directly
  involves `fun x ↦ (x, 1)`, so we can more easily construct it as a limit of maps with different
  underlying maps. -/
  suffices h : ∃ g : TotalSpace F E → TotalSpace F E, (∀ x, (g x).proj = (x.proj.1, 1)) ∧
      (∀ x : B × I, BijOn g (π F E ⁻¹' {x}) (π F E ⁻¹' {(x.1, 1)})) ∧
        IsInducing (fun x ↦ (x.proj, g x)) ∧ ∀ x, ∃ g', P x (x.1, 1) g' ∧ ∀ x', g' x' = g x' by
    have ⟨g, hg, hg', hg'', hg'''⟩ := h
    have hg'''' : Continuous g := continuous_snd.comp hg''.continuous
    refine ⟨.ofHomeomorph ((Equiv.ofBijective (ContinuousBundleHom.pullbackEquiv <| .ofContinuousMap
      (f := fun x ↦ (x.1, 1)) ⟨g, hg''''⟩ hg).toContinuousMap ?_).toHomeomorphOfIsInducing ?_)
      fun x ↦ ?_, fun x ↦ ?_⟩
    · refine (TotalSpace.map_bijective_iff _ _ _ _ bijective_id).2 fun x ↦ ?_
      rw [← Function.Bijective.of_comp_iff' (α := ((fun x ↦ (x.1, 1)) *ᵖ E) (id x))
        (β := E (x.1, 1)) (f := by exact fun x ↦ x) (by exact bijective_id) _]
      refine TotalSpace.map_bijOn_iff F E F E (f := fun x ↦ (x.1, 1)) |>.1 ?_
      refine (hg' x).congr fun x' hx' ↦ ?_
      ext1
      · simp [hg]
      · exact (cast_heq _ _).symm
    · rw [← (inducing_pullbackTotalSpaceEmbedding _ _ _).of_comp_iff]
      convert hg'' using 2 with ⟨_, _⟩
      ext1
      · simp
      · ext1
        · simp [hg]
        · exact cast_heq _ _
    · erw [Equiv.toHomeomorphOfIsInducing_apply]
      simp
    · have ⟨g', hg'''⟩ := hg''' x
      convert! hg'''.1 using 1
      ext x'
      refine (TotalSpace.mk_inj (F := F) (E := E)).1 ?_
      convert! (hg'''.2 x').symm using 1
      ext1
      · exact (hg ⟨x, x'⟩).symm
      · simp only [TotalSpace.mk', ContinuousBundleIso.ofHomeomorph, ContinuousBundleIso.ofHoms,
          ContinuousBundleIso.coe_mk, ContinuousBundleHom.ofContinuousMap,
          ContinuousBundleHom.coeFn_mk, Equiv.toHomeomorphOfIsInducing, ContinuousMap.coe_mk,
          ContinuousMap.coe_coe]
        refine (cast_heq_iff_heq _ _ _).2 HEq.rfl
  /- Since `u` is numerable, we can obtain a bump covering that is subordinate to it. For later
  convenience we first modify `u` such that `u 0` is empty. -/
  wlog hu₀ : u 0 = ∅ generalizing u e with h
  · refine h (u := fun n ↦ n.rec ∅ (fun n _ ↦ u n)) (hu.mono' fun n ↦ ⟨n + 1, by simp⟩)
      (fun n ↦ n.rec ((e 0).restrOpen ∅ isOpen_empty) fun n _ ↦ e n)
      (fun n ↦ by cases n <;> simp [Trivialization.restrOpen, he]) (fun n m ↦ ?_) (by simp)
    exact n.rec (by simp [Trivialization.restrOpen]) fun n _ ↦
      m.rec (by simp [Trivialization.restrOpen]) fun m _ ↦ he' n m
  have hu' n : IsOpen (u n) := by
    rw [← fst_image_prod (α := I) (u n) univ_nonempty, ← he]
    exact isOpenMap_fst _ (e n).open_baseSet
  have ⟨f, hf⟩ := hu.exists_bumpCovering
  have hf₀ : f 0 = 0 := by have := subset_closure.trans <| hf 0; ext1; simp_all
  /- Let `w n` be the subset of `B` where `f n` reaches its maximum, `w' n` the union of all `w m`
  with `m ≤ n`, and `w'' n` the interior of the correspond subset of `B × I`. -/
  let w n := f n ⁻¹' {1}
  have hw : ⋃ n, interior (w n) = univ := by
    refine iUnion_eq_univ_iff.2 fun x ↦ ⟨f.ind x trivial, ?_⟩
    simpa [w, mem_interior_iff_mem_nhds, Filter.EventuallyEq, Filter.eventually_iff, preimage]
      using f.eventuallyEq_one x trivial
  let w' n := ⋃ m ≤ n, w m
  let w'' n : Set (B × I) := interior (w' n) ×ˢ univ
  have hw'' n : IsOpen (w'' n) := by simpa [w''] using isOpen_interior.prod isOpen_univ
  have hw''' n m (h : n ≤ m) : w'' n ⊆ w'' m := by
    unfold w'' w' w
    gcongr 2
    exact biUnion_mono (fun _ h' ↦ LE.le.trans h' h) (by simp)
  have hw'''' x : x ∈ w'' (f.ind x.1 trivial) := by
    simp only [w'', mem_prod, mem_univ, and_true, w']
    refine interior_mono (s := w (f.ind x.1 trivial)) (subset_biUnion_of_mem
      (by exact le_refl <| f.ind x.1 trivial)) ?_
    simpa [w, mem_interior_iff_mem_nhds, Filter.EventuallyEq, Filter.eventually_iff, preimage]
      using f.eventuallyEq_one _ trivial
  /- Let `f' n` be the supremum of all `f' m` with `m ≤ n`, and `f'' n` be the map
  `B × I → B × I` given by `fun x ↦ (x.1, x.2 ⊔ f' n x.1)`. -/
  let f' n := (Finset.Iic n).sup' Finset.nonempty_Iic fun m ↦ f m
  let f'' n : C(B × I, B × I) := .prodMk .fst <| .snd ⊔ .comp
    ⟨_, (map_continuous (f' n)).subtype_mk (by
      simp [f', f.nonneg, f.le_one, -Finset.mem_Iic, Finset.nonempty_Iic.exists_mem])⟩ .fst
  have hf'' (n m : ℕ) (h : n ≤ m) (x : B × I) (hx : f n x.1 = 1) : f'' m x = (x.1, 1) := by
    refine Prod.ext rfl <| unitInterval.one_le_iff.1 ?_
    suffices h : 1 ≤ (f' m) x.1 by simp [f'', ← Subtype.coe_le_coe, h]
    simp only [f', ContinuousMap.coe_sup', Finset.sup'_apply, Finset.le_sup'_iff, Finset.mem_Iic]
    grind
  have hf''' n x (hx : x ∈ w'' n) : f'' n x = (x.1, 1) := by
    have ⟨m, hm, hx⟩ := mem_iUnion₂.1 <| interior_subset hx.1
    exact hf'' m n hm x hx
  have hf'''' n x (hx : x.1 ∉ tsupport (f (n + 1))) : f'' (n + 1) x = f'' n x := by
    suffices h : f' n x.1 = f' (n + 1) x.1 by simp [f'', h]
    unfold f'
    rw! [← Finset.Iio_insert (n + 1), Finset.Iio_add_one_eq_Iic]
    rw [Finset.sup'_insert Finset.nonempty_Iic, ContinuousMap.sup_apply,
      ContinuousMap.coe_sup', Finset.sup'_apply, show (f (n + 1) x.1) = 0 by
        simpa [f''] using notMem_subset subset_closure hx, max_eq_right]
    exact Finset.le_sup'_of_le _ (b := 0) (by simp) (f.nonneg _ _)
  have hf''''' n x : f'' (n + 1) (f''  n x) = f'' (n + 1) x := by
    suffices h : f' n x.1 ≤ f' (n + 1) x.1 by simp [f'', max_assoc, h]
    simp [f', ← Finset.Iio_insert (n + 1), Finset.Iio_add_one_eq_Iic]
  have hf''₀ : f'' 0 = .id _ := by
    ext1; simp [f'', f', hf₀, (show (⊥ : ℕ) = 0 from rfl) ▸ Finset.Iic_bot]
  /- It will suffices to give a sequence of maps `g n : TotalSpace F E → TotalSpace F E` whose
  underlying maps are the maps `f'' n`, that become isomorphisms when viewed as maps to the
  pullback bundle, and that stabilise on the sets `w'' n` as the maps `f'' n` do. -/
  suffices h : ∃ g : ℕ → TotalSpace F E → TotalSpace F E, ∀ n, (∀ x, (g n x).proj = f'' n x.proj) ∧
      (∀ x : B × I, BijOn (g n) (π F E ⁻¹' {x}) (π F E ⁻¹' {f'' n x})) ∧
        IsInducing (fun x ↦ (x.proj, g n x)) ∧
          (∀ x, ∃ g', P x (f'' n x) g' ∧ ∀ x', g' x' = g n x') ∧
            (π F E ⁻¹' w'' n).EqOn (g n) (g (n + 1)) by
    obtain ⟨g, hg⟩ := h
    have hg' n m (h : n ≤ m) : (π F E ⁻¹' w'' n).EqOn (g n) (g m) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      refine k.rec ?_ fun k hk ↦ ?_
      · simp [Set.eqOn_refl]
      · rw [k.succ_eq_add_one, ← add_assoc]
        exact hk.trans <| (hg _).2.2.2.2.mono <| preimage_mono <| hw''' _ _ <| by simp
    have hg'' n m x (hxn : x.proj ∈ w'' n) (hxm : x.proj ∈ w'' m) : g n x = g m x := by
      rw [hg' n (n + m) (by simp) hxn, hg' m (n + m) (by simp) hxm]
    refine ⟨fun x ↦ g (f.ind x.proj.1 trivial) x, fun x ↦ ?_, ?_, ?_, fun x ↦ ?_⟩
    · simp only [hg, hf'' (f.ind x.proj.1 trivial) _ le_rfl x.proj (by simp [f.ind_apply])]
    · intro x
      rw [← hf'' (f.ind x.1 trivial) _ le_rfl x (by simp [f.ind_apply])]
      refine ((hg (f.ind x.1 trivial)).2.1 x).congr ?_
      rintro x rfl
      exact (hg' _ _ (Nat.le_add_right _ _) (hw'''' _)).trans
        (hg' _ _ (Nat.le_add_left _ _) (hw'''' _)).symm
    · refine (isInducing_iff_of_open_cover (u := fun n ↦ w'' n ×ˢ (π F E ⁻¹' w'' n))
        (fun n ↦ ?_) ?_ (fun n ↦ ?_)).2 fun n ↦ ?_
      · exact (hw'' n).prod <| (hw'' n).preimage <| IsFiberBundle.continuous_proj F E
      · refine range_subset_iff.2 fun x ↦ mem_iUnion_of_mem (f.ind x.proj.1 trivial) ⟨hw'''' _, ?_⟩
        simpa [hg, f'', w''] using (hw'''' x.proj).1
      · suffices IsOpen {x : TotalSpace F E | x.proj.1 ∈ interior (w' n)} by
          simpa [preimage, w'', hg, f'']
        exact isOpen_interior.preimage <| continuous_fst.comp <| IsFiberBundle.continuous_proj F E
      · refine ⟨_, (hg n).2.2.1, fun x hx ↦ ?_, ?_⟩
        · simp only [mem_preimage, mem_prod, Prod.mk.injEq, true_and] at hx ⊢
          exact hg'' _ _ _ (hw'''' _) hx.1
        · ext x
          refine and_congr_right_iff.2 fun hx ↦ ?_
          simp [hx, hg, hf''', hw'''']
    · rw [← hf''' _ _ (hw'''' x)]
      exact (hg (f.ind x.1 trivial)).2.2.2.1 x
  /- By induction, to construct the sequence of maps it suffices to show that given a valid map for
  any `n` we can construct a valid map for `n + 1`. The base case `0` is trivial thanks to us
  having chosen `u` such that `u 0 = ∅`, which implies `f'' 0 = id`. -/
  suffices h : ∀ (n : ℕ) (g : TotalSpace F E → TotalSpace F E), (∀ x, (g x).proj = f'' n x.proj) →
      (∀ x, BijOn g (TotalSpace.proj ⁻¹' {x}) (TotalSpace.proj ⁻¹' {f'' n x})) →
        (IsInducing fun x ↦ (x.proj, g x)) → (∀ x, ∃ g', P x (f'' n x) g' ∧ ∀ x', g' x' = g x') →
          ∃ g' : TotalSpace F E → TotalSpace F E, (∀ x, (g' x).proj = f'' (n + 1) x.proj) ∧
            (∀ x, BijOn g' (TotalSpace.proj ⁻¹' {x}) (TotalSpace.proj ⁻¹' {f'' (n + 1) x})) ∧
              (IsInducing fun x ↦ (x.proj, g' x)) ∧
                (∀ x, ∃ g'', P x (f'' (n + 1) x) g'' ∧ ∀ x', g'' x' = g' x') ∧
                  EqOn g g' (TotalSpace.proj ⁻¹' w'' n) by
    choose g hg using h
    let g' : (n : ℕ) → {g : TotalSpace F E → TotalSpace F E | (∀ x, (g x).proj = f'' n x.proj) ∧
        (∀ x, BijOn g (TotalSpace.proj ⁻¹' {x}) (TotalSpace.proj ⁻¹' {f'' n x})) ∧
          (IsInducing fun x ↦ (x.proj, g x)) ∧
            (∀ x, ∃ g', P x (f'' n x) g' ∧ ∀ x', g' x' = g x')} :=
      Nat.rec ⟨id, by simp [hf''₀], fun x ↦ by simp [hf''₀, bijOn_id], by fun_prop, fun x ↦ by
          suffices hP' : P x x id by rw [hf''₀, ContinuousMap.id_apply]; use id; simp [hP']
          have ⟨n, hn⟩ := iUnion_eq_univ_iff.1 hu.cover x.1
          convert he' n n x (by simp [he, hn]) x (by simp [he, hn])
          simp [show x ∈ (e n).baseSet by simp [he, hn]]⟩
        fun n ⟨g', hg'⟩ ↦ ⟨g n g' hg'.1 hg'.2.1 hg'.2.2.1 hg'.2.2.2, by
          simp [hg n g' hg'.1 hg'.2.1 hg'.2.2.1 hg'.2.2.2]⟩
    refine ⟨fun n ↦ (g' n).1, fun n ↦
      ⟨(g' n).2.1, (g' n).2.2.1, (g' n).2.2.2.1, (g' n).2.2.2.2, ?_⟩⟩
    exact (hg n (g' n).1 (g' n).2.1 (g' n).2.2.1 (g' n).2.2.2.1 (g' n).2.2.2.2).2.2.2.2
  /- Finally, given a map `g` for `n` we can construct a map `g'` for `n + 1` out of it by moving
  the points within `π F E ⁻¹' u (n + 1) ×ˢ univ` from the fibers over `f'' n` to the fibers over
  `f'' (n + 1)` using some trivialisation `e` on `u (n + 1) ×ˢ univ`, while leaving it unchanged
  everywhere else. -/
  intro n g hg hg' hg'' hg'''
  have hg'''' : Continuous g := hg''.continuous.snd
  classical
  refine ⟨(fun x ↦ if x.proj.1 ∈ u (n + 1) then
    ⟨f'' (n + 1) x.proj, (e (n + 1)).symm _ (e (n + 1) x).2⟩ else x) ∘ g,
      fun x ↦ ?_, fun x ↦ ?_, ?_, fun x ↦ ?_, fun x hx ↦ ?_⟩
  · by_cases hx : (g x).proj.1 ∈ u (n + 1)
    · simp [↓hx, hg, hf''''']
    · suffices f'' n x.proj = f'' (n + 1) x.proj by simpa [↓hx, hg]
      exact (hf'''' _ _ <| notMem_subset (hf (n + 1)) <| by rwa [hg] at hx).symm
  · refine .comp ?_ (hg' _)
    by_cases hx : x.1 ∈ u (n + 1)
    · refine .congr (f₁ := (e (n + 1)).toOpenPartialHomeomorph.symm ∘
          (fun x' ↦ (f'' (n + 1) x, x'.2)) ∘ e (n + 1)) ?_
        (fun x' hx' ↦ by
          simp only [mem_preimage, mem_singleton_iff] at hx'
          simp only [↓reduceIte, show x'.proj.1 ∈ u (n + 1) by simp [hx', f'', hx]]
          rw [(e _).mk_symm (by simp [he, f'', hx', hx]), hx', hf''''', comp_apply, comp_apply])
      refine ((e _).bijOn_symm_preimage_fst (by simp [he, f'', hx])).comp <| .comp ?_ <|
        (e _).bijOn_preimage_proj (by simp [he, f'', hx])
      refine ⟨fun _ _ ↦ by simp, fun x₁ hx₁ x₂ hx₂ h ↦ ?_, fun x' hx' ↦ ?_⟩
      · simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, true_and] at hx₁ hx₂ h
        exact Prod.ext (hx₁.trans hx₂.symm) h
      · simp only [mem_preimage, mem_singleton_iff] at hx'
        exact ⟨(f'' n x, x'.2), rfl, Prod.ext hx'.symm rfl⟩
    · rw [hf'''' _ _ <| notMem_subset (hf (n + 1)) hx]
      refine .congr (bijOn_id _) fun x' hx' ↦ ?_
      suffices h : x'.proj.1 ∉ u (n + 1) by simp [h]
      simp at hx'
      simp [hx', f'', hx]
  · refine .of_comp_of_continuousOn (Z := (B × ↑I) × TotalSpace F E) (g := fun x ↦
      (x.1, if x.1.1 ∈ u (n + 1) then ⟨f'' n x.1, (e (n + 1)).symm _ (e (n + 1) x.2).2⟩ else x.2))
        ?_ ?_ ?_
    · rw [← continuousOn_univ, ← preimage_univ (f := Prod.fst ∘ π F E),
        show univ = u (n + 1) ∪ (tsupport (f (n + 1)))ᶜ by grind [hf (n + 1)], preimage_union]
      refine .union_of_isOpen ?_ ?_ ((hu' (n + 1)).preimage (by fun_prop))
        ((isClosed_tsupport _).isOpen_compl.preimage (by fun_prop))
      · refine .congr (f := fun x ↦ (x.proj,
          ⟨_, (e (n + 1)).symm (f'' (n + 1) (g x).proj) (e (n + 1) (g x)).2⟩)) ?_ fun x hx ↦ ?_
        · refine .prodMk (by fun_prop) ?_
          refine (e _).continuousOn_symm.comp (f := fun x ↦
            (f'' (n + 1) (g x).proj, (e _ (g x)).2)) ?_ (fun x hx ↦ by simpa [he, hg, f''] using hx)
          · refine .prodMk (by fun_prop) <| continuous_snd.comp_continuousOn ?_
            refine (e _).continuousOn.comp hg''''.continuousOn fun x hx ↦ ?_
            simpa [(e _).source_eq, he, hg, f''] using hx
        · simp [show (g x).proj.1 ∈ u (n + 1) by simpa [hg, f'', hx], ↓reduceIte]
      · refine hg''.continuous.continuousOn.congr fun x hx ↦ ?_
        simp only [preimage_compl, mem_compl_iff, mem_preimage, comp_apply] at hx
        simp only [comp_apply, Prod.mk.injEq, ite_eq_right_iff, true_and]
        intro _
        rw [hf'''' n (g x).proj (by simpa [hg, f'']), hg,
          show f'' n (f'' n x.proj) = f'' n x.proj by simp [f''],
          ← hg, (e _).symm_proj_apply _ (by simpa [he])]
    · refine .mono (s := {x | x.2.proj = f'' (n + 1) x.1}) ?_ ?_
      · rw [← inter_univ {x : (B × ↑I) × TotalSpace F E | x.2.proj = f'' (n + 1) x.1},
          ← preimage_univ (f := Prod.fst ∘ Prod.fst),
          show univ = u (n + 1) ∪ (tsupport (f (n + 1)))ᶜ by grind [hf (n + 1)], preimage_union]
        refine .inter_union_of_isOpen ?_ ?_ ((hu' (n + 1)).preimage (by fun_prop))
          ((isClosed_tsupport _).isOpen_compl.preimage (by fun_prop))
        · refine .congr (f := fun x ↦ ⟨x.1, (e (n + 1)).symm (f'' n x.1) (e (n + 1) x.2).2⟩) ?_
            fun x hx ↦ by simp [show x.1.1 ∈ u (n + 1) by simpa using hx.2]
          refine .prodMk (by fun_prop) <| (e _).continuousOn_symm.comp
            (f := fun x : (B × ↑I) × TotalSpace F E ↦ ((f'' n) x.1, (e _ x.2).2)) ?_
            fun x hx ↦ by simpa [f'', he] using hx.2
          refine .prodMk (by fun_prop) <| continuous_snd.comp_continuousOn ?_
          refine (e _).continuousOn.comp (by fun_prop) fun x hx ↦ ?_
          simpa [(e _).source_eq, he, (Prod.ext_iff.1 hx.1).1, f''] using hx.2
        · refine .congr continuousOn_id fun x hx ↦ Prod.ext rfl <| ite_eq_right_iff.2 fun hx' ↦ ?_
          simp only [preimage_compl, mem_inter_iff, mem_setOf_eq, mem_compl_iff, mem_preimage,
            comp_apply] at hx
          rw [← hf'''' _ _ hx.2, ← hx.1, Trivialization.symm_proj_apply]
          simp [he, hx.1, f'', hx']
      · refine range_subset_iff.2 fun x ↦ ?_
        by_cases hx : x.proj.1 ∈ u (n + 1)
        · simp [hg, show (f'' n x.proj).1 = x.proj.1 by simp [f''], hx, hf''''']
        · simp [hg, show (f'' n x.proj).1 = x.proj.1 by simp [f''], hx,
            hf'''' _ _ (notMem_subset (hf (n + 1)) hx)]
    · convert hg'' using 1
      ext1 x
      simp only [comp_apply, Prod.mk.injEq, true_and]
      rw [show (g x).proj.1 = x.proj.1 by simp [hg, f'']]
      by_cases h : x.proj.1 ∈ u (n + 1)
      · simp only [h, ↓reduceIte]
        rw [(e _).apply_mk_symm (by simp [hg, he, f'', h]), (e _).mk_symm (by simp [he, f'', h])]
        rw [show ((f'' n) x.proj, (e (n + 1) (g x)).2) = e (n + 1) (g x) by
          refine Prod.ext ?_ rfl
          simp [hg, show g x ∈ (e (n + 1)).source by simp [(e _).source_eq, he, hg, f'', h]]]
        rw [(e _).symm_apply_apply (by simp [(e _).source_eq, he, hg, f'', h])]
      · simp [h]
  · have ⟨g', hg'''⟩ := hg''' x
    by_cases hx : x.1 ∈ u (n + 1)
    · simp only [comp_apply, hg, show ((f'' n) x).1 ∈ u (n + 1) by simpa [f''] using hx,
        ↓reduceIte]
      refine ⟨_, hP _ _ _ _ _ hg'''.1 <| he' (n + 1) (n + 1)
        (f'' n x) (by simp [f'', he, hx]) (f'' (n + 1) x) (by simp [f'', he, hx]), fun x' ↦ ?_⟩
      rw [hg, hf''''']
      simp [hg''']
    · rw [hf'''' _ _ <| notMem_subset (hf (n + 1)) hx]
      refine ⟨g', hg'''.1, fun x' ↦ ?_⟩
      simp [hg, show ((f'' n) x).1 ∉ u (n + 1) by simpa [f''] using hx, hg''']
  · simp only [comp_apply, right_eq_ite_iff, hg, mem_preimage] at hx ⊢
    intro hx'
    rw [hg, hf''' n x.proj hx, hf''' (n + 1) (x.proj.1, 1) <| hw''' n _ (by simp) hx,
      ← hf''' n x.proj hx, ← hg, (e _).symm_apply_apply_mk ?_]
    simp [he, hg, hx']

/-- The covering homotopy theorem for fibre bundles: every numerable fibre bundle over `B × I` is
isomorphic to the pullback of itself along the map `B × I → B × I` sending `(b, t)` to `(b, 1)`.

TODO: rename, get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma NumerableBundle.coveringHomotopyLemma (E : B × I → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [∀ b, Zero (E b)] [NumerableBundle F E] :
    Nonempty (E ≃ₜᶠ[F, F] (ContinuousMap.prodMap (.id B) (.const I 1)) *ᵖ E) := by
  have ⟨u, hu⟩ := exists_countable_isTrivialOn_cover_prod_unitInterval F E
  choose e he using fun n ↦
    (isTrivialOn_iff_exists_trivialization _ _ <| (hu.2.2 n).1.prod isOpen_univ).1 (hu.2.2 n).2
  simpa using coveringHomotopyLemma_of_prop F E (fun _ _ _ ↦ True) (by simp) hu.2.1 e he (by simp)

/-- Pullbacks of a numerable bundle along homotopic maps are isomorphic.

The isomorphism is not canonical; we wrap it in `Nonempty` to not surface the details of its
construction, and because nothing interesting could be said about this specific choice of
isomorphism anyway. For example, it does not preserve any extra structure that `E` carries -
analogous lemmas for things like vector bundles and principal bundles have to be proven separately.

TODO: get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma NumerableBundle.pullbackIsoPullback [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [(b : B) → Zero (E b)] [NumerableBundle F E] {f₁ f₂ : C(B', B)}
    (h : f₁.Homotopic f₂) : Nonempty (f₁ *ᵖ E ≃ₜᶠ[F, F] f₂ *ᵖ E) := by
  obtain ⟨H⟩ := h
  replace ⟨H, hH₁, hH₂⟩ :
      ∃ H : C(B' × I, B), (∀ b', H (b', 0) = f₁ b') ∧ (∀ b', H (b', 1) = f₂ b') := by
    exact ⟨.comp H .prodSwap, by simp⟩
  have _ b : Zero ((⇑H *ᵖ E) b) := inferInstanceAs (Zero (E _))
  have ⟨e⟩ := NumerableBundle.coveringHomotopyLemma F (H *ᵖ E)
  rw [show Equiv.refl (B' × I) = Homeomorph.refl (B' × I) from rfl] at e
  replace e := e.pullbackCongr (.prodMk (.id B') (.const B' 0)) (.prodMk (.id B') (.const B' 0))
    (.refl B') (by simp)
  rw [← show Equiv.refl B' = Homeomorph.refl B' from rfl] at e
  have : CompTriple (Equiv.refl B').symm (Equiv.refl B') (Equiv.refl B') := ⟨by simp⟩
  have : CompTriple (Equiv.refl B') (Equiv.refl B') (Equiv.refl B') := ⟨by simp⟩
  replace e := (ContinuousBundleIso.pullbackPullbackIso _ _).symm.trans e
    |>.trans (.pullbackPullbackIso _ _) |>.trans (.pullbackPullbackIso _ _)
  convert Nonempty.intro e <;> ext x <;> simp [hH₁, hH₂]

/-- TODO: move -/
lemma nullhomotopic_of_contractibleSpace_dom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace X] {f : C(X, Y)} : f.Nullhomotopic :=
  (id_nullhomotopic X).comp_right f

/-- TODO: move -/
lemma nullhomotopic_of_contractibleSpace_cod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ContractibleSpace Y] {f : C(X, Y)} : f.Nullhomotopic :=
  (id_nullhomotopic Y).comp_left f

/-- Every numerable fibre bundle on a contractible base space is trivial. -/
lemma IsTrivial.of_contractibleSpace [∀ b, TopologicalSpace (E b)] [IsFiberBundle F E]
    [(b : B) → Zero (E b)] [NumerableBundle F E] [ContractibleSpace B] : IsTrivial F E := by
  rw [← isTrivialOn_univ, IsTrivialOn]
  have ⟨b, h⟩ := nullhomotopic_of_contractibleSpace_cod
    (f := (ContinuousMap.subtypeVal : C((Set.univ : Set B), B)))
  have ⟨e⟩ := NumerableBundle.pullbackIsoPullback F E h
  have : CompTriple (Equiv.refl (univ : Set B)) (Equiv.refl (univ : Set B))
    (Homeomorph.refl (univ : Set B)) := ⟨rfl⟩
  replace e := e.trans <| .pullbackConstIsoTrivial (F := F) (E := E) (B' := (univ : Set B)) b
  rw [show (Homeomorph.refl (univ : Set B)).toEquiv = Homeomorph.refl (univ : Set B) from rfl] at e
  exact (e.isTrivial_iff _).2 <| isTrivial_trivial _
