/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.IndexedJoin
import ClassifyingBundles.PrincipalBundle

/-! # Universal bundles
In this file we define universal principal bundles, i.e. numerable `G`-principal bundles such that
for every other numerable `G`-principal bundle is isomorphic to the pullback of the universal bundle
along up to homotopy exactly one map.

For now we are letting everything in this file live in the same universe `u`, and leaving it for
later to figure out how exactly `IsUniversalBundle` should be stated in a more universe-polymorphic
way if needed.
-/

open Bundle Topology

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (F : Type u) [TopologicalSpace F] {B : Type u} [TopologicalSpace B]
  (E : B → Type u) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (Bundle.TotalSpace F E)]
  [Torsor G F] [IsTopologicalTorsor F]
  [∀ b, Torsor G (E b)] [∀ b, IsTopologicalTorsor (E b)]
  {B' : Type u} [TopologicalSpace B']
  (E' : B' → Type u) [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (Bundle.TotalSpace F E')]
  [∀ b, Torsor G (E' b)] [∀ b, IsTopologicalTorsor (E' b)]

/-- We say that a `G`-principal bundle `E` is universal if every other numerable
`G`-principal bundle is isomorphic to a pullback of `E`, and any two maps into the base space `B`
of `E` are homotopic if the pullbacks of `E` along them are isomorphic.

In other words, a numerable `G`-principal bundle `E` over `B` is universal if for any other space
`B'` the map from homotopy classes of maps `B' → B` to isomorphism classes of numerable principal
bundles over `B'` given by pullback is bijective. We do not state the definition directly in
this form because the API for bundles is written in unbundled form, and it would be inconvenient to
introduce e.g. the type of isomorphism classes of numerable `G`-principal bundles over `B'` just
for this definition.

TODO: figure out the optimal level of universe polymorphism for this. -/
class IsUniversalBundle : Prop extends IsPrincipalBundle G F E, NumerableBundle F E where
  /-- For other numerable `G`-principal bundle `E'`, there exists a map `f` that is classifying
  `E'` in the sense that `E'` is isomorphic to `f *ᵖ E`. -/
  exists_classifyingMap : ∀ (B' : Type u) [TopologicalSpace B'] (E' : B' → Type u)
    [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (Bundle.TotalSpace F E')]
    [IsFiberBundle F E'] [NumerableBundle F E'] [∀ b, Torsor G (E' b)]
    [∀ b, IsTopologicalTorsor (E' b)] [IsPrincipalBundle G F E'],
    ∃ f : C(B', B), Nonempty (E' ≃ₜᶠₑ[G; F, F] f *ᵖ E)
  /-- Any two maps into `B` are homotopic if the pullbacks of `E` along them are isomorphic. -/
  homotopic_of_iso : ∀ (B' : Type u) [TopologicalSpace B'] {f f' : C(B', B)}
    (_ : f *ᵖ E ≃ₜᶠₑ[G; F, F] f' *ᵖ E), f.Homotopic f'

namespace IsUniversalBundle

/-- Given a universal `G`-principal bundle `E` and another numerable `G`-principal bundle,
this is the unique-up-to-homotopy map `f : C(B', B)` for which `E'` is isomorphic to `f *ᵖ E`.

It is chosen nonconstructively here. -/
noncomputable def classifyingMap [IsUniversalBundle G F E]
    [IsPrincipalBundle G F E'] [NumerableBundle F E'] : C(B', B) :=
  (IsUniversalBundle.exists_classifyingMap (G := G) (F := F) (E := E) B' E').choose

/-- Given a universal `G`-principal bundle `E` and another numerable `G`-principal bundle,
this is a nonconstructive choice of isomorphism between `E'` and the pullback of `E` along
`classifyingMap G F E E'`. -/
noncomputable def isoPullbackClassifyingMap [IsUniversalBundle G F E]
    [IsPrincipalBundle G F E'] [NumerableBundle F E'] :
    E' ≃ₜᶠₑ[G; F, F] (classifyingMap G F E E') *ᵖ E :=
  (IsUniversalBundle.exists_classifyingMap (G := G) (F := F) (E := E) B' E').choose_spec.some

omit [IsTopologicalGroup G] in
/-- TODO: get rid of unnecessary `[∀ b, Zero (E b)]` assumptions -/
lemma classifyingMap_pullback_homotopic_comp [IsUniversalBundle G F E] [∀ b, Zero (E b)]
    [IsPrincipalBundle G F E'] [NumerableBundle F E'] [∀ b, Zero (E' b)]
    {B'' : Type u} [TopologicalSpace B''] (f : C(B'', B')) :
    (classifyingMap G F E (f *ᵖ E')).Homotopic ((classifyingMap G F E E').comp f) := by
  apply homotopic_of_iso (G := G) (F := F) (E := E)
  have : CompTriple (Homeomorph.refl B'') (Homeomorph.refl B'') (Homeomorph.refl B'') := ⟨rfl⟩
  refine .trans (φ₁ := Equiv.refl G) (e₁ := Homeomorph.refl B'') ?_ <| .pullbackPullbackIso _ _
  have e := (isoPullbackClassifyingMap G F E (f *ᵖ E')).symm
  rw [Equiv.refl_symm, Homeomorph.refl_symm] at e
  refine e.trans (φ₂ := Equiv.refl G) (e₂ := Homeomorph.refl B'') ?_
  exact .pullbackCongr (isoPullbackClassifyingMap G F E E') f f _ (by simp)

/-- The homotopy equivalence between the base spaces of two universal bundles given by the
classifying maps of the bundles with respect to each other. -/
noncomputable def homotopyEquiv [IsUniversalBundle G F E] [IsUniversalBundle G F E'] :
    ContinuousMap.HomotopyEquiv B B' where
  toFun := classifyingMap G F E' E
  invFun := classifyingMap G F E E'
  left_inv := by
    apply homotopic_of_iso (G := G) (F := F) (E := E)
    have _ : CompTriple (Homeomorph.refl B).symm (Homeomorph.refl B) (Homeomorph.refl B) := ⟨rfl⟩
    have _ b : Zero (E b) := ⟨Classical.arbitrary _⟩
    have _ b : Zero (((classifyingMap G F E E') *ᵖ E) b) := inferInstanceAs (Zero (E _))
    refine .trans (φ₂ := .refl G) (e₂ := .refl B) (.symm <| .pullbackPullbackIso _ _) ?_
    have _ : CompTriple (Homeomorph.refl B) (Homeomorph.refl B) (Homeomorph.refl B) := ⟨rfl⟩
    refine .trans (φ₂ := .refl G) (e₁ := .refl B) (e₂ := .refl B)
      (.pullbackCongr (isoPullbackClassifyingMap G F E E').symm (classifyingMap G F E' E)
        (classifyingMap G F E' E) _ (by simp)) ?_
    have _ b : Zero (E' b) := ⟨Classical.arbitrary _⟩
    refine (isoPullbackClassifyingMap G F E' E).symm.trans (φ₂ := .refl _) (e₂ := .refl _) ?_
    have : IsFiberBundle F (⇑(Homeomorph.refl B) *ᵖ E) :=
      IsFiberBundle.instPullbackCoeContinuousMap F E (f := toContinuousMap (Homeomorph.refl B))
    exact .symm <| .pullbackHomeomorph (.refl _)
  right_inv := by
    apply homotopic_of_iso (G := G) (F := F) (E := E')
    have _ : CompTriple (Homeomorph.refl B').symm (Homeomorph.refl B') (Homeomorph.refl B') := ⟨rfl⟩
    have _ b : Zero (E' b) := ⟨Classical.arbitrary _⟩
    have _ b : Zero (((classifyingMap G F E' E) *ᵖ E') b) := inferInstanceAs (Zero (E' _))
    refine .trans (φ₂ := .refl G) (e₂ := .refl B') (.symm <| .pullbackPullbackIso _ _) ?_
    have _ : CompTriple (Homeomorph.refl B') (Homeomorph.refl B') (Homeomorph.refl B') := ⟨rfl⟩
    refine .trans (φ₂ := .refl G) (e₁ := .refl B') (e₂ := .refl B')
      (.pullbackCongr (isoPullbackClassifyingMap G F E' E).symm (classifyingMap G F E E')
        (classifyingMap G F E E') _ (by simp)) ?_
    have _ b : Zero (E b) := ⟨Classical.arbitrary _⟩
    refine (isoPullbackClassifyingMap G F E E').symm.trans (φ₂ := .refl _) (e₂ := .refl _) ?_
    have : IsFiberBundle F (⇑(Homeomorph.refl B') *ᵖ E') :=
      IsFiberBundle.instPullbackCoeContinuousMap F E' (f := toContinuousMap (Homeomorph.refl B'))
    exact .symm <| .pullbackHomeomorph (.refl _)

omit [IsTopologicalGroup G] in
@[simp]
lemma coe_homotopyEquiv [IsUniversalBundle G F E] [IsUniversalBundle G F E'] :
    ⇑(homotopyEquiv G F E E') = classifyingMap G F E' E := rfl

omit [IsTopologicalGroup G] in
@[simp]
lemma coe_homotopyEquiv_symm [IsUniversalBundle G F E] [IsUniversalBundle G F E'] :
    ⇑(homotopyEquiv G F E E').symm = classifyingMap G F E E' := rfl

omit [IsTopologicalGroup G] in
/-- The base space of any universal bundle is nonempty.

This is can not be made into an instance because `Nonempty B` does not
involve `G`, `F` and `E`, while `IsUniversalBundle G F E` does. -/
lemma nonempty [IsUniversalBundle G F E] : Nonempty B :=
  .map (classifyingMap G F E (Trivial PUnit F)) inferInstance

/-- The total space of any universal bundle is contractible.

This is can not be made into an instance because `ContractibleSpace (TotalSpace F E)` does not
involve `G` while `IsUniversalBundle G F E` does.

TODO: finish - I thought I could get this done abstractly before giving a construction of
universal bundles, but it seems getting contractibility from the construction might actually be
easier. -/
lemma contractibleSpace [IsUniversalBundle G F E] : ContractibleSpace (TotalSpace F E) := by
  have _ := nonempty G F E
  refine (contractible_iff_id_nullhomotopic _).2 ⟨Classical.arbitrary _, ?_⟩
  sorry

end IsUniversalBundle

section MilnorConstruction

/-- Milnor's construction of the classifying space of any topological group `G`. This is
an abbreviation for the orbit space of the locally trivial `G`-space that is the countable join
`IJoin fun _ : ℕ ↦ G`. -/
abbrev Bundle.MilnorBG (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  Quotient (MulAction.orbitRel G (IJoin fun _ : ℕ ↦ G))

/-- Milnor's construction of the classifying bundle of any topological group `G`. This is
an abbreviation for the bundle constructed using `Bundle.OfMap` out of the locally trivial `G`-space
that is the countable join `IJoin fun _ : ℕ ↦ G`. -/
abbrev Bundle.MilnorEG (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MilnorBG G → Type _ :=
  (OfMap (Quotient.mk (MulAction.orbitRel G (IJoin fun _ : ℕ ↦ G))))

variable {B : Type*} [TopologicalSpace B] {f : C(B, MilnorBG G)}

/-- TODO: move -/
lemma _root_.Finsupp.sum_eq_finsum {α M N : Type*} [Zero M] [AddCommMonoid N] (f : α →₀ M)
    {g : α → M → N} (h : ∀ a, g a 0 = 0) : f.sum g = ∑ᶠ a, g a (f a) := by
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset]
  grind [Function.support_subset_iff]

/-- Arbitrary joins of `G` are numerable bundles over their orbit spaces. -/
instance {ι : Type*} :
    NumerableBundle G (OfMap (Quotient.mk (MulAction.orbitRel G (IJoin fun _ : ι ↦ G)))) := by
  let f i : C(Quotient (MulAction.orbitRel G (IJoin fun _ : ι ↦ G)), ℝ) :=
    ⟨fun x ↦ x.lift (fun x ↦ x.weights i) <| by rintro _ x' ⟨g, rfl⟩; simp, by fun_prop⟩
  refine NumerableCover.numerableBundle _ _ (u := fun i ↦ Function.support (f i)) ?_ fun i ↦ ?_
  · exact NumerableCover.iff_exists_generalizedPositivePartition'.2 ⟨{
      toFun i := f i
      point_finite' := by rintro ⟨x⟩; exact x.weights.hasFiniteSupport
      continuous_finsum' := (continuous_const (y := 1)).congr fun x ↦ by
        obtain ⟨x, rfl⟩ := x.exists_rep
        simpa [f] using x.total.symm.trans <| x.weights.sum_eq_finsum (by simp)
      nonneg' i x := by obtain ⟨x, rfl⟩ := x.exists_rep; simp [f]
      exists_pos' x _ := by obtain ⟨x, rfl⟩ := x.exists_rep; exact x.exists_pos
    }, by simp⟩
  · have ⟨e, he, he'⟩ := IJoin.exists_equivariant_trivialization G i
    suffices h : ∃ e' : Trivialization G (π G (OfMap (Quotient.mk
        (MulAction.orbitRel G (IJoin fun _ : ι ↦ G))))), e'.baseSet = Function.support (f i) by
      have ⟨e', he''⟩ := h; exact he'' ▸ e'.isTrivialOn_baseSet
    rw [show π G (OfMap _) = Quotient.mk _ ∘ OfMap.totalSpaceHomeomorph G _ by
      ext x; simp [show ⟦x.snd.1⟧ = x.proj from x.snd.2]]
    refine ⟨e.compHomeomorph (OfMap.totalSpaceHomeomorph G _), he'.trans ?_⟩
    ext x
    simp only [f, Set.mem_setOf, ContinuousMap.coe_mk, Function.mem_support]
    rw [← x.out_eq, Quotient.lift_mk]
    simp [(x.out.nonneg i).lt_iff_ne' (b := 0)]

/-- As expected, `MilnorEG G` is indeed a universal `G`-principal bundle over `MilnorBG G`.

TODO: finish this -/
instance Bundle.MilnorEG.instIsUniversalBundle : IsUniversalBundle G G (MilnorEG G) where
  exists_classifyingMap B' _ E' _ _ _ _ _ _ _ := by
    /- It suffices to prove that an equivariant map to the total space of `MilnorEG G` exists. -/
    suffices h : Nonempty C[G](TotalSpace G E', TotalSpace G (MilnorEG G)) by
      obtain ⟨f⟩ := h
      have _ b : Zero (E' b) := ⟨Classical.arbitrary _⟩
      exact ⟨_, ⟨ContinuousBundleActionHom.pullbackEquivIso _ <| .ofContinuousMulActionHom f⟩⟩
    /- This total space is identified with `IJoin fun _ : ℕ ↦ G`, so it suffices to prove the
    existence of an equivariant map to that. -/
    suffices h : Nonempty C[G](TotalSpace G E', IJoin fun _ : ℕ ↦ G) from
      ⟨(OfMap.totalSpaceContinuousMulActionEquiv _ _).symm.toContinuousMulActionHom.comp h.some⟩
    /- Since `E'` is numerable, we can obtain an `ℕ`-indexed family of equivariant trivialisations
    with a partition of unity `f` subordinate to their base sets. -/
    have ⟨u, hu, ⟨f, hf⟩, hu'⟩ := NumerableBundle.exists_countable_isTrivialOn_cover G E'
    have _ b : Zero (E' b) := ⟨Classical.arbitrary _⟩
    choose e he he' using fun i ↦
      (isTrivialOn_iff_exists_equivariant_trivialization (hu' i).1).1 (hu' i).2
    /- Now the obvious construction works. -/
    exact ⟨{
      toFun x := {
        toStdSimplex := f.toStdSimplex x.proj
        points n := if n ∈ f.finsupport x.proj then (e n x).2 else none
        points_eq_none_iff := by simp }
      continuous_toFun := by
        refine IJoin.continuous_iff.2 ⟨?_, ?_⟩
        · simp only [PartitionOfUnity.weights_toStdSimplex, PartitionOfUnity.toFinsupp_apply]
          fun_prop
        · simp only [PartitionOfUnity.mem_finsupport, Function.mem_support, ne_eq, ite_not,
            Option.continuous_excludedPointTopology'_iff']
          refine fun n ↦ ⟨Continuous.isOpen_support (by fun_prop),
            continuous_snd.comp_continuousOn <| .mono (e n).continuousOn <|
              (Set.preimage_mono (f := π G E') <| subset_closure.trans (hf n)).trans ?_⟩
          simp [(e n).source_eq, he]
      map_smul' g x := by
        refine IJoin.ext (by simp) fun n hn ↦ ?_
        simp only [smul_proj, PartitionOfUnity.weights_toStdSimplex,
          PartitionOfUnity.toFinsupp_apply] at hn
        simp [hn.ne', (he' n).map_smul (g := g) (x := x)
          (by simp [(e n).source_eq, he, subset_closure.trans (hf n) hn.ne'])] }⟩
  homotopic_of_iso B' _ f f' e := by
    /- It suffices to prove that any two `G`-equivariant maps into the total space of `MilnorEG G`
    are `G`-equivariantly homotopic, which we have already have proven in a separate lemma. -/
    suffices h : (ContinuousBundleActionHom.pullbackLift (G := G) (F := G) (E := MilnorEG G)
        (f := f)).toContinuousMulActionHom.Homotopic ((ContinuousBundleActionHom.pullbackLift
          (f := f')).toContinuousMulActionHom.comp e.toContinuousMulActionHom) by
      convert h.baseMap <;> ext <;> simp
    have _ b : Zero (MilnorEG G b) := ⟨Classical.arbitrary _⟩
    rw [← ContinuousMulActionHom.Homotopic.continuousMulActionEquiv_comp_iff
      (OfMap.totalSpaceContinuousMulActionEquiv _ _)]
    exact IJoin.continuousMulActionHom_homotopic _ _

end MilnorConstruction
