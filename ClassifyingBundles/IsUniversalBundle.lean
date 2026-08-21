/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.PrincipalBundle

/-! # Universal bundles
In this file we define universal principal bundles, i.e. numerable `G`-principal bundles such that
for every other numerable `G`-principal bundle is isomorphic to the pullback of the universal bundle
along up to homotopy exactly one map.

For now we are letting everything in this file live in the same universe `u`, and leaving it for
later to figure out how exactly `IsUniversalBundle` should be stated in a more universe-polymorphic
way if needed.
-/

open Bundle

open scoped Topology

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (F : Type u) [TopologicalSpace F] {B : Type u} [TopologicalSpace B]
  (E : B → Type u) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (Bundle.TotalSpace F E)]
  [FiberBundle F E] [Torsor G F] [IsTopologicalTorsor F]
  [∀ b, Torsor G (E b)] [∀ b, IsTopologicalTorsor (E b)]
  {B' : Type u} [TopologicalSpace B']
  (E' : B' → Type u) [∀ b, TopologicalSpace (E' b)] [TopologicalSpace (Bundle.TotalSpace F E')]
  [FiberBundle F E'] [∀ b, Torsor G (E' b)] [∀ b, IsTopologicalTorsor (E' b)]

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
    [FiberBundle F E'] [NumerableBundle F E'] [∀ b, Torsor G (E' b)]
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

omit [IsTopologicalGroup G] [IsTopologicalTorsor F] [∀ b, IsTopologicalTorsor (E b)] in
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
    exact .symm <| .pullbackHomeomorph (.refl _)

omit [IsTopologicalGroup G] [IsTopologicalTorsor F] in
@[simp]
lemma coe_homotopyEquiv [IsUniversalBundle G F E] [IsUniversalBundle G F E'] :
    ⇑(homotopyEquiv G F E E') = classifyingMap G F E' E := rfl

omit [IsTopologicalGroup G] [IsTopologicalTorsor F] in
@[simp]
lemma coe_homotopyEquiv_symm [IsUniversalBundle G F E] [IsUniversalBundle G F E'] :
    ⇑(homotopyEquiv G F E E').symm = classifyingMap G F E E' := rfl

omit [IsTopologicalGroup G] [∀ b, IsTopologicalTorsor (E b)] in
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
