/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import ClassifyingBundles.IsTrivialOn
import ClassifyingBundles.NumerableCover

/-! # Numerable bundles
In this file we define numerable bundles, i.e. fibre bundles that can be trivialised on some
numerable covering.
-/

open Bundle unitInterval

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
instance NumerableBundle.of_paracompactSpace [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
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
instance NumerableBundle.pullback [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [(b : B) → Zero (E b)] [NumerableBundle F E] {B' : Type*} [TopologicalSpace B']
    (f : C(B', B)) : NumerableBundle F (f *ᵖ E) := by
  refine numerableCover_isTrivialOn (F := F) (E := E) |>.preimage (map_continuous f)
    |>.numerableBundle _ _ fun s ↦ s.2.pullback F E f

/-- Every numerable bundle can be trivialised on some countable locally finite numerable open cover.

TODO: get rid of unnecessary `[(b : B) → Zero (E b)]`-assumption -/
lemma NumerableBundle.exists_countable_isTrivialOn_cover [∀ b, TopologicalSpace (E b)]
    [FiberBundle F E] [(b : B) → Zero (E b)] [NumerableBundle F E] :
    ∃ u : ℕ → Set B, LocallyFinite u ∧ NumerableCover u ∧
      ∀ i, IsOpen (u i) ∧ IsTrivialOn F E (u i) := by
  have _ : Nonempty {u | IsTrivialOn F E u} := ⟨⟨∅, isTrivialOn_empty F E⟩⟩
  have h := (numerableCover_isTrivialOn (F := F) (E := E)).countable_locallyFinite_replacement
  refine h.imp fun u ↦ .imp_right <| .imp_right <| forall_imp fun i ⟨u', hu', hu'', hu'''⟩ ↦ ?_
  rw [← hu']
  refine ⟨isOpen_sUnion fun _ h ↦ (hu''' _ h).1, ?_⟩
  rw [Set.sUnion_eq_iUnion]
  refine IsTrivialOn.disjointIUnion F E (fun v ↦ ?_) (fun v ↦ ?_)
  · exact ⟨v, (hu''' _ v.2).1.mem_nhdsSet_self, fun _ h ↦ hu'' h.symm⟩
  · have ⟨i, hi⟩ := (hu''' _ v.2).2
    exact .mono _ _ hi i.2

/-- Every fibre bundle on `B × I` with `B` a paracompact Hausdorff space is trivial on sets of
the form `u i ×ˢ Set.univ` for `u : ℕ → Set B` some countable locally finite open cover.

TODO: generalise to numerable bundles -/
lemma exists_countable_isTrivialOn_cover_prod_unitInterval (E : B × I → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    [∀ b, Zero (E b)] [ParacompactSpace B] [T2Space B] :
    ∃ u : ℕ → Set B, LocallyFinite u ∧ ∀ i, IsOpen (u i) ∧ IsTrivialOn F E (u i ×ˢ .univ) := by
  letI ι : Set (Set B) := {u | IsOpen u ∧ IsTrivialOn F E (u ×ˢ .univ)}
  have _ : Nonempty ι := ⟨⟨∅, isOpen_empty, by simp [isTrivialOn_empty]⟩⟩
  have h := NumerableCover.countable_locallyFinite_replacement (ι := ι)
    (u := Subtype.val) <| .of_paracompactSpace fun b ↦ by
      have ⟨u, hu, hu', hu''⟩ := exists_isTrivialOn_prod_unitInterval F E b
      exact ⟨⟨u, hu', hu''⟩, hu⟩
  refine h.imp fun u ↦ .imp_right fun h ↦ forall_imp (fun i ⟨u', hu', hu'', hu'''⟩ ↦ ?_) h.2
  rw [← hu']
  refine ⟨isOpen_sUnion fun _ h ↦ (hu''' _ h).1, ?_⟩
  rw [Set.sUnion_eq_iUnion, Set.iUnion_prod_const]
  refine IsTrivialOn.disjointIUnion F E (fun v ↦ ?_) (fun v ↦ ?_)
  · refine ⟨v.1 ×ˢ .univ, ((hu''' _ v.2).1.prod isOpen_univ).mem_nhdsSet_self, fun _ h ↦ ?_⟩
    exact Set.Disjoint.set_prod_left (hu'' h.symm) _ _
  · have ⟨i, hi⟩ := (hu''' _ v.2).2
    exact .mono _ _ (by grind) i.2.2
