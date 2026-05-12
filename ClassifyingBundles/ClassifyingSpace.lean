import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Grp_
import Mathlib.Topology.Category.TopCat.Monoidal

/-! # Classifying spaces of topological monoids

Some work towards classifying spaces of topological groups, not grouped further into files for now.

There's really nothing polished or finished about this, I'm just basically just keeping some drafts
here for now.
-/

universe u

open CategoryTheory Functor ConcreteCategory

/-- Todo: is this even the right functor? -/
noncomputable def SimplicialSpace.realisation : SimplicialObject TopCat.{u} ⥤ TopCat.{u} :=
  leftKanExtension (SSet.stdSimplex ⋙ (whiskeringRight _ _ _).obj TopCat.discrete)
    SimplexCategory.toTop

/-- TODO: here's another one -/
noncomputable def SimplicialSpace.realisation' : SimplicialObject TopCat.{u} ⥤ TopCat.{u} :=
  leftKanExtension (SSet.stdSimplex ⋙ (whiskeringRight _ _ _).obj TopCat.discrete)
    SimplexCategory.toTop


def CategoryTheory.singunlarSimplicialObject {C : Type*} [Category* C] [MonoidalCategory C]
    (F : CosimplicialObject C) [hF : ∀ X, Closed (F.obj X)] : C ⥤ SimplicialObject C where
  obj X := {
    obj Y := F.obj Y.unop ⟶[C] X
    map f := (MonoidalClosed.pre (F.map f.unop)).app X }
  map f := {
    app X := (ihom (F.obj X.unop)).map f }

def CategoryTheory.Mon.nerve {C : Type*} [Category* C] [MonoidalCategory C] :
    Mon C ⥤ SimplicialObject C where
  obj M := {
    obj X := by sorry
    map f := by sorry }
  map f := {
    app X := by sorry }

open Finset in
noncomputable def topologicalMonoidNerve (M : Type u) [TopologicalSpace M] [Monoid M] [ContinuousMul M] :
    SimplicialObject TopCat.{u} where
  obj X :=  .of (Fin X.unop.len → M)
  map {n m} f := ⟨fun g i ↦ Finset.Ico (hom f.unop i.castSucc) (hom f.unop i.succ)|>.preimage
    Fin.castSucc (Fin.castSucc_injective _).injOn|>.sort.map g|>.prod, sorry⟩

/-- The nerve functor from topological monoids to simplicial topological spaces. Specialised to
`TopCat` instead of more general categories for now. -/
def CategoryTheory.Mon.topNerve : Mon TopCat.{u} ⥤ SimplicialObject TopCat.{u} where
  obj M := {
    obj X := .of (Fin X.unop.len → M.X)
    map f := by sorry }
  map f := {
    app X := by sorry }
