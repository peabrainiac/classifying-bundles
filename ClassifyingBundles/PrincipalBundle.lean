import ClassifyingBundles.TopologicalTorsor
import Mathlib.Topology.VectorBundle.Basic

open Bundle

/- Some prerequisites on action homomorphisms / equivariant maps.
TODO: move to a better fitting file. -/
section

/-- An isomorphism of an `M`-set and an `N`-set along a bijection `M ≃ N`. -/
structure MulActionEquiv {M N : Type*} (φ : M ≃ N) (X Y : Type*) [SMul M X] [SMul N Y] extends
  X →ₑ[φ] Y, X ≃ Y

/-- Equivariant bijections `X ≃ Y` along a bijection `M ≃ N`. -/
notation:25 X " ≃ₑ[" φ:25 "] " Y:0 => MulActionEquiv φ X Y

/-- `M`-equivariant bijections `X ≃ Y`. This is the same as `X ≃ₑ[Equiv.refl M] Y`. -/
notation:25 X " ≃[" M:25 "] " Y:0 => MulActionEquiv (Equiv.refl M) X Y

/-- The identity as an equivariant bijection. -/
@[simps!]
def MulActionEquiv.refl (M : Type*) (X : Type*) [SMul M X] : X ≃[M] X where
  toEquiv := .refl X
  map_smul' _ _ := rfl

/-- The inverse of an equivariant bijection. -/
@[simps!]
def MulActionEquiv.symm {M N : Type*} {φ : M ≃ N} {X Y : Type*} [SMul M X] [SMul N Y]
    (e : X ≃ₑ[φ] Y) : Y ≃ₑ[φ.symm] X :=
  { e.toEquiv.symm, e.toMulActionHom.inverse' e.invFun φ.right_inv' e.left_inv' e.right_inv' with }

instance {α : Type*} : CompTriple.IsId (Equiv.refl α) :=
  inferInstanceAs (CompTriple.IsId (@id α))

/-- The composition of equivariant bijections. -/
def MulActionEquiv.trans {M : Type*} {X Y Z : Type*} [SMul M X] [SMul M Y] [SMul M Z]
    (e : X ≃[M] Y) (e' : Y ≃[M] Z) : X ≃[M] Z :=
  { e'.toMulActionHom.comp e.toMulActionHom, e.toEquiv.trans e'.toEquiv with }

/-- The unique equivariant map from a `G`-torsor `X` to a `G`-set `Y` mapping `x` to `y`. -/
@[simps]
def MulActionHom.fromTorsor {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [MulAction G Y]
    (x : X) (y : Y) : X →[G] Y where
  toFun x' := (x' /ₛ x) • y
  map_smul' g x' := by simp [smul_sdiv_assoc, mul_smul]

@[simp]
lemma MulActionHom.fromTorsor_smul {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [MulAction G Y]
    {g : G} {x : X} {y : Y} : fromTorsor (g • x) y = fromTorsor x (g⁻¹ • y) := by
  ext x'
  simp [sdiv_smul_eq_sdiv_div, div_eq_mul_inv, mul_smul]

instance {G : Type*} [Group G] {X : Type*} [Torsor G X] : IsCancelSMul G X where
  right_cancel' g g' x hx := by rw [← smul_sdiv g x, ← smul_sdiv g' x, hx]

instance {G : Type*} [Group G] {X : Type*} [Torsor G X] : MulAction.IsPretransitive G X where
  exists_smul_eq x x' := ⟨x' /ₛ x, by simp⟩

/-- Every equivariant map from a `G`-torsor to a set with a free `G`-action is injective. -/
lemma MulActionHom.injective {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [MulAction G Y]
    [IsCancelSMul G Y] (f : X →[G] Y) : Function.Injective f := by
  intro x x' h
  rw [← sdiv_smul x x', f.map_smul] at h
  simpa using IsCancelSMul.eq_one_of_smul h

/-- Every equivariant map from a `G`-torsor to a set with a transitive `G`-action is surjective. -/
lemma MulActionHom.surjective {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [MulAction G Y]
    [MulAction.IsPretransitive G Y] (f : X →[G] Y) : Function.Surjective f := by
  intro y
  have ⟨g, hg⟩ := MulAction.exists_smul_eq G (f Torsor.nonempty.some) y
  rw [← f.map_smul] at hg
  exact ⟨_, hg⟩

/-- Every equivariant map between `G`-torsors is an isomorphism. -/
noncomputable def MulActionHom.toEquiv {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [Torsor G Y]
    (f : X →[G] Y) : X ≃[G] Y :=
  { f, Equiv.ofBijective f ⟨f.injective, f.surjective⟩ with }

-- TODO: figure out how to best put a topology here
instance {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [Torsor G Y] :
    TopologicalSpace (X ≃[G] Y) := sorry

end

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (F : Type*) [TopologicalSpace F] {B : Type*} [TopologicalSpace B]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [TopologicalSpace (Bundle.TotalSpace F E)]

variable {F E}

/-- Typeclass stating that a local trivialization of a bundle is equivariant with respect
to actions on its fibers and the model fiber. -/
class Bundle.Trivialization.IsEquivariant [SMul G F] [∀ b, SMul G (E b)]
    (e : Trivialization F (π F E)) where
  map_smul {b : B} (hb : b ∈ e.baseSet) {g : G} {x : E b} : (e ⟨_, g • x⟩).2 = g • (e ⟨_, x⟩).2

variable {G}

-- TODO: get rid of unnecessary `∀ b, Zero (E b)` condition imposed by `Trivialization.symm`
variable [∀ b, Zero (E b)]

/-- The bijection between `E b` and the model fiber `F` as an isomorphism of torsors. -/
noncomputable def Bundle.Trivialization.mulActionEquivAt (e : Trivialization F (π F E))
    [SMul G F] [∀ b, SMul G (E b)] [e.IsEquivariant G] {b : B} (hb : b ∈ e.baseSet) :
    E b ≃[G] F where
  toFun x := (e ⟨_, x⟩).2
  invFun := e.symm b
  left_inv := e.symm_apply_apply_mk hb
  right_inv x := by simp_rw [e.apply_mk_symm hb x]
  map_smul' g x := IsEquivariant.map_smul hb

open Classical in
/-- The coordinate change function between two trivialisations, as an equivariant automorphism of
the model fiber `F`. Defined to be the identity when `b` does not lie in both trivializations. -/
noncomputable def Bundle.Trivialization.coordChangeₑ (e e' : Trivialization F (π F E))
    [SMul G F] [∀ b, SMul G (E b)] [e.IsEquivariant G] [e'.IsEquivariant G] (b : B) :
    F ≃[G] F :=
  if hb : b ∈ e.baseSet ∩ e'.baseSet then
    (e.mulActionEquivAt hb.1).symm.trans (e'.mulActionEquivAt hb.2) else .refl G F

variable (G F E) in
class PrincipalBundle [FiberBundle F E] [Torsor G F] [IsTopologicalTorsor F]
    [∀ b, Torsor G (E b)] [∀ b, IsTopologicalTorsor (E b)] : Prop where
  trivialization_equivariant' (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    e.IsEquivariant G
  continuousOn_coordChange' (e : Trivialization F (π F E)) (e' : Trivialization F (π F E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContinuousOn (Trivialization.coordChangeₑ (G := G) e e') (e.baseSet ∩ e'.baseSet)
