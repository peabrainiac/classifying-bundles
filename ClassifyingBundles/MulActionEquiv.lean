import ClassifyingBundles.TopologicalTorsor

/-! # Equivariant isomorphisms

In this file we define a type `MulActionEquiv` of isomorphisms of `G`-sets (i.e. types with a
`G`-action) analogous to the type `MulActionHom` of homomorphisms of `G`-sets. Analogous to how we
define homomorphisms relative to a given homomorphism of groups, we also define isomorphisms
relative to a given isomorphism of groups and provide special notation for isomorphisms relative
to the identity.

We also prove a few lemmas about equivariant maps between torsors, and equiv the type `X ≃[G] Y` of
of isomorphisms between `G`-torsors `X` and `Y` with a topology that makes evaluation at `x` a
homeomorphism for every `x : X`.

## Main definitions
* `MulActionEquiv φ X Y`: the type of equivariant bijections between a type `X` with an `M`-action
  and a type `Y` with an `N`-action relative to a bijection `M ≃ N`. This is also denoted
  `X ≃ₑ[φ] Y`, or `X ≃[M] Y` in the case where `M = N` and `φ` is the identity.
* `MulActionHom.fromTorsor x y`: the unique equivariant map from a `G`-torsor `X` to a `G`-set `Y`
  sending `x` to `y`.
* `MulActionHom.toEquiv`: upgrades any equivariant map between `G`-torsors to an isomorphism.
* `MulActionHom.continuous`: every equivariant map from a topological `G`-torsor to a topological
  `G`-set is continuous.
* `MulActionEquiv.evalHomeo x`: evaluation at `x` as a homeomorphism `(X ≃[G] Y) ≃ₜ Y`, for any
  two topological `G`-torsors `X` and `Y` and any `x : X`.
-/

/-- An isomorphism of an `M`-set and an `N`-set along a bijection `M ≃ N`. -/
structure MulActionEquiv {M N : Type*} (φ : M ≃ N) (X Y : Type*) [SMul M X] [SMul N Y] extends
  X →ₑ[φ] Y, X ≃ Y

/-- Equivariant bijections `X ≃ Y` along a bijection `M ≃ N`. -/
notation:25 X " ≃ₑ[" φ:25 "] " Y:0 => MulActionEquiv φ X Y

/-- `M`-equivariant bijections `X ≃ Y`. This is the same as `X ≃ₑ[Equiv.refl M] Y`. -/
notation:25 X " ≃[" M:25 "] " Y:0 => MulActionEquiv (Equiv.refl M) X Y

lemma MulActionEquiv.toEquiv_injective {M N : Type*} {φ : M ≃ N} {X Y : Type*}
    [SMul M X] [SMul N Y] : (toEquiv : (X ≃ₑ[φ] Y) → X ≃ Y).Injective
  | ⟨⟨f, _⟩, f', _, _⟩, ⟨⟨g, _⟩, g', _, _⟩, h => by
    convert rfl
    · exact congrArg (fun f ↦ f.toFun) h.symm
    · exact congrArg (fun f ↦ f.invFun) h.symm

lemma MulActionEquiv.toMulActionHom_injective {M N : Type*} {φ : M ≃ N} {X Y : Type*}
    [SMul M X] [SMul N Y] : (toMulActionHom : (X ≃ₑ[φ] Y) → X →ₑ[φ] Y).Injective
  | ⟨⟨_, _⟩, _, _, _⟩, ⟨⟨_, _⟩, _, _, _⟩, h =>
    toEquiv_injective <| Equiv.coe_inj.1 <| congrArg (fun f ↦ f.toFun) h

instance {M N : Type*} (φ : M ≃ N) (X Y : Type*) [SMul M X] [SMul N Y] :
    EquivLike (X ≃ₑ[φ] Y) X Y where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h h := by
    obtain ⟨⟨_, _⟩, _, _, _⟩ := e
    obtain ⟨⟨_, _⟩, _, _, _⟩ := e'
    convert rfl <;> symm <;> assumption

instance {M N : Type*} (φ : M ≃ N) (X Y : Type*) [SMul M X] [SMul N Y] :
    MulActionSemiHomClass (X ≃ₑ[φ] Y) φ X Y where
  map_smulₛₗ e m x := e.map_smul' m x

@[simp]
lemma MulActionEquiv.coe_mk {M N : Type*} {φ : M ≃ N} {X Y : Type*} [SMul M X] [SMul N Y]
    {f : X →ₑ[φ] Y} {f' : Y → X} {left_inv : Function.LeftInverse f' f}
    {right_inv : Function.LeftInverse f f'} :
    (MulActionEquiv.mk f f' left_inv right_inv : X → Y) = f := rfl

@[ext]
lemma MulActionEquiv.ext {M N : Type*} {φ : M ≃ N} {X Y : Type*} [SMul M X] [SMul N Y]
    {e e' : X ≃ₑ[φ] Y} (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

lemma MulActionEquiv.map_smul'' {M N : Type*} {φ : M ≃ N} {X Y : Type*} [SMul M X] [SMul N Y]
    (e : X ≃ₑ[φ] Y) (m : M) (x : X) : e (m • x) = φ m • e x :=
  e.map_smul' m x

lemma MulActionEquiv.map_smul {M : Type*} {X Y : Type*} [SMul M X] [SMul M Y]
    (e : X ≃[M] Y) (m : M) (x : X) : e (m • x) = m • e x :=
  e.toMulActionHom.map_smul m x

@[simp]
lemma MulActionEquiv.map_sdiv_map {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [Torsor G Y]
    (e : X ≃[G] Y) (x x' : X) : e x /ₛ e x' = x /ₛ x' := by
  simp [← eq_smul_iff_sdiv_eq, ← e.map_smul]

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

@[simp]
lemma MulActionEquiv.trans_apply {M : Type*} {X Y Z : Type*} [SMul M X] [SMul M Y] [SMul M Z]
    {e : X ≃[M] Y} {e' : Y ≃[M] Z} {x : X} : e.trans e' x = e' (e x) := by rfl

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

lemma MulActionHom.eq_fromTorsor {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [MulAction G Y]
    (f : X →[G] Y) (x : X) : f = fromTorsor x (f x) := by
  ext x'; simp [← f.map_smul]

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

@[simp]
-- this really should have come from `@[simps!]`, but I couldn't get it to work
lemma MulActionHom.toEquiv_apply {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [Torsor G Y]
    (f : X →[G] Y) {x' : X} : f.toEquiv x' = f x' := rfl

@[simp]
lemma MulActionHom.coe_mk {M N : Type*} {φ : M → N} {X : Type*} [SMul M X] {Y : Type*} [SMul N Y]
    (f : X → Y) (hf : ∀ (m : M) (x : X), f (m • x) = φ m • f x) :
    MulActionHom.mk f hf = f := rfl

/-- Every equivariant map out of a topological torsor is continuous. -/
lemma MulActionHom.continuous {G : Type*} [TopologicalSpace G] [Group G] {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Torsor G X] [IsTopologicalTorsor X] [MulAction G Y]
    [ContinuousSMul G Y] (f : X →[G] Y) : Continuous f := by
  rw [f.eq_fromTorsor Torsor.nonempty.some]
  dsimp [fromTorsor]
  fun_prop

/-- For each `x : X`, evaluation at `X` defines a bijection `(X ≃[G] Y) ≃ Y`. -/
@[simps]
noncomputable def MulActionEquiv.evalEquiv {G : Type*} [Group G] {X Y : Type*} [Torsor G X]
    [Torsor G Y] (x : X) : (X ≃[G] Y) ≃ Y where
  toFun e := e x
  invFun y := (MulActionHom.fromTorsor x y).toEquiv
  left_inv e := by ext x'; simp [← e.map_smul]
  right_inv y := by simp

noncomputable instance {G : Type*} [Group G] {X Y : Type*} [Torsor G X] [Torsor G Y]
    [TopologicalSpace Y] : TopologicalSpace (X ≃[G] Y) :=
  .induced (MulActionEquiv.evalEquiv Torsor.nonempty.some) inferInstance

/-- `MulActionEquiv.evalEquiv x` is a homeomorphism for every `x`. -/
@[simps!]
noncomputable def MulActionEquiv.evalHomeo {G : Type*} [TopologicalSpace G] [Group G]
    {X Y : Type*} [TopologicalSpace Y] [Torsor G X] [Torsor G Y] [ContinuousConstSMul G Y]
    (x : X) : (X ≃[G] Y) ≃ₜ Y :=
  (evalEquiv x).toHomeomorphOfIsInducing <| by
    let x' : X := Torsor.nonempty.some
    rw [show ⇑(evalEquiv x) = (evalEquiv x').trans ((evalEquiv x').symm.trans (evalEquiv x)) by
      simp [← Equiv.trans_assoc], Equiv.coe_trans]
    refine .comp ?_ ⟨rfl⟩
    simpa [Equiv.coe_trans, Function.comp_def] using (Homeomorph.smul (x /ₛ x')).isInducing
