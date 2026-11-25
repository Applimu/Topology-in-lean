import Topology.Basic
import Topology.Separation

namespace Topology

def product_topology {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y): Topology (X × Y) := {
  is_open S := ∀x: X, ∀y: Y, (x,y) ∈ S → ∃U: τ₁.open_nbhd x, ∃V: τ₂.open_nbhd y,
    ∀x' ∈ U.nbhd, ∀y' ∈ V.nbhd, (x', y') ∈ S
  open_all := by
    intro x y _
    exists τ₁.all_nbhd x
    exists τ₂.all_nbhd y
    intro x' x'_in y' y'_in
    trivial
  open_inter := by
    intro U U_open V V_open x y ⟨a,b⟩
    replace U_open := U_open x y a
    replace V_open := V_open x y b
    rcases U_open with ⟨U₁, V₁, c₁⟩
    rcases V_open with ⟨U₂, V₂, c₂⟩
    exists {
      toSet := U₁.nbhd ∩ U₂.nbhd
      nbhd_open := τ₁.open_inter U₁.nbhd U₁.nbhd_open U₂.nbhd U₂.nbhd_open,
      is_nbhd := ⟨U₁.is_nbhd, U₂.is_nbhd⟩
    }
    exists {
      toSet := V₁.nbhd ∩ V₂.nbhd
      nbhd_open := τ₂.open_inter V₁.nbhd V₁.nbhd_open V₂.nbhd V₂.nbhd_open,
      is_nbhd := ⟨V₁.is_nbhd, V₂.is_nbhd⟩
    }
    dsimp
    intro x' h₁ y' h₂
    constructor
    exact c₁ x' h₁.left y' h₂.left
    apply c₂ x' h₁.right y' h₂.right
  open_of_open_cover_subsets := by
    intro U cover_cond x y Uxy
    obtain ⟨Uxy_set, openn, member, subset⟩ := cover_cond (x,y) Uxy
    obtain ⟨Vx, Vy, hV⟩ := openn x y member
    exists Vx
    exists Vy
    intro x' yea₁ y' yea₂
    apply subset
    exact hV x' yea₁ y' yea₂
}

@[simp]
theorem product_topology_open_def {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y)
(S: Set (X × Y)): (product_topology τ₁ τ₂).is_open S ↔ ∀p ∈ S,
∃U: τ₁.open_nbhd p.fst, ∃V: τ₂.open_nbhd p.snd, ∀x' ∈ U.nbhd, ∀y' ∈ V.nbhd, (x', y') ∈ S where
  mp h := by
    intro ⟨x,y⟩
    exact h x y
  mpr h := by
    intro x y
    exact h (x,y)

@[simp]
theorem product_topology_closed_def {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y)
(S: Set (X × Y)): (product_topology τ₁ τ₂).is_closed S ↔ ∀p ∈ S.complement,
∃U: τ₁.open_nbhd p.fst, ∃V: τ₂.open_nbhd p.snd, ∀x' ∈ U.nbhd, ∀y' ∈ V.nbhd, (x', y') ∈ S.complement where
  mp h := by
    intro ⟨x,y⟩
    exact h x y
  mpr h := by
    intro x y
    exact h (x,y)

theorem fst_continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  continuous (product_topology τ₁ τ₂) τ₁ Prod.fst := by
  apply Topology.continuous_of_open_imp_preimage_open
  intro U U_open
  simp
  intro x y Ux
  exists {toSet := U, nbhd_open := U_open, is_nbhd := Ux}
  exists τ₂.all_nbhd y
  dsimp
  intro x' yea₁ _ _
  assumption


theorem snd_continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  continuous (product_topology τ₁ τ₂) τ₂ Prod.snd := by
  apply continuous_of_open_imp_preimage_open
  intro V V_open
  simp
  intro x y Vy
  exists τ₁.all_nbhd x
  exists ⟨V, V_open, Vy⟩
  simp


theorem diagonal_closed_of_hausdorff {X: Type} (τ: Topology X) (h: τ.isHausdorff):
  (product_topology τ τ).is_closed Set.diagonal := by
  simp
  intro x y hneq
  rcases hausdorff_separates h x y hneq with ⟨U, V, disjoint⟩
  exists U; exists V;
  intro x' x'nbhd y' y'nbhd heq
  cases heq
  change x' ∈ Set.empty
  rw [← disjoint]
  exact ⟨x'nbhd, y'nbhd⟩

theorem hausdorff_of_diagonal_closed {X: Type} (τ: Topology X)
(h: (product_topology τ τ).is_closed Set.diagonal): τ.isHausdorff := by
  simp at h
  intro x y cond
  apply Classical.byContradiction
  intro hneq
  replace h := h x y hneq
  rcases h with ⟨U,V,h⟩
  replace cond := cond U V
  rcases cond with ⟨p, Up, Vp⟩
  exact h p Up p Vp rfl


-- This is another thing to look into maybe?
structure FiberProd (X: Type u) (Y: Type v) {Z: Type w} (f: X → Z) (g: Y → Z) extends Prod X Y where
  h: f fst = g snd

-- This definition does not directly depend on `Z` being a topological space
-- So I am leaving that part out!
def fiber_prod_topology {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y)
  (f: X → Z) (g: Y → Z): Topology {p: X × Y // f p.1 = g p.2} :=
   (product_topology τ₁ τ₂).subspace_topology (Set.mk fun p => f p.1 = g p.2)
/-
@[simp]
theorem fiber_prod_topology_open_def {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y)
(f: X → Z) (g: Y → Z) (S: Set {p: X × Y // f p.1 = g p.2}): (fiber_prod_topology τ₁ τ₂ f g).is_open S ↔
∀x:X, ∀y:Y, (h: f x = g y) → ⟨(x,y), h⟩ ∈ S → ∃U: τ₁.open_nbhd x, ∃V: τ₂.open_nbhd y, Set.preimage Subtype.val (Set.product U.nbhd V.nbhd) ⊆ S where
  mp h := by
    intro x y heq in_S
    simp [fiber_prod_topology, -Prod.forall] at h
    rcases h with ⟨K, h₁, h₂⟩
    subst h₂
    simp only [Set.preimage_def] at in_S
    replace h₁ := h₁ (x,y) in_S
    obtain ⟨U, V, h⟩ := h₁
    exists U, V
    intro ⟨(x,y), hx'⟩ hx
    simp_all
  mpr h := by
    simp [fiber_prod_topology]
    exists Set.image Subtype.val S
    constructor
    intro x y ⟨⟨⟨kx, ky⟩, he⟩, k_in_S, heq⟩
    simp at heq
    rcases heq with ⟨rfl, rfl⟩
    replace h := h kx ky he k_in_S
    obtain ⟨U, V, h⟩ := h
    exists U, V
    intro x' hx' y' hy'
    simp [Set.subset_def] at h
    dsimp at he
    exists ⟨(x', y'), ?_⟩
    simp

    constructor
    apply h
    exact U.is_nbhd
    exact V.is_nbhd
    simp
    apply Set.inj_imp_preimage_image
    simp [Injective.intro]
-/



def continuous_fiber_fst {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Z) (g: Y → Z):
  continuous (fiber_prod_topology τ₁ τ₂ f g) τ₁ (fun p => p.val.fst) := by
    apply continuous_of_open_imp_preimage_open
    intro U U_open
    simp [fiber_prod_topology, product_topology, Topology.subspace_topology]
    exists Set.preimage Prod.fst U
    constructor
    · intro x y x_in_U
      exists {toSet := U, nbhd_open := U_open, is_nbhd := x_in_U}
      exists τ₂.all_nbhd y
      intro x' x'_in_U y' _
      exact x'_in_U
    · rfl

def continuous_fiber_snd {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Z) (g: Y → Z):
  continuous (fiber_prod_topology τ₁ τ₂ f g) τ₂ (fun p => p.val.snd) := by
    apply continuous_of_open_imp_preimage_open
    intro U U_open
    simp [fiber_prod_topology, product_topology, Topology.subspace_topology]
    exists Set.preimage Prod.snd U
    constructor
    · intro x y x_in_U
      exists τ₁.all_nbhd x
      exists {toSet := U, nbhd_open := U_open, is_nbhd := x_in_U}
      intro x' _ y' y'_in_U
      exact y'_in_U
    · rfl

theorem fst_open_map {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  open_map (product_topology τ₁ τ₂) τ₁ Prod.fst := by
  intro U U_open
  dsimp [product_topology] at *
  apply τ₁.open_of_open_cover_subsets'
  intro x ⟨⟨x, y⟩, Uxy, heq⟩
  simp at heq
  subst heq
  rcases U_open x y Uxy with ⟨Ux, Vy, h⟩; clear U_open
  exists Ux
  intro x' Ux_x'
  replace h := h x' Ux_x' y Vy.is_nbhd
  exists (x',y)
