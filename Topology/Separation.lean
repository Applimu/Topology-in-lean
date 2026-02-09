import Topology.Basic

namespace Topology

variable {X: Type} (τ: Topology X)


def isHausdorff : Prop := ∀x y: X, (∀U: τ.open_nbhd x, ∀V: τ.open_nbhd y, Set.nonempty (U.nbhd ∩ V.nbhd)) → x = y

-- Maybe look into this?
structure HausdorffSpace extends Topology X where
  eq_of_nbhds_always_intersect : toTopology.isHausdorff

theorem hausdorff_ext (hausdorff: τ.isHausdorff): ∀x y: X, (∀U: τ.open_nbhd x, ∀V: τ.open_nbhd y,
    ∃p: X, p ∈ U.nbhd ∩ V.nbhd) → x = y := hausdorff

def hausdorff_separates {τ: Topology X} (h: τ.isHausdorff): ∀x y: X, x ≠ y →
  (∃U: τ.open_nbhd x, ∃V: τ.open_nbhd y, U.nbhd ∩ V.nbhd = Set.empty) := by
  intro x y hneq
  have := hneq ∘ h x y
  simp only [imp_false, Classical.not_forall, Set.not_nonempty_iff_eq_empty] at this
  exact this

def hausdorff_separates' {τ: Topology X} (h: τ.isHausdorff): ∀x y: X, x ≠ y →
  (∃U: τ.open_nbhd x, ∃V: τ.open_nbhd y, U.nbhd ∩ V.nbhd = Set.empty) := by
  intro x y hneq
  have := hneq ∘ h x y
  simp only [imp_false, Classical.not_forall, Set.not_nonempty_iff_eq_empty] at this
  exact this

theorem empty_hausdorff: isHausdorff empty_topology := Empty.rec

theorem discrete_hausdorff: isHausdorff (discrete_topology X) := by
  intro x y property
  obtain ⟨p, hp₁, hp₂⟩ := property ⟨{x}, trivial, rfl⟩ ⟨{y}, trivial, rfl⟩
  clear property
  simp_all

instance hausdorff_indiscrete_imp_subsingleton:
  isHausdorff (indiscrete_topology X) → Subsingleton X := by
  intro hausdorff
  apply Subsingleton.intro
  intro x y
  apply hausdorff
  rintro ⟨U, U_open, x_in_U⟩ ⟨V, V_open, y_in_V⟩
  simp at ⊢ U_open V_open
  exists x
  refine And.intro x_in_U ?_
  cases V_open <;> trivial

def isFrechet := ∀x: X, τ.is_closed {x}

theorem discrete_frechet {X: Type}: isFrechet (discrete_topology X) := by
  intro _
  trivial

instance indiscrete_frechet_imp_subsingleton {X: Type}:
  isFrechet (indiscrete_topology X) → Subsingleton X := by
  intro frechet
  apply Subsingleton.intro
  intro x y
  apply Classical.byContradiction
  intro hne
  change ¬y ∈ ({x}: Set X) at hne
  replace frechet := frechet x
  simp_all [Set.ext_iff]


theorem isfrechet_of_exists_external_nbhd {X: Type} (τ: Topology X):
  (∀x y: X, x ≠ y → ∃U: τ.open_nbhd x, ¬y ∈ U.nbhd) → τ.isFrechet := by
    intro h x
    apply τ.open_of_open_cover_subsets
    intro y ne
    simp at ne
    have := h y x ne
    exists this.choose.nbhd
    constructor; exact this.choose.nbhd_open
    constructor; exact this.choose.is_nbhd
    intro y₁ contained
    intro heq
    subst heq
    apply this.choose_spec contained


theorem hausdorff_imp_frechet {X: Type} (τ: Topology X) (h: isHausdorff τ): isFrechet τ := by
  intro x
  apply τ.open_of_open_cover_subsets'
  -- Given two unequal points x and y, we need to find an open set that contains
  -- y but does not contain x
  intro y hneq
  -- We start by showing that there must exist two disjoint open nbhds of
  -- x and y respectively
  obtain ⟨U, V, U_V_disjoint⟩ : ∃U: τ.open_nbhd x, ∃V: τ.open_nbhd y, U.nbhd ∩ V.nbhd = Set.empty := by
    have h' := hneq ∘ h x y
    simp at *
    exact h'
  clear hneq

  -- We claim that the open set containing y satisfies the goal
  exists V
  -- lastly we need to prove that for any z, if z is in V,
  -- then z cannot be equal to x
  intro z h₂ rfl
  -- This is a contradiction because of the disjointedness condition says that
  -- x being in both V an dU is a contradiction
  have : x ∈ open_nbhd.nbhd τ U ∩ open_nbhd.nbhd τ V := ⟨U.is_nbhd, h₂⟩
  rw [U_V_disjoint] at this
  exact this


def fun_indiscrete_to_frechet_constant {X Y: Type} (τ: Topology Y) (Y_frechet: τ.isFrechet)
  (f: X → Y) (h: continuous (indiscrete_topology X) τ f): ∀x:X, ∀y:X, f x = f y := by
  intro x y
  have ne_f_x_inv_open := h.open_imp_preimage_open _ (Y_frechet (f x))
  simp [← Set.eq_all_or_eq_empty_iff_all_or_empty] at ne_f_x_inv_open
  cases ne_f_x_inv_open
  case inl h =>
    exfalso
    exact h (Set.always_in_image f x) (rfl: f x = f x)
  case inr h =>
    simp [Set.ext_iff] at h
    exact Eq.symm (h y)


def approaches {X: Type} (τ: Topology X) (sequence: Nat → X) (L: X): Prop :=
  ∀U: τ.open_nbhd L, ∃N, ∀n, sequence (N + n) ∈ U.nbhd

theorem unique_limits_of_hausdorff {X: Type} (τ: Topology X) (h: τ.isHausdorff)
  (sequence: Nat → X) (L₁ L₂: X) (aL₁: τ.approaches sequence L₁) (aL₂: τ.approaches sequence L₂):
    L₁ = L₂ := by
  simp [Topology.approaches, isHausdorff] at *
  apply h L₁ L₂
  intro U V
  replace aL₁ := aL₁ U
  replace aL₂ := aL₂ V
  exists sequence $ aL₁.choose + aL₂.choose
  constructor
  exact aL₁.choose_spec aL₂.choose
  rw [Nat.add_comm]
  exact aL₂.choose_spec aL₁.choose


theorem frechet_of_unique_limits {X: Type} (τ: Topology X)
  (unique_limits: ∀(sequence: Nat → X), ∀(L₁ L₂: X), τ.approaches sequence L₁ →
  τ.approaches sequence L₂ → L₁ = L₂): τ.isFrechet := by
  simp [isFrechet]
  intro x
  apply τ.open_of_open_cover_subsets'
  intro y (hneq: x ≠ y)
  have const_x_not_approaches_y: ¬τ.approaches (fun _ => x) y := by
    intro h
    apply hneq
    refine unique_limits (fun _ => x) x y ?_ h
    intro U; exists 0
    simp
    exact U.is_nbhd
  simp [Topology.approaches] at const_x_not_approaches_y
  obtain ⟨U, hU⟩ := const_x_not_approaches_y
  exists U
  intro y₂ h rfl
  exact hU h



theorem subspace_hausdorff_hausdorff {X: Type} (τ: Topology X) (h: τ.isHausdorff)
  (S: Set X): (τ.subspace_topology S).isHausdorff := by
    intro ⟨x, x_in_S⟩ ⟨y, y_in_S⟩ condition
    apply Subtype.ext
    dsimp
    apply τ.hausdorff_ext h
    intro U V

    obtain  ⟨⟨p, p_in_S⟩, what, huh⟩ := condition (Topology.cts_preimage_nbhd _ _ Subtype.val U subtype_val_cts) (Topology.cts_preimage_nbhd _ _ Subtype.val V (subtype_val_cts))
    exists p
