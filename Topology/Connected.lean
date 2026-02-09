
import Topology.Basic

namespace Topology

variable {X: Type} (τ: Topology X)

structure Connected: Prop where intro::
  clopen_imp_all_or_empty: ∀U: Set X, τ.is_open U → τ.is_closed U → Set.all_or_empty U

theorem connected_imp_image_connected {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (h_cont: continuous τ₁ τ₂ f) (f_surj: Surjective f) (h: Connected τ₁): Connected τ₂ := by
    apply Connected.intro
    intro U U_open U_closed
    replace h := h.clopen_imp_all_or_empty (Set.preimage f U) (
        preimage_open_of_continuous _ _ _ h_cont U U_open
      ) (
        preimage_closed_of_continuous _ _ _ h_cont U U_closed
      )
    generalize heq: Set.preimage f U = U' at *
    induction h
    case all =>
      simp_all
    case empty =>
      simp_all

theorem connected_def : Connected τ ↔ (∀U: Set X, τ.is_open U → τ.is_closed U → Set.all_or_empty U) where
  mp := fun ⟨h⟩ => h
  mpr h := ⟨h⟩

theorem indiscrete_topology_connected: Connected (indiscrete_topology X) := by
  apply Connected.intro
  intro U U_open U_closed
  simp only [indiscrete_topology_open_def, indiscrete_topology_closed_def] at *
  assumption

theorem discrete_topology_connnected_iff_subsingleton : Connected (discrete_topology X) ↔ Subsingleton X := by
  apply Iff.trans (b := (∀A: Set X, Set.all_or_empty A))
  case h₁ =>
    simp [connected_def]
  case h₂ =>
    exact Set.all_all_or_empty_iff_subsingleton

def is_connected {X: Type} (τ: Topology X) (S: Set X): Prop := Connected (τ.subspace_topology S)

def is_connected' {X: Type} (τ: Topology X) (S: Set X): Prop := ∀U₁, τ.is_open U₁ →
  ∀U₂, τ.is_closed U₂ → U₁ ∩ S = U₂ ∩ S → S ⊆ U₁ ∨ U₁ ∩ S = Set.empty

theorem is_connected'_def {X: Type} (τ: Topology X) (S: Set X) : τ.is_connected S ↔ τ.is_connected' S := by
  constructor
  · intro h U₁ U₁_open U₂ U₂_closed heq
    obtain ⟨h⟩ := h
    simp at h
    replace h := h (Set.preimage Subtype.val U₁) U₁ U₁_open rfl U₂ U₂_closed ?_
    simp [← Set.eq_all_or_eq_empty_iff_all_or_empty] at h
    rw [subtype_full_image_val, Set.inter_comm] at h
    exact h

    ext ⟨x, hx⟩
    simp
    have : ∀U, x ∈ U ↔ x ∈ U ∩ S := by
      simp
      exact fun _ _ => hx
    rw [this U₁, this U₂, heq]

  · intro h
    apply Connected.intro
    intro U U_open U_closed
    simp at *
    obtain ⟨U, U_open, rfl⟩ := U_open
    obtain ⟨U', U'_closed, heq⟩ := U_closed

    simp [Set.preimage_eq_preimage_iff] at heq
    have := h U U_open U' U'_closed heq
    apply Or.elim this <;> clear this
    · intro h
      apply Set.all_or_empty_of_eq_all
      simp
      exact h
    · intro h
      apply Set.all_or_empty_of_eq_empty
      simp
      rw [Set.inter_comm]
      exact h



def ConnectedComponent {X: Type} (τ: Topology X) (x: X): Set X := Set.mk fun y =>
  ∀U, τ.is_open U → τ.is_closed U → (x ∈ U ↔ y ∈ U)

@[simp]
theorem connected_component_def {X: Type} (τ: Topology X) (x y: X) : y ∈ τ.ConnectedComponent x ↔ ∀U, τ.is_open U → τ.is_closed U → (x ∈ U ↔ y ∈ U) := by
  simp [ConnectedComponent]

theorem connected_component_open {X: Type} (τ: Topology X) (x: X) : τ.is_open $ τ.ConnectedComponent x := by
  apply τ.open_of_open_cover_subsets'
  intro y hy
  simp at hy

#check Subtype.val_inj

theorem ConnectedComponent_subtype_connected {X: Type} (τ: Topology X) (x: X): Connected (τ.subspace_topology (ConnectedComponent τ x)) := by
  intro U U_open U_closed
  simp_all
  rcases U_open with ⟨Uo, Uo_open, heq⟩
  subst heq
  rcases U_closed with ⟨Uc, Uc_closed, heq⟩
  simp [Set.preimage_eq_preimage_iff] at heq

  by_cases Set.nonempty (Set.preimage (@Subtype.val X fun x' => x' ∈ τ.ConnectedComponent x) Uo)
  case pos h =>
    simp [h]
    intro y hy
    simp at hy
    replace h₁ := hy Uo Uo_open
    have : τ.is_open (Uo ∩ τ.ConnectedComponent x) := by
      apply τ.open_inter _ Uo_open
  case neg h =>
    simp only [Set.not_nonempty_iff_eq_empty] at h
    exact Set.all_or_empty_of_eq_empty _ h

end
