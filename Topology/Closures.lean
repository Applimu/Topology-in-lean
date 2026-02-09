import Topology.Basic

namespace Topology

-- A point x is in the interior of a set A when there exists an open neighborhood
-- N of x that is a subset of A.
def interior {X: Type} (τ: Topology X) (A: Set X): Set X := Set.mk fun x =>
  ∃N: τ.open_nbhd x, N.nbhd ⊆ A

@[simp]
theorem interior_def {X: Type} (τ: Topology X) (A: Set X) (x: X): x ∈ τ.interior A ↔ ∃N: τ.open_nbhd x, N.nbhd ⊆ A where
  mp h := h
  mpr h := h

@[simp]
theorem interior_is_open {X: Type} (τ: Topology X) (A: Set X):
τ.is_open (τ.interior A) := by
  apply τ.open_of_open_cover_subsets'
  intro x ⟨Uₓ, Uₓ_subset_A⟩
  exists Uₓ
  intro y y_in_Uₓ
  exists {toSet := Uₓ.nbhd, nbhd_open := Uₓ.nbhd_open, is_nbhd := y_in_Uₓ}

def interior_subset {X: Type} (τ: Topology X) (A: Set X): τ.interior A ⊆ A := by
  intro x ⟨N, hN⟩
  apply hN
  exact N.is_nbhd

theorem interior_open_eq_self {X: Type} (τ: Topology X) {U: Set X} (U_open: τ.is_open U): τ.interior U = U := by
  refine Eq.symm (Set.subset_antisymm U (τ.interior U) ?_ ?_)
  · intro u hu
    exists ⟨U, U_open, hu⟩
    exact Set.subset_refl U
  · exact @interior_subset X τ U

@[simp]
theorem interior_interior {X: Type} (τ: Topology X) {U: Set X}: τ.interior (τ.interior U) = τ.interior U := by
  refine interior_open_eq_self τ ?_
  exact interior_is_open τ U

-- idk how useful this theorem is lol
theorem open_of_interior_superset {X: Type} (τ: Topology X) (U: Set X)
  (h: U ⊆ τ.interior U): τ.is_open U := by
    have : U = τ.interior U := Set.subset_antisymm _ _ h (τ.interior_subset U)
    rw [this]
    exact τ.interior_is_open U

theorem interior_inter_eq_inter_interior {X: Type} (τ: Topology X)
 (U V: Set X): τ.interior (U ∩ V) = τ.interior U ∩ τ.interior V := by
  ext p
  constructor
  intro ⟨N, hN⟩
  constructor <;> exists N <;> intro x x_in_nbhd
  exact And.left $ hN x_in_nbhd
  exact And.right $ hN x_in_nbhd
  intro ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩
  exists {
    toSet := N₁.nbhd ∩ N₂.nbhd
    nbhd_open := τ.open_inter N₁.nbhd N₁.nbhd_open N₂.nbhd N₂.nbhd_open
    is_nbhd := ⟨N₁.is_nbhd, N₂.is_nbhd⟩
  }
  intro x ⟨a,b⟩
  exact ⟨hN₁ a, hN₂ b⟩


theorem cts_iff_preimage_interior_sub_interior_preimage {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y):
  continuous τ₁ τ₂ f ↔ (∀U: Set Y, Set.preimage f (τ₂.interior U) ⊆ τ₁.interior (Set.preimage f U)) := by
  constructor
  ·
    intro h U x ⟨N₂, hN₂⟩
    let N₁: τ₁.open_nbhd x := Topology.cts_preimage_nbhd _ _ f N₂ h
    exists N₁
    intro y hy
    exact hN₂ hy
  ·
    intro h
    apply continuous_of_open_imp_preimage_open
    intro U U_open
    apply open_of_open_cover_subsets'
    intro x Ufx
    apply h
    exists ⟨U, U_open, Ufx⟩
    exact Set.subset_refl _


def of_interior {X: Type} (interior: Set X → Set X) (interior_shrinks: ∀A, interior A ⊆ A)
  (interior_all: interior Set.all = Set.all) (interior_interior: ∀A, interior (interior A) = interior A)
  (interior_inter : ∀A B, interior (A ∩ B) = interior A ∩ interior B): Topology X where
    is_open U := interior U = U
    open_all := interior_all
    open_inter U U_open V V_open := by
      apply Set.subset_antisymm
      exact interior_shrinks (U ∩ V)
      rw [interior_inter, U_open, V_open]
      exact Set.subset_refl _
    open_of_open_cover_subsets U cover := by
      simp [Classical.skolem] at cover
      obtain ⟨cover, (h_cover : ∀x h, _)⟩ := cover
      apply Set.subset_antisymm
      exact interior_shrinks U
      intro x hx
      have ⟨h₁, h₂, h₃⟩ := h_cover x hx
      generalize hC : cover x hx = C at h₁ h₂ h₃
      have := interior_inter C U
      rw [← Set.inter_eq_left_iff_subset] at h₃
      rw [h₁, h₃, Eq.comm, h₁, Set.inter_eq_left_iff_subset] at this
      exact this h₂


theorem others_imply_interior_interior {X: Type} (interior: Set X → Set X) (interior_shrinks: ∀A, interior A ⊆ A)
  (interior_all: interior Set.all = Set.all)
  (interior_inter : ∀A B, interior (A ∩ B) = interior A ∩ interior B): ∀A, interior (interior A) = interior A := by
    intro A
    apply Set.subset_antisymm
    exact @interior_shrinks (interior A)
    have := @interior_shrinks A
    rw [← Set.inter_eq_right_iff_subset] at this
    rw [← Set.inter_eq_left_iff_subset, ← interior_inter, this]
    apply Set.subset_antisymm
    exact @interior_shrinks (interior A)

/--
  A point x is in the closure of U iff for every closed set S which is
  a superset of U, x is in S
-/
def closure {X: Type} (τ: Topology X) (A: Set X): Set X := Set.mk fun x => ∀S: Set X, τ.is_closed S → (A ⊆ S) → x ∈ S

@[simp]
theorem closure_def {X: Type} (τ: Topology X) (A: Set X) (x: X): x ∈ τ.closure A ↔ ∀S: Set X, τ.is_closed S → (A ⊆ S) → x ∈ S := by
  simp [Topology.closure]

theorem is_closed_closure {X: Type} (τ: Topology X) (U: Set X): τ.is_closed (τ.closure U) := by
  simp [Topology.closure]
  apply τ.open_of_open_cover_subsets'
  intro x cond
  simp at cond
  rcases cond with ⟨C, C_closed, U_sub_C, not_x_mem_C⟩
  exists {
    toSet := C.complement
    nbhd_open := C_closed,
    is_nbhd := not_x_mem_C
  }
  intro y h
  simp
  exists C

@[simp]
theorem closure_closed_iff_eq_self {X: Type} (τ: Topology X) (U: Set X): τ.closure U = U ↔ τ.is_closed U where
  mp := by
    intro heq
    rw [← heq]
    exact τ.is_closed_closure U
  mpr := by
    intro u
    ext x
    constructor
    · intro h
      apply h
      assumption
      exact Set.subset_refl _
    · intro h S _ h₃
      exact h₃ h


theorem closure_superset {X: Type} (τ: Topology X) (S: Set X): S ⊆ τ.closure S := by
  intro x x_in_S C _ C_superset
  exact C_superset x_in_S


theorem closure_closure {X: Type} (τ: Topology X) (A: Set X): τ.closure (τ.closure A) = τ.closure A := by
  rw [closure_closed_iff_eq_self]
  exact is_closed_closure τ A

/--
  While I do not remember the exact problem at this point, it should be apparent that this is
  a proof that you can add one point to a topology
-/
def exam_problem_1 {X: Type} (τ: Topology X): Topology (Option X) where
  is_open := fun U => (none ∈ U ∧ (τ.is_open (Set.preimage some U))) ∨ U = Set.empty
  open_all := by
    left
    simp
  open_inter := by
    simp
    intro U U_open V V_open
    cases U_open
    case inr h₁ =>
      subst h₁
      simp
    case inl h₁ =>
    cases V_open
    case inr h₂ =>
      subst h₂
      simp
    case inl h₂ =>
      left
      constructor
      exact ⟨h₁.left, h₂.left⟩
      apply τ.open_inter
      exact h₁.right
      exact h₂.right
  open_of_open_cover_subsets := by
    intro U open_cover_subsets
    by_cases h: none ∈ U
    case pos =>
      left
      refine And.intro h ?_
      apply τ.open_of_open_cover_subsets'
      intro x hx
      replace open_cover_subsets := open_cover_subsets (some x) hx
      obtain ⟨Uₓ, open_idk, x_in_Uₓ, Uₓ_sub_U⟩ := open_cover_subsets
      cases open_idk
      case h.a.inl k =>
        exists {
          toSet := Set.preimage some Uₓ
          nbhd_open := k.right
          is_nbhd := x_in_Uₓ
        }
        simp
        exact Set.preimage_monotone some _ _ Uₓ_sub_U
      case h.a.inr heq =>
        subst heq
        exact False.elim x_in_Uₓ

    case neg =>
      right
      ext x
      simp
      intro x_in_U
      replace open_cover_subsets := open_cover_subsets x x_in_U
      obtain ⟨Uₓ, open_idk, x_in_Uₓ, Uₓ_sub_U⟩ := open_cover_subsets
      cases open_idk
      case h.h.inl k => exact absurd (Uₓ_sub_U k.left) h
      case h.h.inr heq =>
        subst heq
        exact x_in_Uₓ


#check Topology.closure_closed_iff_eq_self
/--
  I believe this question said "Suppose (X, τ) is a topology such that the closure of
  every nonempty set is the set X itself. Prove that τ must be the indiscrete topology"
-/
theorem exam_problem_3 {X: Type} (τ: Topology X) (h: ∀U: Set X, Set.nonempty U → τ.closure U = Set.all):
  τ = Topology.indiscrete_topology X := by
  have : ∀S: Set X, Set.nonempty S → (S = Set.all ↔ τ.is_closed S) := by
    intro S hs
    constructor
    · intro rfl
      exact Topology.closed_all τ

    · intro h_closed
      rw [← Topology.closure_closed_iff_eq_self] at h_closed
      exact Eq.trans h_closed.symm (h S hs)

  simp [Set.ext_iff] at h
  apply Topology.topologies_equal_of_same_closed_sets
  intro S
  simp
  constructor
  · intro S_closed
    apply Set.of_nonempty_imp_eq_all
    intro nonempty
    rw [this S nonempty]
    exact S_closed
  · exact all_or_empty_imp_closed τ S



def homeomorphism {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∃h: Bijective f, continuous τ₁ τ₂ f ∧ continuous τ₂ τ₁ (@inv _ _ f (Surjective.imp_nonempty_inv h.toSurjective))

def id_homeomorphism {X: Type} (τ: Topology X): homeomorphism τ τ id := by
  exists Bijective.id_bij <;> simp

def homogeneous {X: Type} (τ: Topology X):= ∀x₁, ∀x₂, ∃e: X→X, homeomorphism τ τ e ∧ e x₁ = x₂



theorem exam_problem_5 {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (homeomorphic: homeomorphism τ₁ τ₂ f) (h: homogeneous τ₁): homogeneous τ₂ := by
  intro y₁ y₂
  obtain ⟨f_bij, f_cont, inv_f_cont⟩ := homeomorphic
  have : Nonempty (Y → X) := Surjective.imp_nonempty_inv f_bij.toSurjective
  rcases h (inv f y₁) (inv f y₂) with ⟨e, ⟨e_bij, e_cont, inv_e_cont⟩, y_e_y⟩
  exists f ∘ e ∘ inv f
  constructor
  constructor
  constructor
  · apply continuous_of_open_imp_preimage_open
    intro U U_open
    simp [Set.preimage_comp]
    apply inv_f_cont.open_imp_preimage_open
    apply e_cont.open_imp_preimage_open
    apply f_cont.open_imp_preimage_open
    exact U_open
  · apply continuous_of_open_imp_preimage_open
    intro U U_open
    have : Nonempty (X → Y) := ⟨f⟩
    have : Bijective (f ∘ e) := by exact Bijective.comp_bij e f e_bij f_bij
    have inv_f_bij: Bijective (inv f) := by exact inv_bij f f_bij
    have : Bijective (e ∘ inv f) := by exact Bijective.comp_bij (inv f) e inv_f_bij e_bij
    rw [Bijective.inv_comp this f_bij, Bijective.inv_comp inv_f_bij e_bij, inv_inv f f_bij]
    simp
    apply inv_f_cont.open_imp_preimage_open
    apply inv_e_cont.open_imp_preimage_open
    exact f_cont.open_imp_preimage_open U U_open
  · have inv_f_bij: Bijective (inv f) := by exact inv_bij f f_bij
    apply Bijective.comp_bij
    apply Bijective.comp_bij
    all_goals assumption
  · dsimp
    rw [y_e_y]
    change (f ∘ inv f) y₂ = y₂
    rw [Surjective.inv_right_inv f_bij.toSurjective]
    rfl






theorem interior_subset_closure {X: Type} (τ: Topology X) (A: Set X):
  τ.interior A ⊆ τ.closure A := by
    apply Set.subset_trans _ A _
    exact @interior_subset X τ A
    exact @closure_superset X τ A


def boundary {X: Type} (τ: Topology X) (A: Set X): Set X :=
  Set.mk fun x => ∀U: Set X, τ.is_open U → x ∈ U → Set.nonempty (U ∩ A) ∧ Set.nonempty (U ∩ A.complement)

@[simp]
theorem boundary_def {X: Type} (τ: Topology X) (A: Set X) (x: X): x ∈ τ.boundary A ↔
∀U, τ.is_open U → x ∈ U → Set.nonempty (U ∩ A) ∧ Set.nonempty (U ∩ A.complement) := by
  rfl

def boundary_empty_empty {X: Type} (τ: Topology X): τ.boundary Set.empty = Set.empty := by
  apply Set.subset_antisymm
  -- ⊆
  intro x x_in_boundary
  simp at x_in_boundary
  apply x_in_boundary Set.all
  exact τ.open_all
  trivial
  --⊇
  exact Set.empty_subset (τ.boundary Set.empty)


def boundary_all_empty {X: Type} (τ: Topology X): τ.boundary Set.all = Set.empty := by
  apply Set.subset_antisymm
  intro x x_in_boundary
  simp at x_in_boundary
  apply x_in_boundary Set.all
  exact τ.open_all
  trivial
  exact Set.empty_subset (τ.boundary Set.all)

theorem boundary_all_or_empty_empty {X: Type} (τ: Topology X) (U: Set X) (aoe: Set.all_or_empty U):
  τ.boundary U = Set.empty := by
  induction aoe
  exact boundary_all_empty τ
  exact boundary_empty_empty τ

def boundary_interior_disjoint {X: Type} (τ: Topology X) (A: Set X): τ.interior A ∩ τ.boundary A = Set.empty := by
  apply Set.subset_antisymm _ _ _ (Set.empty_subset _)
  rintro x ⟨h_int, h_bound⟩
  obtain ⟨_, ⟨o, ho₁, ho₂⟩⟩ := (h_bound (τ.interior A)
      (τ.interior_is_open A)
      h_int)
  exact absurd (τ.interior_subset A ho₁) ho₂

def boundary_subset_closure {X: Type} (τ: Topology X) (A: Set X): τ.boundary A ⊆ τ.closure A := by
  intro x x_boundary
  intro S S_closed S_superset
  apply Classical.byContradiction
  intro x_not_in_S
  obtain ⟨i, hi⟩ := (x_boundary S.complement S_closed x_not_in_S).left
  apply hi.left
  apply S_superset
  exact hi.right
