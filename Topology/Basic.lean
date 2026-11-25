import Topology.Sets
import Topology.Functions



structure Topology (X: Type) where
  is_open: Set X → Prop
  open_all: is_open Set.all
  open_inter: ∀U: Set X, is_open U → ∀V: Set X, is_open V → is_open (U ∩ V)
  open_of_open_cover_subsets: ∀U: Set X,
    (∀x ∈ U, ∃Uₓ: Set X, is_open Uₓ ∧ x ∈ Uₓ ∧ Uₓ ⊆ U) → is_open U

/-
To experiment with!!:
structure Topology' (X: Type) where
  interior: Set X → Set X
  intensive: ∀A, interior A ⊆ A
  interior_all: interior Set.all = Set.all
  interior_interior: ∀A, interior (interior A) = interior A

def Topology'.is_open {X: Type} (τ: Topology' X) (U: Set X): Prop := τ.interior U = U
-/

namespace Topology

section
variable {X: Type} (τ: Topology X)

@[simp]
theorem open_all': τ.is_open Set.all := τ.open_all

@[simp]
theorem open_empty: τ.is_open Set.empty := by
  apply τ.open_of_open_cover_subsets
  intro x
  exact False.elim

@[simp]
theorem all_or_empty_imp_open (U: Set X) (aoe: Set.all_or_empty U): τ.is_open U := by
  induction aoe <;> simp


def discrete_topology (X: Type): Topology X where
  is_open _ := True
  open_all := by simp
  open_inter := by simp
  open_of_open_cover_subsets x := by simp

@[simp]
theorem discrete_topology_open_def (U: Set X): (discrete_topology X).is_open U ↔ True := by
  simp [discrete_topology]

def indiscrete_topology (X: Type): Topology X where
  is_open := Set.all_or_empty
  open_all := by simp
  open_inter := by
    intro U U_open V V_open
    cases U_open <;> cases V_open <;> simp
  open_of_open_cover_subsets := by
    intro U open_cover_subsets
    by_cases Set.nonempty U
    case pos h =>
      refine Set.all_or_empty_of_eq_all U ?_
      simp [Set.ext_iff]
      intro y
      obtain ⟨x, hx⟩ := h
      obtain ⟨Uₓ, aoe, x_in_Uₓ, Uₓ_sub⟩ := open_cover_subsets x hx
      have : Uₓ.nonempty := ⟨x, x_in_Uₓ⟩
      simp_all
    case neg h =>
      simp at h
      exact Set.all_or_empty_of_eq_empty U h


@[simp]
theorem indiscrete_topology_open_def (U: Set X): (indiscrete_topology X).is_open U ↔ Set.all_or_empty U := by
  simp [indiscrete_topology]

abbrev empty_topology: Topology Empty := discrete_topology Empty

abbrev point_topology: Topology Unit := discrete_topology Unit

@[ext]
theorem topologies_equal_of_same_open_sets {X: Type} (τ₁ τ₂: Topology X)
  (heq: ∀U, τ₁.is_open U ↔ τ₂.is_open U): τ₁ = τ₂ := by
  cases τ₁
  cases τ₂
  simp_all [funext_iff]

theorem point_topology_eq (τ: Topology Unit): τ = point_topology := by
  rcases τ with ⟨τ_is_open, p₁, p₂, p₃⟩
  ext U
  simp
  apply p₃
  intro x Ux
  exists Set.all
  refine ⟨p₁, trivial, ?_⟩
  intro y _
  rw [Unit.ext y x]
  assumption


def serpinski_space: Topology Bool where
  is_open U := false ∈ U → true ∈ U
  open_all := by simp
  open_inter := by
    intro U U_open V V_open
    simp
    intro Uf Vf
    exact ⟨U_open Uf, V_open Vf⟩
  open_of_open_cover_subsets := by
    intro U cond Uf
    replace cond := cond false Uf
    rcases cond with ⟨U₂, yea, U₂f, subset⟩
    apply subset
    apply yea
    assumption

def is_closed {X: Type} (τ: Topology X) (U: Set X): Prop := τ.is_open U.complement

theorem is_closed_iff_is_open_complement {X: Type} (τ: Topology X) (U: Set X): τ.is_closed U ↔ τ.is_open U.complement := by
  simp [is_closed]


theorem is_open_iff_is_closed_complement {X: Type} (τ: Topology X) (U: Set X): τ.is_open U ↔ τ.is_closed U.complement := by
  simp [is_closed]

theorem topologies_equal_of_same_closed_sets {X: Type} (τ₁ τ₂: Topology X)
  (heq: ∀U, τ₁.is_closed U ↔ τ₂.is_closed U): τ₁ = τ₂ := by
  ext U
  have := heq U.complement
  simp [is_closed_iff_is_open_complement] at this
  exact this

@[simp]
theorem closed_all: τ.is_closed Set.all := by
  unfold is_closed
  simp

@[simp]
theorem closed_empty : τ.is_closed Set.empty := by
  unfold is_closed
  simp

@[simp]
theorem all_or_empty_imp_closed (U: Set X) (aoe: Set.all_or_empty U): τ.is_closed U := by
  induction aoe <;> simp

@[simp]
theorem mk_is_closed : (Topology.mk h₀ h₁ h₂ h₃).is_closed C ↔ h₀ (C.complement) := by
  simp [is_closed]

@[simp]
theorem indiscrete_topology_closed_def (U: Set X): (indiscrete_topology X).is_closed U ↔ Set.all_or_empty U := by
  simp [is_closed_iff_is_open_complement]

@[simp]
theorem discrete_topology_closed_def (U: Set X): (discrete_topology X).is_closed U := by
  simp [is_closed_iff_is_open_complement]

structure open_nbhd (x: X) extends Set X where
  nbhd_open: τ.is_open toSet
  is_nbhd: x ∈ toSet

instance (x: X): CoeOut (@open_nbhd X τ x) (Set X) where
 coe := open_nbhd.toSet

@[simp]
def open_nbhd.nbhd {x: X} (self: τ.open_nbhd x): Set X := self.toSet

@[simp]
def in_nbhd {x U} {h₁: τ.is_open U} {h₂: y ∈ U}: x ∈ @open_nbhd.nbhd X τ y {toSet := U, nbhd_open := h₁, is_nbhd := h₂} ↔ x ∈ U := by
  rfl

@[deprecated "dont use this" (since := "12/11/25")]
def exists_open_nbhd {X: Type} (τ: Topology X) (x: X): τ.open_nbhd x := ⟨Set.all, τ.open_all, trivial⟩

theorem open_of_open_cover_subsets' {X: Type} (τ: Topology X):
  ∀U: Set X, (∀x ∈ U, ∃Uₓ: τ.open_nbhd x, Uₓ.nbhd ⊆ U) → τ.is_open U := by
  intro U cond
  apply τ.open_of_open_cover_subsets
  intro x x_in_U
  replace cond := cond x x_in_U
  rcases cond with ⟨Uₓ, Uₓ_subset⟩
  exists Uₓ
  constructor
  exact Uₓ.nbhd_open
  constructor
  exact Uₓ.is_nbhd
  exact Uₓ_subset

/--
  The whole set is always a neighborhood of every point
-/
def all_nbhd (x: X): τ.open_nbhd x where
  toSet := Set.all
  nbhd_open := τ.open_all
  is_nbhd := trivial


theorem open_union {A B : Set X} (hA: τ.is_open A) (hB: τ.is_open B) : τ.is_open (A ∪ B) := by
  refine open_of_open_cover_subsets' τ (A ∪ B) ?_
  rintro x (hx | hx)
  · exists ⟨A, hA, hx⟩
    simp [Set.subset_union_left]
  · exists ⟨B, hB, hx⟩
    simp [Set.subset_union_right]

theorem open_set_union {F: Set (Set X)} (hf: ∀S ∈ F, τ.is_open S): τ.is_open (Set.set_union F) := by
  refine open_of_open_cover_subsets' τ F.set_union ?_
  intro x hx
  obtain ⟨U, hU, hx⟩ := hx
  exists ⟨U, hf U hU, hx⟩
  simp
  intro y hy
  exists U

theorem closed_set_inter {F: Set (Set X)} (hf: ∀S ∈ F, τ.is_closed S): τ.is_closed (Set.set_inter F) := by
  refine (is_closed_iff_is_open_complement τ F.set_inter).mpr ?_
  simp [Set.complement_set_inter]
  refine open_set_union τ ?_
  rintro U ⟨V, hV, rfl⟩
  exact hf V hV

end


section
section
variable {Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)

structure continuous: Prop where intro::
  open_imp_preimage_open: ∀U: Set Y, τ₂.is_open U → τ₁.is_open (Set.preimage f U)

theorem continuous_of_open_imp_preimage_open
  (open_imp_preimage_open: ∀U: Set Y, τ₂.is_open U → τ₁.is_open (Set.preimage f U)):
  continuous τ₁ τ₂ f := continuous.intro open_imp_preimage_open

@[simp]
theorem preimage_open_of_continuous (f_cont: continuous τ₁ τ₂ f)
    (U: Set Y) (h_open: τ₂.is_open U): τ₁.is_open (Set.preimage f U) := f_cont.open_imp_preimage_open U h_open

@[simp]
theorem preimage_closed_of_continuous (f_cont: continuous τ₁ τ₂ f)
    (U: Set Y) (h_closed: τ₂.is_closed U): τ₁.is_closed (Set.preimage f U) := f_cont.open_imp_preimage_open U.complement h_closed

@[simp]
def id_continuous : continuous τ τ id := by
  apply continuous_of_open_imp_preimage_open
  intro U U_open
  exact U_open

@[simp]
def comp_continuous {X Y Z: Type} {τ₁: Topology X} (τ₂: Topology Y) {τ₃: Topology Z}
    (f: X → Y) (g: Y → Z) (f_cont: continuous τ₁ τ₂ f)
    (g_cont: continuous τ₂ τ₃ g): continuous τ₁ τ₃ (g ∘ f) := by
  apply continuous_of_open_imp_preimage_open
  intro U U_open
  exact f_cont.open_imp_preimage_open (U.preimage g) (g_cont.open_imp_preimage_open U U_open)


def fun_discrete_continuous: continuous (discrete_topology X) τ₂ f := by
  apply continuous_of_open_imp_preimage_open
  intro U _
  trivial

def continuous_of_preimage_closed_sets_closed (h: ∀C: Set Y, τ₂.is_closed C → τ₁.is_closed (Set.preimage f C)): continuous τ₁ τ₂ f := by
  apply continuous_of_open_imp_preimage_open
  intro U U_open
  replace h := h U.complement
  simp [← Set.complement_preimage, is_closed_iff_is_open_complement] at h
  exact h U_open

def cts_preimage_nbhd {x: X} (Nf: τ₂.open_nbhd (f x)) (f_cont: continuous τ₁ τ₂ f): τ₁.open_nbhd x where
  toSet := Set.preimage f Nf.nbhd
  nbhd_open := by
    apply f_cont.open_imp_preimage_open
    exact Nf.nbhd_open
  is_nbhd := by
    simp [open_nbhd.nbhd]
    exact Nf.is_nbhd

end

section

variable {X Y: Type} (τ: Topology X) (f: X → Y)

-- Note: Im not entirely sure what to call this
-- but according to wikipedia final topology is a nice option.
def final_topology: Topology Y where
    -- A set is open in Y if it's preimage is open in X
  is_open U := τ.is_open (Set.preimage f U)

  open_all := by simp
  open_inter := by
    intro U U_open V V_open
    exact τ.open_inter (U.preimage f) U_open (V.preimage f) V_open
  open_of_open_cover_subsets := by
    intro U cond
    apply τ.open_of_open_cover_subsets
    intro x ux; replace cond := cond (f x) ux
    rcases cond with ⟨Uₓ, fiUₓ_open, fx_in_Uₓ, Uₓ_subset_U⟩
    exists Uₓ.preimage f
    constructor
    exact fiUₓ_open
    constructor;
    exact fx_in_Uₓ
    exact Set.preimage_monotone f _ _ Uₓ_subset_U

@[simp]
theorem final_topology_open_def (U: Set Y): (final_topology τ f).is_open U ↔ τ.is_open (Set.preimage f U) := by
  simp [final_topology]

theorem final_map_continuous: continuous τ (final_topology τ f) f := by
  apply continuous.intro
  intro U U_open
  exact U_open

end

section

variable {X: Type} (τ: Topology X)

/--
  We define the subspace topology to be in terms of a function `i: Y → X` which we think of it's
  domain as the subspace. If it is an injective function or is actually `Subtype.val`
  then it is an actual subspace topology.
-/
def subspace_topology' {Y} (i: Y → X): Topology Y where
  is_open U := ∃U': Set X, τ.is_open U' ∧ Set.preimage i U' = U
  open_all := by
    exists Set.all
    simp
  open_inter U₁ hU₁ U₂ hU₂ := by
    obtain ⟨U₁', U₁'_open, rfl⟩ := hU₁
    obtain ⟨U₂', U₂'_open, rfl⟩ := hU₂
    exists U₁' ∩ U₂'
    simp [τ.open_inter U₁' U₁'_open U₂' U₂'_open]
  open_of_open_cover_subsets U cover := by
    simp only [Classical.skolem, forall_and] at cover
    obtain ⟨cover, ⟨cover', cover'_open, cover_def⟩, in_cover, cover_sub⟩ := cover
    replace in_cover : ∀x h, x ∈ Set.preimage i (cover' x h) := by
      intro x h
      rw [cover_def]
      exact in_cover x h
    replace cover_sub : ∀x h, Set.preimage i (cover' x h) ⊆ U := by
      intro x h
      rw [cover_def]
      exact cover_sub x h
    clear cover_def cover -- expanded everything in terms of cover'
    exists Set.mk fun x => ∃y, ∃hy, x ∈ cover' y hy
    constructor
    · apply τ.open_of_open_cover_subsets'
      intro x ⟨y, hy, h⟩
      exists ⟨cover' y hy, cover'_open y hy, h⟩
      intro v
      simp
      intro hv
      exists y, hy
    · ext x
      simp
      constructor
      · rintro ⟨y, hy, h⟩
        apply cover_sub y hy
        exact h
      · intro hx
        exists x, hx
        exact in_cover x hx


abbrev subspace_topology (S: Set X): Topology S.subtype := τ.subspace_topology' (@Subtype.val X (· ∈ S))

@[simp]
theorem subspace_topology'_open_def {i: Y → X} (U: Set Y): (τ.subspace_topology' i).is_open U ↔
  ∃U': Set X, τ.is_open U' ∧ Set.preimage i U' = U := by
    simp [subspace_topology']

@[simp]
theorem subspace_topology'_closed_def {i: Y → X} (U: Set Y): (τ.subspace_topology' i).is_closed U ↔
  ∃U': Set X, τ.is_closed U' ∧ Set.preimage i U' = U := by
    simp [is_closed_iff_is_open_complement, ← Set.complement_eq_iff]
    constructor
    · rintro ⟨Uo, Uo_open, rfl⟩
      exists Uo.complement
      simp [Uo_open]
    · rintro ⟨Uc, Uc_closed, rfl⟩
      exists Uc.complement
      simp [Uc_closed]


theorem open_subspace_topology_inclusion_cts {i: Y → X} (subspace_open: τ.is_open (Set.full_image i)): continuous (τ.subspace_topology' i) τ i := by
  apply continuous_of_open_imp_preimage_open
  intro U U_open
  simp
  exists U ∩ Set.full_image i
  constructor
  exact τ.open_inter U U_open (Set.full_image i) subspace_open
  ext y
  simp

theorem subtype_val_cts  {τ: Topology X} {i: Y → X}: continuous (τ.subspace_topology' i) τ i := by
  apply continuous_of_open_imp_preimage_open
  intro U U_open
  exists U



end
/--
  This is a shorthand for the subspace of a whole space which is the image of a function
-/
abbrev image_subspace (τ: Topology Y) (f: X → Y): Topology (Set.full_image f).subtype :=
  τ.subspace_topology (Set.full_image f)

@[simp]
theorem image_subspace_open_def {τ: Topology Y}
  (f: X → Y) (U: Set (Set.full_image f).subtype): (τ.image_subspace f).is_open U ↔
    ∃Uo: Set Y, τ.is_open Uo ∧ Set.preimage Subtype.val Uo = U := by
  simp [image_subspace]

/--
  A map is open if the image of every open set is an open set
-/
def open_map (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀U: Set X, τ₁.is_open U → τ₂.is_open (Set.image f U)

def cts_factor_property {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y) (τ₃: Topology Z) (f: X → Y)
  (f_cont: continuous τ₁ τ₂ f) (f_surj: Surjective f) (k: Y → Z) (open_map_kof: open_map τ₁ τ₃ (k ∘ f)):
open_map τ₂ τ₃ k := by
  intro U U_open
  have fiU_open: τ₁.is_open (U.preimage f) := f_cont.open_imp_preimage_open U U_open
  clear f_cont U_open
  have image_open := open_map_kof (U.preimage f) fiU_open
  simp [f_surj, Set.image_comp] at image_open
  exact image_open

/--
  A map is relatively open if the image of every open set is open in the image subspace topology
-/
def rel_open_map (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀U: Set X, τ₁.is_open U → (τ₂.image_subspace f).is_open (Set.mk fun ⟨_, hy⟩ => hy.choose ∈ U)

def closed_map {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀C: Set X, τ₁.is_closed C → τ₂.is_closed (Set.image f C)

def image_closed_map_closed {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (closed: closed_map τ₁ τ₂ f): τ₂.is_closed (Set.full_image f) := by
    rw [← Set.image_all]
    apply closed
    exact closed_all τ₁




variable {X: Type} (τ: Topology X)

structure Basis where
  is_basis_set: Set X → Prop
  basis_open: ∀B, is_basis_set B → τ.is_open B
  basis_cover: ∀x: X, ∃B, is_basis_set B ∧ x ∈ B
  /-- Every intersection of basis sets has a cover of basis subsets-/
  basis_intersection: ∀B₁, is_basis_set B₁ → ∀B₂, is_basis_set B₂ → ∀x ∈ B₁ ∩ B₂,
   ∃B₃, is_basis_set B₃ ∧ x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂

def open_sets_are_open_basis: τ.Basis where
  is_basis_set := τ.is_open
  basis_open := by simp
  basis_cover := by
    intro x
    exists Set.all
    exact And.intro τ.open_all trivial
  basis_intersection := by
    intro B₁ B₁_open B₂ B₂_open x h
    exists B₁ ∩ B₂
    refine And.intro ?_ (And.intro ?_ ?_)
    exact τ.open_inter _ B₁_open _ B₂_open
    trivial
    exact Set.subset_refl _

def from_basis_sets (is_basis_set: Set X → Prop)
  (basis_cover: ∀x: X, ∃B, is_basis_set B ∧ x ∈ B)
  (basis_intersection: ∀B₁, is_basis_set B₁ → ∀B₂, is_basis_set B₂ → ∀x ∈ B₁ ∩ B₂,
    ∃B₃, is_basis_set B₃ ∧ x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂): Topology X where
  is_open U := ∀x ∈ U, ∃B, is_basis_set B ∧ x ∈ B ∧ B ⊆ U
  open_all := by
    simp
    exact basis_cover
  open_inter := by
    simp
    intro U U_open V V_open x x_in_U x_in_V
    have ⟨B₁, B₁_basis, x_in_B₁, B₁_subset_U⟩ := (U_open x x_in_U)
    have ⟨B₂, B₂_basis, x_in_B₂, B₂_subset_U⟩ := (V_open x x_in_V)
    clear U_open V_open basis_cover
    rcases basis_intersection B₁ B₁_basis B₂ B₂_basis x ⟨x_in_B₁, x_in_B₂⟩ with ⟨B, B_basis, x_in_B, B_subset⟩
    exists B
    refine And.intro B_basis (And.intro x_in_B ?_)
    apply Set.subset_inter
    refine Set.subset_trans _ _ _ ?_ B₁_subset_U
    refine Set.subset_trans _ _ _ B_subset ?_
    exact Set.inter_subset_left B₁ B₂
    refine Set.subset_trans _ _ _ ?_ B₂_subset_U
    refine Set.subset_trans _ _ _ B_subset ?_
    exact Set.inter_subset_right B₁ B₂
  open_of_open_cover_subsets := by
    intro U property x x_in_U
    rcases property x x_in_U with ⟨Uₓ, conds, x_in_Uₓ, Uₓ_subset_U⟩
    rcases conds x x_in_Uₓ with ⟨B, B_basis, x_in_B, B_subset_Uₓ⟩
    exists B
    constructor
    refine B_basis
    constructor
    exact x_in_B
    exact Set.subset_trans _ _ _ B_subset_Uₓ Uₓ_subset_U

@[simp]
theorem from_basis_sets_open_def {X: Type} (is_basis_set: Set X → Prop)
  (basis_cover: ∀x: X, ∃B, is_basis_set B ∧ x ∈ B)
  (basis_intersection: ∀B₁, is_basis_set B₁ → ∀B₂, is_basis_set B₂ → ∀x ∈ B₁ ∩ B₂,
    ∃B₃, is_basis_set B₃ ∧ x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂) (U: Set X):
  (from_basis_sets is_basis_set basis_cover basis_intersection).is_open U ↔ ∀x ∈ U, ∃B, is_basis_set B ∧ x ∈ B ∧ B ⊆ U := by
  unfold from_basis_sets
  simp

end
