
structure Topology (X: Type) where
  -- Predicate which says whether a given set is open
  is_open: (X → Prop) → Prop
  whole_set_open: is_open (fun _ => True)
  intersection_open: ∀U, is_open U → ∀V, is_open V →
    is_open (fun x => U x ∧ V x)
  -- "For any set U, if it is the case that for all x in U there exists an open set
  -- Uₓ such that x ∈ Uₓ and Uₓ ⊆ U, then U is an open set"
  open_cover_subsets_imp_open: ∀U: X → Prop, (∀x: X, U x → ∃Uₓ: X → Prop, is_open Uₓ ∧
    Uₓ x ∧ (∀y: X, Uₓ y → U y)) → is_open U

@[simp]
theorem Topology.whole_set_open' {X: Type} (τ: Topology X): τ.is_open (fun _ => True) := τ.whole_set_open

@[simp]
theorem Topology.empty_set_open {X: Type} (τ: Topology X): τ.is_open (fun _ => False) := by
  apply τ.open_cover_subsets_imp_open
  intro x
  exact False.elim

theorem Topology.open_of_eq_open_set {X: Type} (τ: Topology X) (U₁: X → Prop) {U₂: X → Prop}
  (heq: ∀x, U₁ x ↔ U₂ x) (U₁_open: τ.is_open U₁) : τ.is_open U₂ :=
    have : U₁ = U₂ := by
      funext x
      exact propext (heq x)
    Eq.subst this U₁_open

def discrete_topology (X: Type): Topology X := Topology.mk (is_open := fun _ => True)
  (by simp) (by simp) (by simp)

def indiscrete_topology (X: Type): Topology X :=
  Topology.mk (is_open := fun U =>
    ∀x₁, U x₁ → ∀x₂, U x₂
  ) (whole_set_open := by
    intro _ _ _
    trivial
  ) (intersection_open := by
    intro U U_open V V_open
    intro x₁ h₁ x₂
    constructor
    exact U_open x₁ h₁.left x₂
    exact V_open x₁ h₁.right x₂
  ) (open_cover_subsets_imp_open := by
    intro U property x₁ x₁_in_U x₂
    replace property := property x₁ x₁_in_U
    have : property.choose x₂ := by
      refine property.choose_spec.left x₁ ?_ x₂
      exact property.choose_spec.right.left
    exact property.choose_spec.right.right x₂ this
  )

def empty_topology: Topology Empty := Topology.mk
  (is_open := fun _ => True)
  (whole_set_open :=
  by
    trivial
  ) (intersection_open := by
    intro _ _ _ _
    trivial
  ) (open_cover_subsets_imp_open := by
    intro U _
    trivial
  )

def point_topology: Topology Unit := discrete_topology Unit

theorem point_topology_eq (τ: Topology Unit): τ = point_topology := by
  rcases τ with ⟨τ_is_open, p₁, p₂, p₃⟩
  simp [point_topology, discrete_topology]
  funext U
  apply eq_true
  apply p₃
  intro x Ux
  exists fun _ => True
  refine ⟨p₁, trivial, ?_⟩
  intro y _
  rw [Unit.ext y x]
  assumption


def serpinski_space: Topology Bool := {
  is_open := fun U => U false → U true
  whole_set_open := by
    trivial
  intersection_open := by
    intro U U_open V V_open
    simp
    intro Uf Vf
    exact ⟨U_open Uf, V_open Vf⟩
  open_cover_subsets_imp_open := by
    intro U cond Uf
    replace cond := cond false Uf
    rcases cond with ⟨U₂, yea, U₂f, subset⟩
    apply subset
    apply yea
    assumption
}

@[simp]
def Topology.is_closed {X: Type} (τ: Topology X) (U: X → Prop): Prop := τ.is_open fun x => ¬U x

structure nbhd {X: Type} (is_open: (X → Prop) → Prop) (x: X) where
  in_nbhd: X → Prop
  nbhd_open: is_open in_nbhd
  is_nbhd: in_nbhd x

def Topology.open_nbhd {X: Type} (τ: Topology X) (x: X): Type :=
  nbhd (τ.is_open) x

def Topology.open_nbhd.nbhd_open {X: Type} (τ: Topology X) (x: X)
 (U: τ.open_nbhd x): τ.is_open U.in_nbhd := nbhd.nbhd_open U

def exists_open_nbhd {X: Type} (τ: Topology X) (x: X): τ.open_nbhd x := ⟨fun _ => True, τ.whole_set_open, trivial⟩

theorem Topology.open_cover_subsets_imp_open' {X: Type} (τ: Topology X):
  ∀U: X → Prop, (∀x: X, U x → ∃Uₓ: τ.open_nbhd x, ∀y: X, Uₓ.in_nbhd y → U y) → τ.is_open U := by
  intro U cond
  apply τ.open_cover_subsets_imp_open
  intro x x_in_U
  replace cond := cond x x_in_U
  rcases cond with ⟨Uₓ, Uₓ_subset⟩
  exists Uₓ.in_nbhd
  constructor
  exact Uₓ.nbhd_open
  constructor
  exact Uₓ.is_nbhd
  exact Uₓ_subset

def Topology.whole_set_nbhd {X: Type} (τ: Topology X) (x: X): τ.open_nbhd x := {
  in_nbhd := fun _ => True,
  nbhd_open := τ.whole_set_open,
  is_nbhd := trivial
}

-- A point x is in the interior of a set A when there exists an open neighborhood
-- N of x that is a subset of A.
def Topology.interior {X: Type} (τ: Topology X) (A: X → Prop): X → Prop := fun x =>
  ∃N: τ.open_nbhd x, ∀y: X, N.in_nbhd y → A y

theorem Topology.open_of_interior_superset {X: Type} (τ: Topology X) (U: X → Prop)
  (h: ∀x, U x → τ.interior U x): τ.is_open U := by
    apply τ.open_cover_subsets_imp_open
    intro x Ux
    exists (h x Ux).choose.in_nbhd
    constructor; exact (h x Ux).choose.nbhd_open
    constructor; exact (h x Ux).choose.is_nbhd
    intro y y_in_nbhd
    exact (h x Ux).choose_spec y y_in_nbhd


theorem Topology.interior_is_open {X: Type} (τ: Topology X) (A: X → Prop):
τ.is_open (τ.interior A) := by
  apply τ.open_cover_subsets_imp_open'
  intro x h
  rcases h with ⟨⟨Uₓ, Uₓ_open, x_in_Uₓ⟩, Uₓ_subset_A⟩
  exists {in_nbhd := Uₓ, nbhd_open := Uₓ_open, is_nbhd := x_in_Uₓ}
  intro y y_in_Uₓ
  exists ⟨Uₓ, Uₓ_open, y_in_Uₓ⟩

def Topology.interior_subset {X: Type} (τ: Topology X) (A: X → Prop): ∀x, τ.interior A x → A x := by
  intro x h
  refine h.choose_spec x h.choose.is_nbhd

theorem Topology.interior_empty_set_eq_empty_set {X: Type} (τ: Topology X):
  τ.interior (fun _ => False) = (fun _ => False) := by
  funext x
  refine eq_false ?_
  intro h
  exact τ.interior_subset _ x h

theorem Topology.interior_whole_set_eq_whole_set {X: Type} (τ: Topology X):
  τ.interior (fun _ => True) = (fun _ => True) := by
  funext x
  refine eq_true ?_
  refine Exists.intro (Topology.open_nbhd.mk (fun _ => True) ?_ ?_) ?_
  exact τ.whole_set_open
  exact True.intro
  intro _ _
  exact True.intro

structure Topology.Basis {X: Type} (τ: Topology X) where
  is_basis_set: (X → Prop) → Prop
  basis_open: ∀B, is_basis_set B → τ.is_open B
  basis_cover: ∀x: X, ∃B, is_basis_set B ∧ B x
  basis_intersection: ∀B₁, is_basis_set B₁ → ∀B₂, is_basis_set B₂ → ∀x: X,
    B₁ x → B₂ x → ∃B₃, is_basis_set B₃ ∧ B₃ x ∧ (∀y:X, B₃ y → B₁ y ∧ B₂ y)

def Topology.open_sets_are_open_basis {X: Type} (τ: Topology X): τ.Basis :=
  Basis.mk (is_basis_set := τ.is_open) (basis_open := by
    intro b
    exact id
  ) (basis_cover := by
    intro x
    exists (fun _ => True)
    exact And.intro τ.whole_set_open True.intro
  ) (basis_intersection := by
    intro B₁ B₁_open B₂ B₂_open x x_in_B₁ x_in_B₂
    exists (fun x => B₁ x ∧ B₂ x)
    refine And.intro ?_ (And.intro ?_ ?_)
    exact τ.intersection_open _ B₁_open _ B₂_open
    trivial
    intro y
    exact id
  )

def Topology.from_basis_sets {X: Type} (is_basis_set: (X → Prop) → Prop)
  (basis_cover: ∀x: X, ∃B, is_basis_set B ∧ B x)
  (basis_intersection: ∀B₁, is_basis_set B₁ → ∀B₂, is_basis_set B₂ → ∀x: X,
    B₁ x → B₂ x → ∃B₃, is_basis_set B₃ ∧ B₃ x ∧ (∀y:X, B₃ y → B₁ y ∧ B₂ y)): Topology X :=
  Topology.mk (is_open := fun U =>
    ∀x: X, U x → ∃B, is_basis_set B ∧ B x ∧ (∀y: X, B y → U y)
  ) (whole_set_open := by
    simp
    exact basis_cover
  ) (intersection_open := by
    simp
    intro U U_open V V_open x x_in_U x_in_V
    have ⟨basis₁, basis₂⟩ := And.intro (U_open x x_in_U) (V_open x x_in_V)
    clear U_open V_open basis_cover
    rcases basis_intersection basis₁.choose (basis₁.choose_spec.left)
                      basis₂.choose (basis₂.choose_spec.left)
                      x (basis₁.choose_spec.right.left)
                      (basis₂.choose_spec.right.left) with ⟨B, B_basis, x_in_B, B_subset⟩
    exists B
    refine And.intro B_basis (And.intro x_in_B ?_)
    intro y By
    have := B_subset y By
    refine And.intro ?_ ?_
    exact basis₁.choose_spec.right.right y this.left
    exact basis₂.choose_spec.right.right y this.right
  ) (open_cover_subsets_imp_open := by
    intro U property x x_in_U
    rcases property x x_in_U with ⟨Uₓ, conds, x_in_Uₓ, Uₓ_subset⟩
    exists (conds x x_in_Uₓ).choose
    constructor
    refine (conds x x_in_Uₓ).choose_spec.left
    constructor
    exact (conds x x_in_Uₓ).choose_spec.right.left
    intro y h
    refine Uₓ_subset y ?_
    exact (conds x x_in_Uₓ).choose_spec.right.right y h
  )

def Topology.hausdorff {X: Type} (τ: Topology X): Prop :=
  ∀x: X, ∀y: X, (∀U: τ.open_nbhd x, ∀V: τ.open_nbhd y,
    ∃p: X, U.in_nbhd p ∧ V.in_nbhd p) → x = y

def hausdorff_separates {X: Type} {τ: Topology X} (h: τ.hausdorff): ∀x y: X, x ≠ y →
  (∃U: τ.open_nbhd x, ∃V: τ.open_nbhd y, ∀p: X, U.in_nbhd p → ¬V.in_nbhd p) := by
  intro x y hneq
  have := hneq ∘ h x y
  simp only [imp_false, Classical.not_forall, not_exists, not_and] at this
  exact this

theorem empty_hausdorff: Topology.hausdorff empty_topology := Empty.rec

theorem discrete_hausdorff {X: Type}: Topology.hausdorff (discrete_topology X) := by
  intro x y property
  replace property := property ⟨(fun p => x = p), trivial, rfl⟩
            ⟨(fun p => p = y), trivial, rfl⟩
  exact Eq.trans property.choose_spec.left property.choose_spec.right

instance hausdorff_indiscrete_imp_subsingleton:
  Topology.hausdorff (indiscrete_topology X) → Subsingleton X := by
  intro hausdorff
  apply Subsingleton.intro
  intro x y
  apply hausdorff
  rintro ⟨U, _, x_in_U⟩ ⟨V, V_open, y_in_V⟩
  exists x
  refine And.intro x_in_U ?_
  exact V_open y y_in_V x

def Topology.frechet {X: Type} (τ: Topology X) :=
  ∀x: X, τ.is_open (fun y => x ≠ y)

theorem discrete_frechet {X: Type}: Topology.frechet (discrete_topology X) := by
  intro _
  trivial

instance indiscrete_frechet_imp_subsingleton {X: Type}:
  Topology.frechet (indiscrete_topology X) → Subsingleton X := by
  intro frechet
  apply Subsingleton.intro
  intro x y
  apply Classical.byContradiction
  intro hne
  have := (frechet x) y hne x
  contradiction

theorem exists_external_nbhd_imp_frechet {X: Type} (τ: Topology X):
  (∀x y: X, x ≠ y → ∃U: τ.open_nbhd x, ¬U.in_nbhd y) → τ.frechet := by
    intro h x
    apply τ.open_cover_subsets_imp_open
    intro y ne
    have := (h y x ne.symm)
    exists this.choose.in_nbhd
    constructor; exact this.choose.nbhd_open
    constructor; exact this.choose.is_nbhd
    intro y₁ contained
    intro heq
    cases heq
    apply this.choose_spec contained


theorem hausdorff_imp_frechet {X: Type} (τ: Topology X) (h: Topology.hausdorff τ):
  Topology.frechet τ := by
  intro x
  apply τ.open_cover_subsets_imp_open
  -- Given two unequal points x and y, we need to find an open set that contains
  -- y but does not contain x
  intro y hneq
  -- We start by showing that there must exist two disjoint open nbhds of
  -- x and y respectively
  replace h: ∃U: τ.open_nbhd x, ∃V: τ.open_nbhd y, ∀p, U.in_nbhd p → ¬V.in_nbhd p := by
    have h' := hneq ∘ h x y
    simp at h'
    exact h'
  clear hneq
  -- unpack what it means for τ to be hausdorff
  rcases h with ⟨U, V, U_V_disjoint⟩

  -- We claim that the open set containing y satisfies the goal
  exists V.in_nbhd
  constructor; exact V.nbhd_open
  constructor; exact V.is_nbhd
  -- lastly we need to prove that for any z, if z is in V,
  -- then z cannot be equal to x
  intro _ h₂ hneq₂
  -- BWOC, assume z is in V and x = z, and then substitute x=z everywhere
  cases hneq₂
  -- This is a contradiction because of the disjointedness condition says that
  -- x being in both V an dU is a contradiction
  exact U_V_disjoint x U.is_nbhd h₂


def continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀U: Y → Prop, τ₂.is_open U → τ₁.is_open (fun x => U (f x))

def id_continuous {X: Type} {τ: Topology X} : continuous τ τ id := by
  intro U U_open
  exact U_open

def comp_continuous {X Y Z: Type} {τ₁: Topology X} (τ₂: Topology Y) {τ₃: Topology Z}
    (f: X → Y) (g: Y → Z) (f_cont: continuous τ₁ τ₂ f)
    (g_cont: continuous τ₂ τ₃ g): continuous τ₁ τ₃ (g ∘ f) := by
  intro U U_open
  exact f_cont (fun y => U (g y)) (g_cont U U_open)


def fun_indiscrete_to_frechet_constant {X Y: Type} (τ: Topology Y) (Y_frechet: τ.frechet)
  (f: X → Y) (h: continuous (indiscrete_topology X) τ f): ∀x:X, ∀y:X, f x = f y := by
  intro x y
  have ne_f_x_inv_open := h _ (Y_frechet (f x))
  refine Classical.byContradiction (fun hne => ?_)
  exact ne_f_x_inv_open y hne x rfl

def fun_discrete_continuous {X Y: Type} (τ₂: Topology Y) (f: X → Y):
  continuous (discrete_topology X) τ₂ f := by
    intro U _
    trivial

def continuous_of_inv_closed_sets_closed {X Y: Type} (τX: Topology X) (τY: Topology Y)
  (f: X → Y) (h: ∀C: Y → Prop, τY.is_closed C → τX.is_closed (C ∘ f)): continuous τX τY f := by
  intro U U_open
  replace h := h (fun x => ¬ U x)
  simp at *
  exact h U_open

-- Note: I renamed this from quotient topology because
-- Its not exactly the same. Im not entirely sure what to call it
-- but according to wikipedia final topology is a nice option.
def final_topology {X Y: Type} (τ: Topology X) (f: X → Y):
  Topology Y := Topology.mk (
    -- A set is open in Y if it's preimage is open in X
    is_open := fun U => τ.is_open (U ∘ f)
  ) (
    whole_set_open := by
    simp
    exact τ.whole_set_open
  ) (
    intersection_open := by
    intro U U_open V V_open
    change τ.is_open (fun x => (U ∘ f) x ∧ (V ∘ f) x)
    exact τ.intersection_open (U ∘ f) U_open (V ∘ f) V_open
  ) (
    open_cover_subsets_imp_open := by
    intro U cond
    apply τ.open_cover_subsets_imp_open
    intro x ux; replace cond := cond (f x) ux
    exists cond.choose ∘ f
    constructor
    exact cond.choose_spec.left
    constructor;
    exact cond.choose_spec.right.left
    intro x' yea
    exact cond.choose_spec.right.right (f x') yea
  )

theorem final_map_continuous {X Y: Type} (τ: Topology X) (f: X → Y):
  continuous τ (final_topology τ f) f := by
    intro U U_open
    exact U_open

-- A point x is in the closure of U iff for every closed set S which is
-- a superset of U, x is in S
def Topology.closure {X: Type} (τ: Topology X) (U: X → Prop): X → Prop :=
  fun x => ∀S: X→ Prop, τ.is_closed S → (∀y, U y → S y) → S x

theorem Topology.is_closed_closure {X: Type} (τ: Topology X) (U: X → Prop):
  τ.is_closed (τ.closure U) := by
  simp [Topology.closure]
  apply τ.open_cover_subsets_imp_open'
  --apply τ.open_of_interior_superset
  intro x cond

  exists {
    in_nbhd := fun x => ¬cond.choose x,
    nbhd_open := cond.choose_spec.left,
    is_nbhd := cond.choose_spec.right.right
  }
  intro y h
  exists fun y => cond.choose y
  constructor
  simp
  exact cond.choose_spec.left
  constructor
  simp
  exact cond.choose_spec.right.left
  simp
  exact h

theorem Topology.closure_closed_eq_self {X: Type} (τ: Topology X) (U: X → Prop):
  τ.is_closed U ↔ U = τ.closure U := by
  constructor
  intro u
  funext x
  apply Eq.propIntro
  intro h S _ h₃
  apply h₃
  assumption
  intro h
  apply h
  assumption
  exact fun _ => id
  intro heq
  rw [heq]
  exact τ.is_closed_closure U

theorem Topology.closure_superset {X: Type} (τ: Topology X) (S: X → Prop):
  ∀x, S x → τ.closure S x := by
  intro x x_in_S C _ C_superset
  exact C_superset x x_in_S

theorem topologies_equal_of_same_open_sets {X: Type} (τ₁ τ₂: Topology X)
  (heq: τ₁.is_open = τ₂.is_open): τ₁ = τ₂ := by
  cases τ₁ <;> cases τ₂
  case mk.mk open1 _ _ _ open2 _ _ _=>
  simp at *
  exact heq

theorem topologies_equal_of_same_closed_sets {X: Type} (τ₁ τ₂: Topology X)
  (heq: τ₁.is_closed = τ₂.is_closed): τ₁ = τ₂ := by
  apply topologies_equal_of_same_open_sets
  funext U
  have := funext_iff.mp heq (fun x => ¬U x)
  simp at this
  exact propext this

@[simp]
theorem Topology.whole_set_closed {X: Type} (τ: Topology X): τ.is_closed (fun _ => True) := by
  unfold Topology.is_closed
  simp
  --exact τ.empty_set_open

@[simp]
theorem Topology.empty_set_closed {X: Type} (τ: Topology X) : τ.is_closed (fun _ => False) := by
  unfold Topology.is_closed
  simp
  --exact τ.whole_set_open


def exam_problem_1 {X: Type} (τ: Topology X): Topology (Option X) := Topology.mk
  (is_open :=
    fun U => (
      (U none) ∧ ∃UX, (τ.is_open UX ∧ ∀x, U (some x) ↔ UX x)
    ) ∨ ∀x, ¬U x
  ) (whole_set_open := by
    left
    simp
    exists (fun _ => True)
    simp
  ) (intersection_open := by
    simp
    intro U U_open V V_open
    cases U_open
    case inr h₁ =>
      right; intro x Ux Vx
      exact h₁ x Ux
    case inl h₁ =>
    cases V_open
    case inr h₂ =>
      right; intro x Ux Vx
      exact h₂ x Vx
    case inl h₂ =>
      left
      constructor
      exact ⟨h₁.left, h₂.left⟩
      have X_int := τ.intersection_open h₁.right.choose h₁.right.choose_spec.left h₂.right.choose
        h₂.right.choose_spec.left
      exists (fun x => h₁.right.choose x ∧ h₂.right.choose x)
      constructor; assumption
      intro x;
      constructor
      intro h
      constructor
      exact (h₁.right.choose_spec.right x).mp h.left
      exact (h₂.right.choose_spec.right x).mp h.right
      intro h
      constructor
      exact (h₁.right.choose_spec.right x).mpr h.left
      exact (h₂.right.choose_spec.right x).mpr h.right
  ) (open_cover_subsets_imp_open := by
    intro U open_cover_subsets
    apply Classical.or_iff_not_imp_right.mpr
    intro U_non_empty; simp at U_non_empty
    have ⟨Uₓ, a, b, c⟩:= open_cover_subsets U_non_empty.choose U_non_empty.choose_spec
    simp at a
    cases a
    case inr a =>
      exact absurd b (a U_non_empty.choose)
    case inl a =>
      constructor
      apply c
      exact a.left
      exists a.right.choose
      constructor
      exact a.right.choose_spec.left
      intro x
      constructor
      intro x_in_U
      refine (a.right.choose_spec.right x).mp ?_
      sorry
      sorry
  )


theorem exam_problem_3 {X: Type} (τ: Topology X) (h: ∀U: X→ Prop, ∀x, τ.closure U x):
  τ = indiscrete_topology X := by
  apply topologies_equal_of_same_closed_sets
  funext S
  apply Eq.propIntro
  intro S_closed
  simp [indiscrete_topology]
  intro x₁ x₁_not_in_S x₂ _
  apply x₁_not_in_S
  rw [(τ.closure_closed_eq_self S).mp S_closed]
  exact h S x₁
  intro h₂
  by_cases ∃x, S x
  case pos non_empty =>
    have : S = fun _ => True := by
      funext x
      apply eq_true
      simp [indiscrete_topology] at h₂
      apply Classical.not_not.mp
      intro x_not_in_S
      exact h₂ x x_not_in_S non_empty.choose non_empty.choose_spec
    rw [this]
    exact τ.whole_set_closed
  case neg empty =>
    have : S = fun _ => False := by
      funext x
      apply eq_false
      intro x_in_S
      apply empty
      exists x
    rw [this]
    exact τ.empty_set_closed

def homeomorphism {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∃f_inv: Y → X, f ∘ f_inv = id ∧ f_inv ∘ f = id ∧ continuous τ₁ τ₂ f ∧ continuous τ₂ τ₁ f_inv

def id_homeomorphism {X: Type} (τ: Topology X): homeomorphism τ τ id := by
  exists id
  constructor; rfl
  constructor; rfl
  constructor; exact id_continuous
  exact id_continuous

def homogeneous {X: Type} (τ: Topology X):= ∀x₁, ∀x₂, ∃e: X→X, homeomorphism τ τ e ∧ e x₁ = x₂

theorem exam_problem_5 {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (homeomorphic: homeomorphism τ₁ τ₂ f) (h: homogeneous τ₁): homogeneous τ₂ := by
  intro y₁ y₂
  cases homeomorphic; case intro f_inv cond =>
  rcases h (f_inv y₁) (f_inv y₂) with ⟨e, e_homeo, e_inv⟩
  exists f ∘ e ∘ f_inv
  constructor
  exists f ∘ e_homeo.choose ∘ f_inv
  constructor
  · change f ∘ e ∘ (f_inv ∘ f) ∘ e_homeo.choose ∘ f_inv = id
    rw [cond.right.left]
    change f ∘ (e ∘ e_homeo.choose) ∘ f_inv = id
    rw [e_homeo.choose_spec.left]
    change f ∘ f_inv = id
    exact cond.left
  constructor
  · change f ∘ e_homeo.choose ∘ (f_inv ∘ f) ∘ e ∘ f_inv = id
    rw [cond.right.left]
    change f ∘ (e_homeo.choose ∘ e) ∘ f_inv = id
    rw [e_homeo.choose_spec.right.left]
    change f ∘ f_inv = id
    exact cond.left
  constructor
  · refine comp_continuous τ₁ ?_ ?_ ?_ ?_
    refine comp_continuous τ₁ ?_ ?_ ?_ ?_
    exact cond.right.right.right
    exact e_homeo.choose_spec.right.right.left
    exact cond.right.right.left
  · refine comp_continuous τ₁ ?_ ?_ ?_ ?_
    refine comp_continuous τ₁ ?_ ?_ ?_ ?_
    exact cond.right.right.right
    exact e_homeo.choose_spec.right.right.right
    exact cond.right.right.left
  · change f (e (f_inv y₁)) = y₂
    rw [e_inv]
    change (f ∘ f_inv) y₂ = y₂
    rw [cond.left]
    rfl



theorem interior_subset_closure {X: Type} (τ: Topology X) (A: X → Prop):
  ∀x, τ.interior A x → τ.closure A x := by
    intro x x_in_interior
    apply τ.closure_superset
    exact τ.interior_subset A x x_in_interior


def Topology.boundary {X: Type} (τ: Topology X) (A: X → Prop): X → Prop :=
  fun x => ∀U: X→ Prop, τ.is_open U → U x → (∃i, U i ∧ A i) ∧ (∃o, U o ∧ ¬A o)

def boundary_empty_set_empty {X: Type} (τ: Topology X):
  τ.boundary (fun _ => False) = fun _ => False := by
    funext x
    apply Eq.propIntro
    -- ⊆
    intro x_in_boundary
    simp [Topology.boundary] at x_in_boundary
    apply x_in_boundary (fun _ => True)
    exact τ.whole_set_open
    trivial
    --⊇
    exact False.elim


def boundary_whole_set_empty {X: Type} (τ: Topology X):
  τ.boundary (fun _ => True) = fun _ => False := by
    funext x
    apply Eq.propIntro
    intro x_in_boundary
    simp [Topology.boundary] at x_in_boundary
    apply x_in_boundary (fun _ => True)
    exact τ.whole_set_open
    trivial
    exact False.elim

def boundary_interior_disjoint {X: Type} (τ: Topology X) (A: X → Prop):
  ∀x, ¬(τ.interior A x ∧ τ.boundary A x) := by
    rintro x ⟨h_int, h_bound⟩
    have exists_outside := (h_bound (τ.interior A)
        (τ.interior_is_open A)
        h_int).right
    exact exists_outside.choose_spec.right (τ.interior_subset A
      exists_outside.choose
      exists_outside.choose_spec.left)

def boundary_subset_closure {X: Type} (τ: Topology X) (A: X → Prop):
  ∀x, τ.boundary A x → τ.closure A x := by
    intro x x_boundary
    intro S S_closed S_superset
    apply Classical.byContradiction
    intro x_not_in_S
    have := (x_boundary (fun x => ¬S x) S_closed x_not_in_S).left
    apply this.choose_spec.left
    apply S_superset
    exact this.choose_spec.right

def Topology.open_of_every_point_in {X: Type} (τ: Topology X) (U: X → Prop):
  (∀x, U x) → τ.is_open U := by
    intro h
    have : U = fun _ => True := by
      funext x
      apply eq_true
      exact h x
    rw [this]
    exact τ.whole_set_open

def Topology.open_of_no_point_in {X: Type} (τ: Topology X) (U: X → Prop):
  (∀x, ¬U x) → τ.is_open U := by
    intro h
    have : U = fun _ => False := by
      funext x
      apply eq_false
      exact h x
    rw [this]
    exact τ.empty_set_open

def product_topology {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y): Topology (X × Y) := {
  is_open := fun P => ∀x: X, ∀y: Y, P (x,y) → ∃U: τ₁.open_nbhd x, ∃V: τ₂.open_nbhd y,
    ∀x': X, U.in_nbhd x' → ∀y': Y, V.in_nbhd y' → P (x',y')
  whole_set_open := by
    dsimp
    intro x y _
    exists τ₁.whole_set_nbhd x
    exists τ₂.whole_set_nbhd y
    intro x' x'_in y' y'_in
    trivial
  intersection_open := by
    dsimp
    intro U U_open V V_open x y ⟨a,b⟩
    replace U_open := U_open x y a
    replace V_open := V_open x y b
    rcases U_open with ⟨U₁, V₁, c₁⟩
    rcases V_open with ⟨U₂, V₂, c₂⟩
    exists {
      in_nbhd := fun x => U₁.in_nbhd x ∧ U₂.in_nbhd x,
      nbhd_open := τ₁.intersection_open U₁.in_nbhd U₁.nbhd_open U₂.in_nbhd U₂.nbhd_open,
      is_nbhd := ⟨U₁.is_nbhd, U₂.is_nbhd⟩
    }
    exists {
      in_nbhd := fun x => V₁.in_nbhd x ∧ V₂.in_nbhd x,
      nbhd_open := τ₂.intersection_open V₁.in_nbhd V₁.nbhd_open V₂.in_nbhd V₂.nbhd_open,
      is_nbhd := ⟨V₁.is_nbhd, V₂.is_nbhd⟩
    }
    dsimp
    intro x' h₁ y' h₂
    constructor
    exact c₁ x' h₁.left y' h₂.left
    apply c₂ x' h₁.right y' h₂.right
  open_cover_subsets_imp_open := by
    dsimp
    intro U cover_cond x y Uxy
    replace cover_cond := cover_cond (x,y) Uxy
    rcases cover_cond with ⟨Uxy_set, openn, member, subset⟩
    exists (openn x y member).choose
    exists (openn x y member).choose_spec.choose
    intro x' yea₁ y' yea₂
    apply subset
    exact (openn x y member).choose_spec.choose_spec x' yea₁ y' yea₂
}

theorem fst_continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  continuous (product_topology τ₁ τ₂) τ₁ Prod.fst := by
  intro U U_open
  simp [product_topology]
  intro x y Ux
  exists {in_nbhd := U, nbhd_open := U_open, is_nbhd := Ux}
  exists τ₂.whole_set_nbhd y
  dsimp
  intro x' yea₁ _ _
  assumption


theorem snd_continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  continuous (product_topology τ₁ τ₂) τ₂ Prod.snd := by
    intro V V_open
    simp [product_topology]
    intro x y Vy
    exists τ₁.whole_set_nbhd x
    exists Topology.open_nbhd.mk V V_open Vy
    dsimp
    intro _ _ _
    exact id


theorem diagonal_closed_of_hausdorff {X: Type} (τ: Topology X) (h: τ.hausdorff):
  (product_topology τ τ).is_closed (fun p => p.fst = p.snd) := by
  simp [product_topology]
  intro x y hneq
  rcases hausdorff_separates h x y hneq with ⟨U, V, disjoint⟩
  exists U; exists V;
  intro x' x'nbhd y' y'nbhd heq
  cases heq
  exact disjoint x' x'nbhd y'nbhd

theorem hausdorff_of_diagonal_closed {X: Type} (τ: Topology X)
(h: (product_topology τ τ).is_closed (fun p => p.fst = p.snd)): τ.hausdorff := by
  simp [product_topology] at h
  intro x y cond
  apply Classical.byContradiction
  intro hneq
  replace h := h x y hneq
  rcases h with ⟨U,V,h⟩
  replace cond := cond U V
  rcases cond with ⟨p, Up, Vp⟩
  exact h p Up p Vp rfl

def Topology.subspace_topology {X: Type} (τ: Topology X) (pred: X → Prop):
  Topology {x: X // (pred x)} := Topology.mk (
    is_open := fun U  =>
      ∃Uo: X → Prop, τ.is_open Uo ∧ U = Uo ∘ Subtype.val
  ) (
    whole_set_open := by
      exists fun _ => True
      simp
      funext _
      rfl
  ) (
    intersection_open := by
      rintro U_restr ⟨U, U_open, heq₁⟩ V_restr ⟨V, V_open, heq₂⟩
      cases heq₁ <;> cases heq₂
      exists fun x => U x ∧ V x
      constructor
      exact τ.intersection_open U U_open V V_open
      funext x
      simp
  ) (
    open_cover_subsets_imp_open := by
      intro U cond
      dsimp at cond
      -- This Uo is the union of the cover of U in the subspace
      exists fun x => ∃x': {x // pred x}, ∃h: U x', (cond x' h).choose_spec.left.choose x
      constructor
      · apply τ.open_cover_subsets_imp_open'
        rintro x ⟨x', hx, w⟩
        exists {
          in_nbhd := (cond x' hx).choose_spec.left.choose,
          nbhd_open := (cond x' hx).choose_spec.left.choose_spec.left,
          is_nbhd := w
        }
        intro y hy
        exists x'
        exists hx
      · funext x'
        apply Eq.propIntro
        intro h
        have := (cond x' h).choose_spec.left.choose_spec.right
        exists x'; exists h
        replace this := funext_iff.mp this x'
        dsimp at this
        rw [<- this]
        exact (cond x' h).choose_spec.right.left

        dsimp
        intro ⟨x, hx, what⟩
        refine (cond x hx).choose_spec.right.right x' ?_
        rw [(cond x hx).choose_spec.left.choose_spec.right]
        exact what
  )

@[simp]
def subspace_open_nbhd {X: Type} {τ: Topology X} {pred: X → Prop} (x: X) (pred_x: pred x)
(U: τ.open_nbhd x): ((τ.subspace_topology pred).open_nbhd ⟨x, pred_x⟩) := by
  constructor
  case in_nbhd =>
    exact fun ⟨p, _⟩ => U.in_nbhd p
  dsimp [Topology.subspace_topology]
  exists U.in_nbhd
  constructor
  exact U.nbhd_open
  funext ⟨y, _⟩
  simp
  exact U.is_nbhd

def Topology.Compact {X: Type} (τ: Topology X): Prop := ∀Y, ∀τ₂: Topology Y,
  ∀C: X × Y → Prop, (product_topology τ τ₂).is_open C → τ₂.is_open (fun y => ∀x, C (x,y))

#check ∀X, ∀τ: Topology X, ∀Y, ∀τ₂: Topology Y, ∀C: X × Y → Prop,
  (∀x: X, ∀y: Y, C (x,y) → ∃U: τ.open_nbhd x, ∃V: τ₂.open_nbhd y,
    ∀x':X, U.in_nbhd x' → ∀y':Y, V.in_nbhd y' → C (x', y'))
  → τ₂.is_open (fun y => ∀x, C (x,y))

#check ∀X, ∀τ: Topology X, ∀Y, ∀τ₂: Topology Y, ∀C: X × Y → Prop,
  ∀y₀: Y, (∀x, C (x,y₀)) →
  (∀x: X, ∀y: Y, C (x,y) → ∃U: τ.open_nbhd x, ∃V: τ₂.open_nbhd y,
    ∀x':X, U.in_nbhd x' → ∀y':Y, V.in_nbhd y' → C (x', y'))
  → ∃W: τ₂.open_nbhd y₀, ∀y': Y, W.in_nbhd y' → ∀x': X, C (x', y')

def point_compact (τ: Topology Unit): τ.Compact := by
  intro Y τ₂ C pC_closed
  apply τ₂.open_cover_subsets_imp_open'
  intro x empty
  replace empty : C ((), x) := empty ()
  replace pC_closed := pC_closed () x empty
  rcases pC_closed with ⟨singleton, V, c⟩
  exists V
  replace c := c () singleton.is_nbhd
  intro y Vy a
  rw [Unit.ext a ()]
  exact c y Vy


theorem image_compact_cont_surj_is_compact {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (f_cont: continuous τ₁ τ₂ f) (f_surj: ∀y: Y, ∃x, f x = y) (cpct: τ₁.Compact):  τ₂.Compact := by
  dsimp [Topology.Compact, product_topology] at *
  intro Z τZ C C_closed
  -- we'll use the fact that the image of the projeciton of this set is closed
  replace cpct := cpct Z τZ (fun (x,y) => C (f x, y))
  dsimp at cpct
  apply τZ.open_of_eq_open_set (fun x => ∀ x_1, C (f x_1, x))
  · intro x
    constructor
    intro h y
    rw [<- (f_surj y).choose_spec]
    exact h (f_surj y).choose
    intro h x
    exact h (f x)
  apply cpct
  clear cpct f_surj
  intro x y nCfxy
  rcases C_closed (f x) y nCfxy with ⟨U, V, yea⟩
  clear C_closed
  exists {
    in_nbhd := U.in_nbhd ∘ f
    nbhd_open := by
      apply f_cont -- Preimage of U is open by continuity!
      exact U.nbhd_open
    is_nbhd := U.is_nbhd
  }
  exists V
  intro x' f_invUx' z' Vz'
  dsimp at f_invUx'
  exact yea (f x') f_invUx' z' Vz'

theorem tube_lemma {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (Y_cpct: τ₂.Compact)
  (x₀: X) (U: Y×X→ Prop) (U_open: (product_topology τ₂ τ₁).is_open U) (h: ∀y: Y, U (y, x₀)):
    ∃W: τ₁.open_nbhd x₀, ∀x, W.in_nbhd x → ∀y, U (y, x) := by
    exists {
      in_nbhd := fun y => ∀x, U (x,y),
      nbhd_open := Y_cpct X τ₁ U U_open,
      is_nbhd := h
    }
    intro x x_in_W y
    dsimp at x_in_W
    exact x_in_W y


theorem infinite_discrete_set_not_cpct: ¬((discrete_topology Nat).Compact) := by
  dsimp [discrete_topology, Topology.Compact, product_topology]
  intro h
  replace h := h Nat {
    is_open := fun U => U 0 ∨ ∀x, ¬U x
    whole_set_open := by left; trivial
    intersection_open := by
      intro U U_open V V_open
      cases U_open
      case inr h =>
        right
        intro x h₂
        exact h x (h₂.left)
      case inl h =>
      cases V_open
      case inr h =>
        right
        intro x h₂
        exact h x (h₂.right)
      case inl h₂ =>
        left
        exact ⟨h, h₂⟩
    open_cover_subsets_imp_open := by
      dsimp
      intro U cond
      apply Classical.or_iff_not_imp_right.mpr
      intro U_nonempty
      simp only [Classical.not_forall, Classical.not_not] at U_nonempty
      rcases U_nonempty with ⟨x₀, U_x₀⟩
      replace cond := cond x₀ U_x₀
      rcases cond with ⟨Uₓ, mb_mt ,i, k⟩
      have : Uₓ 0 := by
        cases mb_mt
        case inl => assumption
        case inr h =>
          exact absurd i (h x₀)
      exact k 0 this
  }


def cofinite_topology {X: Type}: Topology X := Topology.from_basis_sets (
    is_basis_set := fun B => ∀x:X, ¬B x → ∀y, B y ∨ x = y
  ) (basis_cover := by
    intro x
    dsimp
    exists fun _ => True
    simp
  ) (basis_intersection := by
    intro B₁ B₁_basis B₂ B₂_basis x B₁x B₂x

  )


def Topology.approaches {X: Type} (τ: Topology X) (sequence: Nat → X) (L: X): Prop :=
  ∀U: τ.open_nbhd L, ∃N, ∀n, (U.in_nbhd ∘ sequence) (N + n)

theorem unique_limits_of_hausdorff {X: Type} (τ: Topology X) (h: τ.hausdorff)
  (sequence: Nat → X) (L₁ L₂: X) (aL₁: τ.approaches sequence L₁) (aL₂: τ.approaches sequence L₂):
    L₁ = L₂ := by
  simp [Topology.approaches, Topology.hausdorff] at *
  apply h L₁ L₂
  intro U V
  replace aL₁ := aL₁ U
  replace aL₂ := aL₂ V
  exists sequence $ aL₁.choose + aL₂.choose
  constructor
  exact aL₁.choose_spec aL₂.choose
  rw [Nat.add_comm]
  exact aL₂.choose_spec aL₁.choose


theorem frechet_of_unique_limits {X: Type} (τ: Topology X):
  (∀(sequence: Nat → X), ∀(L₁ L₂: X), τ.approaches sequence L₁ →
  τ.approaches sequence L₂ → L₁ = L₂) → τ.frechet := by
  simp [Topology.frechet]
  intro unique_limits
  intro x
  apply τ.open_cover_subsets_imp_open'
  intro y hneq
  have const_x_not_approaches_y: ¬τ.approaches (fun _ => x) y := by
    replace unique_limits := unique_limits (fun _ => x) x y
    intro h
    apply hneq
    refine unique_limits ?_ h
    intro U; exists 0
    simp
    exact U.is_nbhd
  simp [Topology.approaches] at const_x_not_approaches_y
  exists const_x_not_approaches_y.choose
  intro y₂ h heq
  rw [← heq] at h
  exact const_x_not_approaches_y.choose_spec h


-- This definition does not directly depend on `Z` being a topological space
-- So I am leaving that part out!
def fiber_prod_topology {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y)
  (f: X → Z) (g: Y → Z): Topology {p: X × Y // f p.1 = g p.2} :=
   (product_topology τ₁ τ₂).subspace_topology (fun p => f p.1 = g p.2)

def continuous_fiber_fst {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Z) (g: Y → Z):
  continuous (fiber_prod_topology τ₁ τ₂ f g) τ₁ (fun p => p.val.fst) := by
    intro U U_open
    simp [fiber_prod_topology, product_topology, Topology.subspace_topology]
    exists fun p => U p.fst
    constructor
    · intro x y x_in_U
      exists {in_nbhd := U, nbhd_open := U_open, is_nbhd := x_in_U}
      exists τ₂.whole_set_nbhd y
      intro x' x'_in_U y' _
      exact x'_in_U
    · rfl

def continuous_fiber_snd {X Y Z: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Z) (g: Y → Z):
  continuous (fiber_prod_topology τ₁ τ₂ f g) τ₂ (fun p => p.val.snd) := by
    intro U U_open
    simp [fiber_prod_topology, product_topology, Topology.subspace_topology]
    exists fun p => U p.snd
    constructor
    · intro x y x_in_U
      exists τ₁.whole_set_nbhd x
      exists {in_nbhd := U, nbhd_open := U_open, is_nbhd := x_in_U}
      intro x' _ y' y'_in_U
      exact y'_in_U
    · rfl


def Topology.image_subspace {X Y: Type} {τ: Topology Y}
  (f: X → Y): Topology {y: Y // ∃x, y = f x} := --τ₂.subspace_topology (fun y => ∃x, y = f x)
  {
    is_open := fun U => ∃Uo: Y → Prop, τ.is_open Uo ∧ U = Uo ∘ Subtype.val,
    whole_set_open := by
      exists fun _ => True
      simp
      funext y
      simp
    intersection_open := by
      intro U' ⟨U, U_open, heq₁⟩ V' ⟨V, V_open, heq₂⟩
      cases heq₁
      cases heq₂
      exists (fun y => U y ∧ V y)
      constructor
      exact τ.intersection_open U U_open V V_open
      funext ⟨y, hy⟩
      dsimp
    open_cover_subsets_imp_open := by
      intro U cond
      dsimp at cond
      exists (fun y => ∃x': X,
        let y': {y: Y // ∃x, y = f x} := ⟨f x', by exists x'⟩
        ∃h: U y', (cond y' h).choose_spec.left.choose y
      )
      dsimp
      constructor
      apply τ.open_cover_subsets_imp_open
      intro y ⟨x, c, k⟩
      rcases cond ⟨f x, Exists.intro x rfl⟩ c with ⟨U_,⟨U'', U''_open, heq⟩,U_fx, subset⟩
      cases heq
      dsimp at *
      exists U''
      constructor; assumption
      constructor; sorry;
      intro y' U''y'
      sorry
      sorry
  }


def open_map {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀U: X → Prop, τ₁.is_open U → τ₂.is_open (fun y => ∃x, y = f x ∧ U x)

def cts_factor_property {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (f_cont: continuous τ₁ τ₂ f) (f_surj: ∀y, ∃x, y = f x):
    ∀Z: Type, ∀τ₃: Topology Z, ∀k: Y → Z, open_map τ₁ τ₃ (k ∘ f) → open_map τ₂ τ₃ k := by
  intro Z τ₃ k open_map_kof U U_open
  have fiU_open: τ₁.is_open (U ∘ f) := f_cont U U_open; clear f_cont U_open
  have image_open := open_map_kof (U ∘ f) fiU_open
  refine τ₃.open_of_eq_open_set (fun y => ∃ x, y = (k ∘ f) x ∧ (U ∘ f) x) ?_ image_open
  intro z
  simp
  constructor
  intro ⟨x, hx, Ufx⟩
  exists f x
  intro ⟨y, hy, Uy⟩
  exists (f_surj y).choose
  rw [← (f_surj y).choose_spec]
  exact ⟨hy, Uy⟩

def rel_open_map (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀U: X → Prop, τ₁.is_open U → (τ₂.image_subspace f).is_open (fun ⟨y, hy⟩ => U hy.choose)


theorem fst_open_map {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  open_map (product_topology τ₁ τ₂) τ₁ Prod.fst := by
  intro U U_open
  dsimp [product_topology] at *
  apply τ₁.open_of_eq_open_set (fun y => ∃x, U (y, x))
  · intro x
    constructor
    intro ⟨y, hy⟩
    exists (x,y)
    intro ⟨p, hp⟩
    exists p.snd
    rw [hp.left]
    exact hp.right
  apply τ₁.open_cover_subsets_imp_open'
  intro x ⟨y, Uxy⟩
  rcases U_open x y Uxy with ⟨Ux, Vy, h⟩; clear U_open
  exists Ux
  intro x' Ux_x'
  replace h := h x' Ux_x' y Vy.is_nbhd
  exists y



theorem subspace_hausdorff_hausdorff {X: Type} (τ: Topology X) (h: τ.hausdorff)
  (pred: X → Prop): (τ.subspace_topology pred).hausdorff := by
    intro ⟨x, pred_x⟩ ⟨y, pred_y⟩ condition
    apply Subtype.ext
    dsimp
    replace h := h x y
    apply h
    intro ⟨U, U_open, U_x⟩ ⟨V, V_open, V_y⟩
    dsimp
    replace condition := condition {
      in_nbhd := U ∘ Subtype.val,
      nbhd_open := by
        exists U
      is_nbhd := U_x
    } {
      in_nbhd := V ∘ Subtype.val,
      nbhd_open := by exists V
      is_nbhd := V_y
    }
    dsimp at condition
    rcases condition with ⟨⟨p, pred_p⟩, what, huh⟩
    exists p




theorem closed_subspace_compact_compact {X: Type} (τ: Topology X) (c: τ.Compact)
  (pred: X → Prop) (closed: τ.is_closed pred): (τ.subspace_topology pred).Compact := by
  intro Y τ₂ C C_open
  dsimp [product_topology] at *
  apply τ₂.open_of_eq_open_set (fun y => ∀x, ∀pred_x, C (⟨x, pred_x⟩,y))
  · intro y
    simp



def closed_map {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y): Prop :=
  ∀C: X → Prop, τ₁.is_closed C → τ₂.is_closed (fun y => ∃x, f x = y ∧ C x)

def image_closed_map_closed {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (closed: closed_map τ₁ τ₂ f): τ₂.is_closed (fun y => ∃x, f x = y) := by
    apply τ₂.open_of_eq_open_set (fun y => ¬ ∃x, f x = y ∧ (fun _ => True) x)
    intro y
    simp
    apply closed
    exact Topology.whole_set_closed τ₁
