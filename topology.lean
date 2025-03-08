
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

def discrete_topology (X: Type): Topology X :=
  Topology.mk (is_open :=
    fun _ => True
  ) (whole_set_open := by
    trivial
  ) (intersection_open := by
    intro _ _ _ _
    trivial
  ) (open_cover_subsets_imp_open := by
    intro _ _
    trivial
  )

-- Fridays 2:30-4 !!

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
  (whole_set_open := by
    trivial
  ) (intersection_open := by
    intro _ _ _ _
    trivial
  ) (open_cover_subsets_imp_open := by
    intro U _
    trivial
  )

def point_topology: Topology Unit := discrete_topology Unit

@[simp]
def Topology.is_closed {X: Type} (τ: Topology X) (U: X → Prop): Prop := τ.is_open fun x => ¬U x


-- A point x is in the interior of a set A when there exists an open neighborhood
-- Uₓ of x that is a subset of A.
def Topology.interior {X: Type} (τ: Topology X) (A: X → Prop): X → Prop := fun x =>
  ∃Uₓ: X → Prop, τ.is_open Uₓ ∧ Uₓ x ∧ (∀y: X, Uₓ y → A y)

theorem Topology.interior_is_open {X: Type} (τ: Topology X) (A: X → Prop):
τ.is_open (τ.interior A) := by
  apply τ.open_cover_subsets_imp_open
  intro x h
  rcases h with ⟨Uₓ, Uₓ_open, x_in_Uₓ, Uₓ_subset_A⟩
  exists Uₓ
  refine And.intro Uₓ_open ?_
  refine And.intro x_in_Uₓ ?_
  intro y y_in_Uₓ
  exists Uₓ

def Topology.interior_subset {X: Type} (τ: Topology X) (A: X → Prop): ∀x, τ.interior A x → A x := by
  intro x h
  refine h.choose_spec.right.right x h.choose_spec.right.left

theorem Topology.interior_emptt_set_eq_empty_set {X: Type} (τ: Topology X):
  τ.interior (fun _ => False) = (fun _ => False) := by
  funext x
  refine eq_false ?_
  intro h
  exact τ.interior_subset _ x h

theorem Topology.interior_whole_set_eq_whole_set {X: Type} (τ: Topology X):
  τ.interior (fun _ => True) = (fun _ => True) := by
  funext x
  refine eq_true ?_
  refine Exists.intro (fun _ => True) (And.intro ?_ (And.intro ?_ ?_))
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
  ∀x: X, ∀y: X, (∀U: X → Prop, τ.is_open U → U x →
                 ∀V: X → Prop, τ.is_open V → V y → ∃p: X, U p ∧ V p) → x = y


theorem empty_hausdorff: Topology.hausdorff empty_topology := Empty.rec

theorem discrete_hausdorff {X: Type}: Topology.hausdorff (discrete_topology X) := by
  intro x y property
  replace property := property (fun p => x = p) True.intro rfl
            (fun p => p = y) True.intro rfl
  exact Eq.trans property.choose_spec.left property.choose_spec.right

theorem hausdorff_indiscrete_imp_contractible:
  Topology.hausdorff (indiscrete_topology X) → ∀x: X, ∀y: X, x = y := by
  intro hausdorff x y
  apply hausdorff
  intro U _ x_in_U V V_open y_in_V
  exists x
  refine And.intro x_in_U ?_
  exact V_open y y_in_V x


def Topology.frechet {X: Type} (τ: Topology X) :=
  ∀x: X, τ.is_open (fun y => x ≠ y)

theorem discrete_frechet {X: Type}: Topology.frechet (discrete_topology X) := by
  intro _
  trivial

theorem indiscrete_frechet_imp_contractible {X: Type}:
  Topology.frechet (indiscrete_topology X) → ∀x y: X, x = y := by
  intro frechet x y
  apply Classical.byContradiction
  intro hne
  have := (frechet x) y hne x
  contradiction

theorem complement_singletons_open_imp_frechet {X: Type} (τ: Topology X):
  (∀x y: X, x ≠ y → ∃U: X → Prop, τ.is_open U ∧ U x ∧ ¬U y) → τ.frechet := by
    intro h x
    apply τ.open_cover_subsets_imp_open
    intro y ne
    have := (h y x ne.symm)
    exists this.choose
    constructor; exact this.choose_spec.left
    constructor; exact this.choose_spec.right.left
    intro y₁ contained
    intro heq
    cases heq
    apply this.choose_spec.right.right contained


theorem hausdorff_imp_frechet {X: Type} (τ: Topology X) (h: Topology.hausdorff τ):
  Topology.frechet τ := by
  intro x
  apply τ.open_cover_subsets_imp_open
  -- Given two unequal points x and y, we need to find an open set that contains
  -- y but does not contain x
  intro y hneq
  -- We start by showing that there must exist two disjoint open sets containing
  -- x and y respectively
  replace h: ∃U, τ.is_open U ∧ U x ∧ ∃V, τ.is_open V ∧ V y ∧ ∀p, U p → ¬V p := by
    have h' := hneq ∘ h x y
    simp at h'
    exact h'
  -- unpack what it means for τ to be hausdorff
  match h with
  | ⟨_, _, x_in_U, V, V_open, y_in_V, U_V_disjoint⟩ =>
  clear h hneq

  -- We claim that the open set containing y satisfies the goal
  exists V
  constructor; exact V_open
  constructor; exact y_in_V
  -- lastly we need to prove that for any z, if z is in V,
  -- then z cannot be equal to x
  intro _ h₂ hneq₂
  -- BWOC, assume z is in V and x = z, and then substitute x=z everywhere
  cases hneq₂
  -- This is a contradiction because of the disjointedness condition says that
  -- x being in both V an dU is a contradiction
  exact U_V_disjoint x x_in_U h₂


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
  unfold Topology.closure
  apply τ.open_cover_subsets_imp_open
  intro x cond
  simp at cond
  exists fun x => ¬cond.choose x
  constructor; exact cond.choose_spec.left
  constructor; exact cond.choose_spec.right.right
  intro y h h₂
  apply h
  apply h₂
  exact cond.choose_spec.left
  intro u u_in_U
  exact cond.choose_spec.right.left u u_in_U

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



def exam_problem_1 {X: Type} (τ: Topology X): Topology (X ⊕ Unit) := Topology.mk
  (is_open :=
    fun (U: X ⊕ Unit → Prop) => (
      (U (Sum.inr ())) ∧ ∃UX, (τ.is_open UX ∧ ∀x, U (Sum.inl x) ↔ UX x)
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
    intro U_non_empty
    have := τ.open_cover_subsets_imp_open
    constructor
    sorry; sorry
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
    intro x h
    cases h; case intro h_int h_bound =>
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

def product_topology {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y): Topology (X × Y) :=
  Topology.from_basis_sets (
    fun B => ∃U: X → Prop, τ₁.is_open U ∧
      ∃V: Y→ Prop, τ₂.is_open V ∧
        ∀x, ∀y, B ⟨x, y⟩ ↔ (U x ∧ V y)
  ) (by
    intro p
    exists fun _ => True
    simp
    exists fun _ => True
    refine And.intro (τ₁.whole_set_open) ?_
    exists fun _ => True
    refine And.intro (τ₂.whole_set_open) ?_
    intro x y
    simp
  ) (by
    simp
    intro B₁ B₁_X B₁_X_open B₁_Y B₁_Y_open B₁_cond
    intro B₂ B₂_X B₂_X_open B₂_Y B₂_Y_open B₂_cond
    intro x y xy_in_B₁ xy_in_B₂
    let B_int := fun pair => B₁ pair ∧ B₂ pair
    let B_X_int := fun x => B₁_X x ∧ B₂_X x
    let B_Y_int := fun y => B₁_Y y ∧ B₂_Y y

    exists B_int
    simp [*]
    constructor

    exists B_X_int
    constructor
    exact τ₁.intersection_open _ B₁_X_open _ B₂_X_open
    exists B_Y_int
    constructor
    exact τ₂.intersection_open _ B₁_Y_open _ B₂_Y_open
    · intro px py
      constructor
      intro h
      constructor; constructor
      exact ((B₁_cond px py).mp (h.left)).left
      exact ((B₂_cond px py).mp (h.right)).left
      constructor
      exact ((B₁_cond px py).mp (h.left)).right
      exact ((B₂_cond px py).mp (h.right)).right
      intro h
      constructor
      apply (B₁_cond px py).mpr
      constructor
      exact h.left.left
      exact h.right.left
      apply (B₂_cond px py).mpr
      constructor
      exact h.left.right
      exact h.right.right
    · constructor
      constructor
      assumption
      assumption
      intro a b B₁_a B₂_a B₁_b B₂_b
      constructor
      exact ⟨B₁_a, B₂_a⟩
      exact ⟨B₁_b, B₂_b⟩
  )


theorem fst_continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  continuous (product_topology τ₁ τ₂) τ₁ Prod.fst := by
    intro U U_open
    simp [product_topology, Topology.from_basis_sets]
    intro a b a_in_U
    sorry

theorem snd_continuous {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y):
  continuous (product_topology τ₁ τ₂) τ₂ Prod.snd := by sorry
-- n
