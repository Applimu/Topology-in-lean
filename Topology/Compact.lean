import Topology.Basic
import Topology.Product
import Topology.Closures


theorem exists_maximal_over (X: Type) (r: X → X → Prop)
(r_refl: ∀x, r x x)
(r_wf: ∀U: Set X, Set.nonempty U → ∃m ∈ U, ∀x, r m x → x = m) (y: X): ∃m: X, r y m ∧ ∀x, r m x → x = m := by
  exact r_wf (Set.mk fun u => r y u) ⟨y, r_refl y⟩




namespace Topology
/--
  We define compactness to be close to the tube lemma because proving finiteness sucks
-/
def Compact {X: Type} (τ: Topology X): Prop := ∀Y, ∀τ₂: Topology Y,
  ∀C: Set (X × Y), (product_topology τ τ₂).is_open C → τ₂.is_open (Set.snd_tube C)

def point_compact (τ: Topology Unit): τ.Compact := by
  intro Y τ₂ C pC_closed
  apply τ₂.open_of_open_cover_subsets'
  intro x empty
  replace empty : ((), x) ∈ C := empty ()
  obtain ⟨singleton, V, c⟩ := pC_closed () x empty
  replace c := c () singleton.is_nbhd
  exists V
  intro y Vy a
  obtain rfl := Unit.ext a ()
  exact c y Vy

/--
  A space is compact if there is a continuous surjection to the space from a compact space
-/
theorem compact_of_cont_surj_compact {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (f: X → Y)
  (f_cont: continuous τ₁ τ₂ f) (f_surj: Surjective f) (cpct: τ₁.Compact): τ₂.Compact := by
  dsimp [Topology.Compact, product_topology] at *
  intro Z τZ C C_closed
  -- we'll use the fact that the image of the projection of this set is closed
  replace cpct := cpct Z τZ (Set.mk fun (x,y) => (f x, y) ∈ C)
  simp_all
  have : C.snd_tube = (Set.mk fun x: X × Z => (f x.fst, x.snd) ∈ C).snd_tube := by
    ext x
    simp
    constructor
    intro h x'
    exact h (f x')
    intro h y
    obtain ⟨x', heq⟩ := f_surj.exists_ap_eq y
    subst heq
    exact h x'
  rw [this]
  apply cpct
  clear cpct f_surj
  intro x y nCfxy
  rcases C_closed (f x) y nCfxy with ⟨U, V, yea⟩
  clear C_closed
  exists {
    toSet := Set.preimage f U.nbhd
    nbhd_open := by
      apply f_cont.open_imp_preimage_open -- Preimage of U is open by continuity!
      exact U.nbhd_open
    is_nbhd := U.is_nbhd
  }
  exists V
  intro x' f_invUx' z' Vz'
  dsimp at f_invUx'
  exact yea (f x') f_invUx' z' Vz'

theorem tube_lemma {X Y: Type} (τ₁: Topology X) (τ₂: Topology Y) (Y_cpct: τ₂.Compact)
  (U: Set (Y × X)) (U_open: (product_topology τ₂ τ₁).is_open U) (x₀: X) (h: x₀ ∈ U.snd_tube):
    ∃W: τ₁.open_nbhd x₀, W.nbhd ⊆ U.snd_tube := by
    exists {
      toSet := Set.snd_tube U,
      nbhd_open := Y_cpct X τ₁ U U_open,
      is_nbhd := h
    }
    intro x x_in_W y
    exact x_in_W y


theorem closed_subspace_compact_compact {X: Type} (τ: Topology X) (cpct: τ.Compact)
  (U: Set X) (closed: τ.is_closed U): (τ.subspace_topology U).Compact := by
  intro Y τ₂ C C_open

  let C': Set (X × Y) := Set.mk fun (x,y) => ∀h: x ∈ U, (⟨x, h⟩,y) ∈ C
  have : C.snd_tube = C'.snd_tube := by
    ext y
    simp [C']
  rw [this]; clear this

  apply cpct Y τ₂ C'
  intro x y hxy
  by_cases x ∈ U
  case pos h =>
    replace hxy := hxy h
    replace C_open := C_open ⟨x, h⟩ y hxy
    rcases C_open with ⟨Cx, Cy, h_open⟩
    rcases Cx with ⟨Cx_, ⟨Cx, h₁, h₂⟩, h₃⟩
    subst h₂
    exists {
      toSet := Cx
      nbhd_open := h₁
      is_nbhd := h₃
    }
    exists Cy
    simp [C']
    intro x' hx' y' hy' hx'₂
    replace h_open := h_open ⟨x', hx'₂⟩ hx' y' hy'
    exact h_open
  case neg h =>
    exists {
      toSet := U.complement
      nbhd_open := closed
      is_nbhd := h
    }
    exists Topology.all_nbhd _ _
    simp [C']
    intro x' hx' y' hy' hx'_U
    exact False.elim (hx' hx'_U)








theorem infinite_discrete_set_not_cpct: ¬((discrete_topology Nat).Compact) := by
  simp [Topology.Compact, discrete_topology, product_topology]
  sorry
