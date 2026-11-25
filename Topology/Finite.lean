
import Topology.Sets
import Topology.Functions


structure Finite (A: Type u): Prop where
  /--
    A type is finite if every nonempty family of sets has some maximal element M
  -/
  max_exists: ∀S: Set (Set A), Set.nonempty S → ∃M ∈ S, ∀s ∈ S, M ⊆ s → s = M

/--
  A set is finite iff every set of sets has a maximal element under set inclusion
-/
theorem finite_iff_maximal_exists (A: Type u): Finite A ↔ ∀S: Set (Set A), Set.nonempty S → ∃M ∈ S, ∀s ∈ S, M ⊆ s → s = M := by
  constructor
  exact @Finite.max_exists A
  exact Finite.mk

/--
  A set is finite iff every set of sets has a minimal element under set inclusion
-/
theorem finite_iff_minimal_exists (A: Type u): Finite A ↔ ∀S: Set (Set A), Set.nonempty S → ∃M ∈ S, ∀s ∈ S, s ⊆ M → s = M := by
  constructor
  intro A_fin
  intro S ⟨s, hs⟩
  have ⟨max_complement, ⟨M, M_in_S, hM⟩, h₂⟩ := A_fin.max_exists (Set.image Set.complement S) ⟨Set.complement s, by simp [hs]⟩
  subst hM
  exists M
  simp_all only [Set.image_def, forall_exists_index, and_imp, Set.complement_subset_complement,
    forall_apply_eq_imp_iff₂, Set.complement_inj, true_and]
  exact h₂

  intro min
  constructor
  intro S ⟨s, hs⟩
  have ⟨min_complement, ⟨M, M_in_S, hM⟩, h₂⟩ := min (Set.image Set.complement S) ⟨Set.complement s, by simp [hs]⟩
  subst hM
  exists M
  refine ⟨M_in_S, ?_⟩
  simp only [Set.image_def, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Set.complement_inj, Set.complement_subset_complement] at h₂
  exact h₂

theorem Nat.not_finite: ¬Finite Nat := by
  intro ⟨h⟩
  replace h := h (Set.full_image (fun i: Nat => Set.mk fun j => j ≤ i)) ⟨{0}, by exists 0; ext i; simp⟩
  rcases h with ⟨M, ⟨I, hI⟩, h⟩
  subst hI
  simp_all [Set.subset_def]
  replace h := h (I + 1) (by omega)
  revert h
  simp [funext_iff]
  exists I + 1
  simp

/--
  A type is finite if there exists an injection from the type into a known finite type
-/
theorem finite_of_injective_finite {A B: Type u} (f: A → B) (f_inj: Injective f) (B_fin: Finite B): Finite A := by
  constructor
  -- We are only given a family of subsets of `A`
  intro S ⟨s, hs⟩
  -- We use a double-preimage to construct a family of sets on B, and then take that set's maximum `M`
  obtain ⟨M, h₁, h₂⟩ := B_fin.max_exists (Set.preimage (Set.preimage f) S)
    ⟨Set.image f s, by simp [Set.inj_imp_preimage_image f f_inj, hs]⟩-- #1
  simp at h₁ h₂
  change ∀n, _ at h₂

  -- We then say that the maximal element of `s` is the preimage of `M` under `f`
  exists Set.preimage f M                  -- #2
  refine ⟨h₁, ?_⟩

  -- Now we need to prove that this set is maximal among the sets in `s`
  intro V V_in_s preimage_sub
  apply Set.subset_antisymm _ _ _ preimage_sub
  intro v hv
  replace h₂ := h₂ (Set.image f V ∪ Set.complement (Set.full_image f))         -- #3
  simp [Set.inj_imp_preimage_image f f_inj] at h₂
  have M_sub: M ⊆ Set.image f V ∪ Set.complement (Set.full_image f):= by
    intro b b_in_M
    -- "either b is in the image of `V` or b is not in the image of f"
    apply Classical.or_iff_not_imp_right.mpr
    intro h
    simp_all
    rcases h with ⟨k, hk⟩
    subst hk
    exists k
    refine ⟨?_, rfl⟩
    apply preimage_sub
    exact b_in_M

  have : Set.preimage f (Set.complement (Set.full_image f)) = Set.empty := by
    simp [Set.ext_iff]
  simp [this, V_in_s] at h₂

  replace h₂ := h₂ M_sub

  subst h₂
  simp [Set.inj_imp_preimage_image f f_inj, hv]

/--
  A set is finite if there exists a surjection from a finite set
-/
theorem finite_of_surjective_finite {A B: Type u} (f: A → B) (f_surj: Surjective f) (A_fin: Finite A): Finite B := by
  constructor
  intro S ⟨s, hs⟩
  obtain ⟨M, h₁, h₂⟩ := A_fin.max_exists (Set.preimage (Set.image f) S)
    ⟨Set.preimage f s, by simp [Set.surj_imp_image_preimage f f_surj, hs]⟩
  simp at h₁ h₂
  exists Set.image f M
  refine ⟨h₁, ?_⟩
  intro V V_in_S image_subset
  apply Set.subset_antisymm _ _ ?_ image_subset

  intro v v_in_V
  replace h₂ := h₂ (Set.preimage f V)
  rw [Set.surj_imp_image_preimage f f_surj] at h₂
  have : M ⊆ Set.preimage f V := by
    intro b b_in_M
    simp
    exact image_subset ⟨b, b_in_M, rfl⟩
  replace h₂ := h₂ V_in_S this
  subst h₂
  simp [Set.surj_imp_image_preimage f f_surj, v_in_V]


theorem finite_imp_not_surjective (A: Type) (inst: Finite A) (f: A → Nat): ¬Surjective f := by
  intro h
  apply Nat.not_finite
  exact finite_of_surjective_finite f h inst

theorem finite_imp_fn_not_inj (A: Type) (inst: Finite A) (f: Nat → A): ¬Injective f := by
  intro h
  apply Nat.not_finite
  exact finite_of_injective_finite f h inst

theorem all_maximal {A: Type u} (S: Set (Set A)) (h: Set.all ∈ S): ∃M, M ∈ S ∧ ∀s ∈ S, M ⊆ s → s = M := by
    exists Set.all
    refine ⟨h, ?_⟩
    intro s' _ hs'
    simp_all [Set.ext_iff, Set.subset_def]

theorem subsingleton_finite [h: Subsingleton X]: Finite X := by
  constructor
  intro S ⟨s, hs⟩
  induction s using Set.subsingleton_set_ind
  · exact all_maximal S hs
  · by_cases h: Set.all ∈ S
    case pos =>
      exact all_maximal S h
    case neg =>
      exists Set.empty
      refine ⟨hs, ?_⟩
      intro s s_in_S _
      induction s using Set.subsingleton_set_ind
      · exact False.elim (h s_in_S)
      · rfl

theorem unit_finite: Finite Unit := subsingleton_finite

@[ext]
theorem set_empty_ext (s₁ s₂: Set Empty): s₁ = s₂ := by
  ext x
  nomatch x

theorem empty_finite : Finite Empty := subsingleton_finite

theorem set_bool (s: Set Bool): s = Set.empty ∨ s = {true} ∨ s = {false} ∨ s = Set.all := by
  by_cases h_true: true ∈ s <;> by_cases h_false: false ∈ s <;> simp_all [Set.ext_iff]

/--
  Helper proposition for proving `finite_iff_ssubset_wf_relation`
  An inductive set `S` is a set such that for any `a: A`, if every
  element `y` where `r y s` satisfies `y ∈ S`, then `a` is also in `S`
-/
structure Inductive {A: Type u} (r: A → A → Prop) (S: Set A) where
  induct: ∀s : A, (∀y, r y s → y ∈ S) → s ∈ S

theorem inductive_iff {A: Type} (r: A → A → Prop) (S: Set A): (Inductive r S) ↔ (∀s : A, (∀y, r y s → y ∈ S) → s ∈ S) where
  mp := Inductive.induct
  mpr := Inductive.mk

theorem inductive_wf_imp_eq_all {A: Type} (r: A → A → Prop) (wf: WellFounded r) (S: Set A): Inductive r S → S = Set.all := by
  intro h_ind

  have : ∀x, Acc r x → x ∈ S := by
    intro x hx
    apply WellFounded.recursion wf
    exact h_ind.induct

  ext x
  simp
  apply this
  exact wf.apply x

theorem finite_iff_ssubset_wf_relation (A: Type): Finite A ↔ @WellFounded (Set A) (· ⊂ ·) where
-- Proofs here are based on the proofs in the ncatlab article for well-founded relations
  mp A_finite := by
    let U := Set.mk (fun s: Set A => Acc (· ⊂ ·) s)
    suffices U = Set.all by
      simp [Set.ext_iff, U] at this
      exact WellFounded.intro this

    apply Classical.byContradiction
    intro h; simp [Set.ext_iff, ← Set.complement_def] at h
    obtain ⟨M, h₁, h₂⟩ := (finite_iff_minimal_exists A).mp A_finite U.complement h


    apply h₁
    constructor
    intro v ⟨v_sub, v_neq⟩
    change v ∈ U
    apply Classical.byContradiction
    intro hv
    replace h₂ := h₂ v hv v_sub
    exact False.elim (v_neq h₂)


  mpr := by
    intro wf
    rw [finite_iff_minimal_exists]
    intro F F_nonempty
    apply Classical.byContradiction
    intro h; simp [Classical.skolem, ← Set.ssubset_def] at h
    rcases h with ⟨shrink, h_shrink⟩
    obtain ⟨s, hsF⟩ := F_nonempty

    induction wf.apply s
    case intro s h ih =>
    obtain ⟨h₁, h₂⟩ := h_shrink s hsF
    exact ih (shrink s hsF) h₂ h₁

/--
  If you can prove that if you can construct something for any strict subset of a set, then it is true for that set,
  then the statement holds in a finite type.
-/
noncomputable def finite_set_induction {A: Type} {finite: Finite A} {motive: Set A → Type} (f: (s: Set A) → (∀y ⊂ s, motive y) → motive s) (s: Set A): motive s := by
  rw [finite_iff_ssubset_wf_relation] at finite
  exact WellFounded.fix finite f s

theorem finite_imp_option_finite {A: Type} (A_finite: Finite A): Finite (Option A) := by
  constructor
  intro S ⟨s, hs⟩
  obtain ⟨Maximal, ⟨s', s'_in_S, heq⟩, Maximal_is_maximal⟩ := A_finite.max_exists (Set.image (Set.preimage some) S) ⟨
      Set.preimage some s, by exists s
  ⟩
  subst heq
  by_cases s' ∪ {none} ∈ S
  case pos h =>
    exists s' ∪ {none}
    constructor
    assumption
    intro s s_in_S s'_sub_s
    apply Set.subset_antisymm _ _ _ s'_sub_s
    simp [Set.union_subset_iff] at s'_sub_s
    replace preimages_eq := Maximal_is_maximal (Set.preimage some s) (by exists s) (by
      apply Set.preimage_monotone
      exact s'_sub_s.left
    )
    simp [Set.ext_iff] at preimages_eq
    intro x hx
    cases x
    case some x =>
      left
      exact (preimages_eq x).mp hx
    case none =>
      right
      rfl
  case neg h =>
    have none_not_mem: ¬ none ∈ s' := by
      intro h'
      have : s' ∪ {none} = s' := by simp [h']
      rw [← this] at s'_in_S
      exact absurd s'_in_S h
    have : s' ⊆ Set.full_image some := by
      intro x hx
      cases x
      case none => exact False.elim (none_not_mem hx)
      case some x => exists x

    exists s'
    constructor
    assumption
    intro s s_in_S s'_sub_s
    apply Set.subset_antisymm _ _ _ s'_sub_s
    replace preimage_eq := Maximal_is_maximal (Set.preimage some s) (by exists s) (by
      apply Set.preimage_monotone
      assumption
    )
    simp [Set.ext_iff] at preimage_eq
    intro x hx
    cases x
    case some x =>
      exact (preimage_eq x).mp hx
    case none =>
      have : s = s' ∪ {none} := by
        ext x
        cases x <;> simp
        case h.none => assumption
        case h.some x => exact preimage_eq x
      subst this
      exact absurd s_in_S h

theorem finite_of_bijective_finite {A B: Type}  (f: A → B) (f_bij: Bijective f) (A_finite: Finite A): Finite B := by
    exact finite_of_surjective_finite f f_bij.toSurjective A_finite

theorem bool_finite : Finite Bool := by
  apply finite_of_bijective_finite (fun
    | some (Unit.unit) => true
    | none => false
  )
  case f_bij =>
    apply Bijective.of_inj_and_surj
    apply Injective.intro
    intro a₁ a₂
    split <;> split <;> trivial
    apply Surjective.intro
    intro b
    cases b
    case true => exists some ()
    case false => exists none
  apply finite_imp_option_finite
  exact unit_finite



/--
  Example bijection for the inductive case when
  proving `finite_fin: Finite (Fin n)`
-/
def Fin.castOption {n: Nat} : Fin (n + 1) → Option (Fin n) := Fin.lastCases none some

theorem Fin.castOption_bij {n: Nat} : Bijective (@Fin.castOption n) where
  exists_ap_eq
    | none => by
      exists Fin.last n
      simp [Fin.castOption]
    | some y => by
      exists y.castSucc
      simp [Fin.castOption]
  eq_of_ap_eq := by
    intro x y heq
    induction x using Fin.reverseInduction
    <;> induction y using Fin.reverseInduction
    <;> simp_all [Fin.castOption]

/--
  The `Fin n` types are all finite
-/
theorem finite_fin (n: Nat): Finite (Fin n):= by
  induction n
  case zero =>
    constructor
    intro S ⟨s, hs⟩
    exists Set.all
    have : s = Set.all := by
      ext x; nomatch x
    subst this
    refine And.intro hs ?_
    intro s s_in_S all_sub
    exact Set.all_subset s all_sub
  case succ n' ih =>
    apply finite_of_injective_finite Fin.castOption Fin.castOption_bij.toInjective
    exact finite_imp_option_finite ih

/--
  The equivalent formulation of finiteness for `Set`s
-/
structure finite {X: Type u} (S: Set X): Prop where
  max_exists: ∀F, Set.nonempty F → ∃M ∈ F, ∀s ∈ F, M ∩ S ⊆ s → M ∩ S = s ∩ S

theorem finite_set_iff_minimal_exists {X: Type u} {S: Set X} : finite S ↔ ∀F, Set.nonempty F → ∃M ∈ F, ∀s ∈ F, s ∩ S ⊆ M → M ∩ S = s ∩ S where
  mp S_finite F F_nonempty := by
    obtain ⟨M, ⟨M', hM', heq⟩, M_maximal⟩ := S_finite.max_exists (Set.image Set.complement F) (by
      obtain ⟨s, hs⟩ := F_nonempty
      exists s.complement, s
    )
    subst heq
    exists M'
    constructor
    exact hM'
    intro s hs s_sub
    have : M'.complement ∩ S ⊆ s.complement := by
      intro x ⟨hxM', hxS⟩ hxs
      exact hxM' (s_sub ⟨hxs, hxS⟩)
    replace M_maximal := M_maximal s.complement (by exists s) this
    open Classical in
    simp_all [Set.ext_iff, Decidable.not_iff_not]
  mpr min := by
    apply finite.mk
    intro F F_nonempty
    obtain ⟨M, ⟨M', hM', heq⟩, M_minimal⟩ := min (Set.image Set.complement F) (by
      obtain ⟨s, hs⟩ := F_nonempty
      exists s.complement, s
    )
    subst heq
    exists M'
    constructor
    exact hM'
    intro s hs s_sub
    have : s.complement ∩ S ⊆ M'.complement := by
      intro x ⟨hxs, hxS⟩ hxM'
      exact hxs (s_sub ⟨hxM', hxS⟩)
    replace M_maximal := M_minimal s.complement (by exists s) this
    open Classical in
    simp_all [Set.ext_iff, Decidable.not_iff_not]


inductive finite' {X: Type u} : Set X → Prop where
  | intro (s: Set X) (h: ∀s', s' ⊂ s → finite' s'): finite' s

theorem finite'_induction {X: Type u} {motive: Set X → Prop} (s: Set X) (s_finite: finite' s)
  (h: ∀x ⊆ s, (∀y ⊂ x, motive y) → motive x): motive s := by
  induction s_finite
  case intro s' hs' ih =>
  apply h s' (Set.subset_refl _)
  intro y y_ssub
  apply ih y y_ssub

  intro c hc
  have : c ⊂ s' := by
    calc
      c ⊆ y := by assumption
      y ⊂ s' := by assumption
  apply h c this.left

-- noncomputable def finite'_fix {X: Type u} {C: Set X → Sort v} (s: Set X) (s_finite: finite' s)
--   (F: ∀s' ⊆ s, (∀y ⊂ s', C y) → C s'): C s :=
--   -- finite'.rec (fun s h h_ih F =>
--   --     F s (Set.subset_refl _) fun y y_ssub =>
--   --         h_ih y y_ssub fun c hc =>
--   --             F c (Set.subset_trans _ _ _ hc y_ssub.left)
--   --   ) s_finite F


--   by
--   apply finite'_induction (motive := C)
--   case intro s' hs' ih =>
--   apply F s' (Set.subset_refl _)
--   intro y y_ssub
--   apply ih y y_ssub
--   intro c hc
--   exact F c (Set.subset_trans _ _ _ hc y_ssub.left)

theorem finite'_of_subset_finite' {X: Type u} {s₁ s₂: Set X} (s₂_finite: finite' s₂) (h_sub: s₁ ⊆ s₂): finite' s₁ := by
  induction s₂_finite
  case intro s₂ h ih =>
  by_cases s₁ = s₂
  case pos heq =>
    subst heq
    exact finite'.intro s₁ h
  case neg hneq =>
    exact h s₁ ⟨h_sub, hneq⟩

theorem empty_finite' {X: Type u}: @finite' X Set.empty := by
  apply finite'.intro
  intro s ⟨hs, hneq⟩
  obtain rfl := Set.subset_empty s hs
  contradiction


theorem finite'_imp_image_finite' {X Y: Type u} {f: X → Y} {s: Set X}: finite' s → finite' (Set.image f s) := by
  intro s_finite
  induction s_finite
  case intro s s_finite ih =>

  apply finite'.intro
  intro ys ⟨hys, ys_neq⟩

  have ssub : (Set.preimage f ys) ∩ s ⊂ s := by
    constructor
    · exact @Set.inter_subset_right X _ s
    · simp
      intro s_sub
      apply ys_neq
      apply Set.subset_antisymm
      exact hys
      simp [s_sub]

  have sub : ys ⊆ Set.image f (Set.preimage f ys ∩ s) := by
    intro y hy
    obtain ⟨x, hx, heq⟩ := hys hy
    subst heq
    exists x

  have h_finite := ih _ ssub
  apply finite'_of_subset_finite' h_finite sub

-- noncomputable def size {X: Type u} (s: Set X) (s_finite: finite' s): Nat :=
--   finite'_fix s s_finite fun s' s'_sub_s f =>
--     open Classical in
--     if h: s'.nonempty then
--       have ssub: s' ∩ Set.complement {h.choose} ⊂ s' := by
--         constructor
--         exact @Set.inter_subset_left X s' (Set.complement {h.choose})
--         simp
--         intro h_sub
--         apply @h_sub h.choose h.choose_spec rfl
--       Nat.succ (f (s' ∩ Set.complement {h.choose}) ssub )
--     else
--       0

-- theorem size_empty {X: Type u}: @size X Set.empty (empty_finite') = 0 := by
--   simp [size, f]
--   split


theorem inter_ssub_of_not_sub (A B: Set X): ¬B ⊆ A → A ∩ B ⊂ B := by
  intro h
  constructor
  · exact @Set.inter_subset_right X A B
  · simp [h]




theorem finite'_union_singleton_imp_finite' {X: Type u} (s: Set X) (s_finite: finite' s) (x: X): finite' (s ∪ {x}) := by
  by_cases x ∈ s
  case pos h =>
    have : s ∪ {x} = s := by simp [h]
    rw [this]
    exact s_finite
  case neg not_mem =>

  induction s_finite
  case intro s s_finite ih =>

  replace ih : ∀s', s' ⊂ s → finite' (s' ∪ {x}) := by
    intro s' hs'
    have : ¬ x ∈ s' := by
      intro hx
      exact not_mem (hs'.left hx)
    exact ih s' hs' this

  apply finite'.intro
  intro s' ⟨s'_sub, s'_neq⟩

  by_cases s' ⊆ s
  case pos h_sub =>
    replace s_finite := finite'.intro _ s_finite
    apply finite'_of_subset_finite' s_finite h_sub
  case neg h =>
    have hx : x ∈ s' := by
      apply Classical.byContradiction
      intro h_not
      apply h
      intro v hv
      cases s'_sub hv <;> simp_all

    have h_ssub : s' ∩ s ⊂ s := by
      refine inter_ssub_of_not_sub s' s ?_
      intro h_sub
      apply s'_neq
      refine Set.subset_antisymm s' (s ∪ {x}) s'_sub ?_
      refine @Set.union_subset X s {x} s' h_sub ?_
      simp [hx]

    have : (s' ∩ s) ∪ {x} = s' := by
      apply Set.subset_antisymm
      refine @Set.union_subset X (s' ∩ s) {x} s' ?_ ?_
      exact @Set.inter_subset_left X s' s
      exact @Iff.mpr ({x} ⊆ s') (x ∈ s') (Set.singleton_sub s' x) hx
      intro v hv
      simp [hv]
      rw [Eq.comm]
      exact s'_sub hv
    rw [← this]
    exact ih _ h_ssub

/- TODO: Move to `Sets.lean` -/
theorem Set.sub_imp_exists_pair {A B s: Set X} (h: s ⊆ A ∪ B): ∃s₁ ⊆ A, ∃s₂ ⊆ B, s = s₁ ∪ s₂ := by
  exists s ∩ A, ?_
  · exact inter_subset_right s A
  exists s ∩ B, ?_
  · exact inter_subset_right s B
  rw [← inter_union_left, inter_comm, Eq.comm, inter_eq_right_iff_subset]
  exact h



theorem singleton_finite' {X: Type u} (x: X): finite' {x} := by
  apply finite'.intro
  intro s ⟨s_sub, s_neq⟩
  obtain rfl : s = Set.empty := by
    simp [Set.ext_iff]
    intro x' hx'
    obtain rfl := s_sub hx'
    simp_all
  exact empty_finite'



theorem not_finite'_imp_exists_infinite_subset {s: Set X}: ¬finite' s → ∃s' ⊂ s, ¬ finite' s' := by
  intro inf
  apply Classical.byContradiction
  intro h
  simp at h
  exact inf (finite'.intro s h)

private theorem finite'_disjoint_union_finite {X: Type u} {A B: Set X} (A_finite: finite' A) (B_finite: finite' B) (hAB: A ∩ B = ∅) : finite' (A ∪ B) := by
  simp at hAB
  induction A_finite generalizing B
  case intro A hA ih' =>
  induction B_finite
  case intro B hB ih =>

  apply finite'.intro
  intro s' hs'
  obtain ⟨sA, hsA, sB, hsB, rfl⟩ := Set.sub_imp_exists_pair hs'.left
  replace hs' := hs'.right
  by_cases sA = A
  case pos heq =>
    subst heq
    obtain ⟨b, hb, hb'⟩ : ∃b ∈ B, ¬b ∈ sB := by
      apply Classical.byContradiction fun nh => ?_
      simp at nh
      apply hs'
      congr
      apply Set.subset_antisymm
      · exact hsB
      · exact nh
    apply ih sB
    · constructor
      assumption
      intro rfl
      contradiction
    -- · exact finite'.intro sA hA
    · calc
        sA ∩ sB = sA ∩ (B ∩ sB) := by
          congr
          rw [(Set.inter_eq_right_iff_subset _ _).mpr hsB]
        sA ∩ (B ∩ sB) = (sA ∩ B) ∩ sB := by rw [← Set.inter_assoc]
        (sA ∩ B) ∩ sB = Set.empty := by simp [hAB]
  case neg hneq =>
    have A_ssub: sA ⊂ A := ⟨hsA, hneq⟩
    apply ih' sA A_ssub
    · apply finite'_of_subset_finite' ⟨B, hB⟩ hsB
    refine Set.subset_empty (sA ∩ sB) ?_
    calc
      sA ∩ sB ⊆ sA ∩ B := by exact Set.subset_inter_left sB B sA hsB
      sA ∩ B ⊆ A ∩ B := by exact Set.subset_inter_right sA A B hsA
      A ∩ B = Set.empty := hAB


theorem finite'_union_finite' {X: Type u} {A B: Set X} (A_finite: finite' A) (B_finite: finite' B) : finite' (A ∪ B) := by
  generalize hB': B ∩ A.complement = B'
  have hu: A ∪ B = A ∪ B' := by
    subst hB'
    rw [Set.union_inter_left, Set.union_comm A A.complement, Set.complement_union_eq_all, Set.inter_all]
  have hd : A ∩ B' = Set.empty := by
    subst hB'
    rw [Set.inter_comm, ← Set.inter_assoc, Set.complement_inter_eq_empty, Set.inter_empty]
  have B'_sub: B' ⊆ B := by
    subst hB'
    exact Set.inter_subset_left B A.complement
  have B'_finite: finite' B' := by exact finite'_of_subset_finite' B_finite B'_sub

  rw [hu]
  apply finite'_disjoint_union_finite <;> try assumption










theorem Finite_iff_all_finite' {X: Type u}: Finite X ↔ ∀S: Set X, finite' S where
  mp X_finite := by
    rw [finite_iff_minimal_exists] at X_finite
    let finite_sets: Set (Set X) := Set.mk finite'

    apply Classical.byContradiction
    intro hneq
    simp only [Classical.not_forall] at hneq

    obtain ⟨M, hM, M_minimal⟩ := X_finite (finite_sets.complement) hneq
    apply hM
    apply finite'.intro
    intro s' ⟨s'_sub, s'_neq⟩
    apply Classical.byContradiction
    change ¬ s' ∈ finite_sets.complement
    intro h_inf
    obtain rfl := M_minimal s' h_inf s'_sub
    exact False.elim (s'_neq rfl)
  mpr all_finite' := by
    rw [finite_iff_minimal_exists]
    intro F F_nonempty
    apply Classical.byContradiction
    intro h
    simp [Classical.skolem] at h
    obtain ⟨shrink, h_shrink⟩ := h
    have shrink_ssub S (h: S ∈ F): shrink S h ⊂ S := (h_shrink S h).right
    have shrink_in_F S h := (h_shrink S h).left
    clear h_shrink

    obtain ⟨s, hsF⟩ := F_nonempty
    induction all_finite' s
    case intro s h ih =>
    exact ih (shrink s hsF) (shrink_ssub s hsF) (shrink_in_F s hsF)

theorem Finite_iff_finite'_all {X: Type u}: Finite X ↔ @finite' X Set.all := by
  have : @finite' X Set.all ↔ ∀S: Set X, finite' S := by
    constructor
    · intro all_finite' s
      apply finite'_of_subset_finite' all_finite' (Set.subset_all _)
    · intro all_finite
      exact all_finite Set.all
  apply Iff.trans ?_ this.symm
  exact Finite_iff_all_finite'


@[simp]
theorem iff_iff_iff {A B: Prop} : ((A ↔ B) ↔ B) ↔ A := by
  by_cases ha: A
  case pos => simp [ha]
  case neg =>
    obtain rfl : A = False := eq_false ha
    simp





-- theorem finite_iff_finite' {X: Type u} (S: Set X): finite S ↔ finite' S where
--   mp S_finite := by
--     rw [finite_set_iff_minimal_exists] at S_finite
--     let U := Set.mk fun s': Set X => finite' s' ∧ s' ⊆ S

--     suffices U = Set.power_set S by
--       simp [Set.ext_iff, U] at this
--       apply finite'.intro
--       intro s ⟨s_sub, s_neq⟩
--       exact this s s_sub



--     apply Classical.byContradiction
--     intro h
--     simp [Set.ext_iff, U] at h


--     obtain ⟨m, ⟨hm, m_sub⟩, m'_minimal⟩ := S_finite (U.complement ∩ Set.power_set S) (by
--       obtain ⟨s, hs₁, hs₂⟩ := h
--       exists s
--       constructor
--       exact fun ⟨s_fin, _⟩ => hs₂ s_fin
--       exact hs₁
--     )
--     apply hm
--     simp [U]
--     constructor
--     constructor
--     · intro v ⟨v_sub, v_neq⟩
--       suffices v ∈ U by exact this.left
--       apply Classical.byContradiction
--       intro h_nv
--       simp_all
--       have v_sub_S: v ⊆ S := Set.subset_trans _ _ _ v_sub m_sub
--       replace m'_minimal := m'_minimal v h_nv (by
--         exact Set.subset_trans _ _ _ v_sub m_sub
--       )
--       have : v ∩ S = v := by exact (Set.inter_eq_left_iff_subset v S).mpr v_sub_S
--       rw [this] at m'_minimal
--       replace : m ∩ S = m := by exact (Set.inter_eq_left_iff_subset m S).mpr m_sub
--       rw [this, Eq.comm] at m'_minimal
--       exact v_neq (m'_minimal v_sub)
--     · exact m_sub

--   mpr h := by
--     rw [finite_set_iff_minimal_exists]
--     intro F F_nonempty
--     apply Classical.byContradiction
--     intro h
--     simp [Classical.skolem] at h
--     obtain ⟨shrink, h_shrink⟩ := h
--     have shrink_in_F s h := (h_shrink s h).left
--     have shrink_ssub s h : shrink s h ∩ S ⊂ s ∩ S := by
--       have ⟨_, h₁, h₂⟩ := h_shrink s h
--       constructor
--       refine @Set.subset_inter X s S (shrink s h ∩ S) h₁ ?_
--       exact @Set.inter_subset_right X (shrink s h) S
--       exact fun a => h₂ (id (Eq.symm a))
--     clear h_shrink

--     obtain ⟨s, hsF⟩ := F_nonempty

--     have : s ∩ S ⊆ S := by exact @Set.inter_subset_right X s S
--     replace := finite'_of_subset_finite' h this
--     apply finite'_induction (motive := fun _ => False) _ this
--     intro k hk





--     revert F_nonempty
--     apply (Set.not_nonempty_iff_eq_empty F).mpr


--     let U := Set.mk fun u => ∀x ⊆ u, ¬u ∈ F

--     suffices Inductive (· ⊂ ·) U by
--       have clearly : U ∩ F = Set.empty := by
--         ext x
--         simp [U]
--         exact fun h => h x (Set.subset_refl x)
--       have : U ∩ F = F := by
--         refine (Set.inter_eq_right_iff_subset U F).mpr ?_
--         have : ∀s, finite' s → s ∈ U := by



--         intro s hs s' s'_sub_s hs'

--         sorry
--       rw [this] at clearly
--       exact clearly

--     constructor
--     intro z hz
--     have z_minimal : ∀y, y ∩ S ⊂ z → ¬ y ∈ F := by
--       intro y hy
--       have y_ssub: y ⊂ z := by
--         constructor


--       apply hz y y_ssub y (Set.subset_refl y)
--     have : ¬ z ∈ F := by
--       intro z_in_F
--       have ⟨h₁, h₂, h₃⟩ := h_shrink z z_in_F
--       have h₄: shrink z z_in_F ∩ S ⊂ z := by
--         constructor
--         exact h₂
--         intro heq
--         rw (occs := [1]) [← heq] at h₃
--         simp [Set.inter_self_right] at h₃
--       apply z_minimal (shrink z z_in_F) h₄ h₁

--     exact fun _ _ => this











theorem Set.empty_finite {X: Type u}: @finite X Set.empty := by
  apply finite.mk
  intro F F_nonempty
  simp
  exact F_nonempty

theorem Set.singleton_finite {X: Type u} (x: X): finite {x} := by
  apply finite.mk
  intro F F_nonempty
  by_cases ∃M ∈ F, x ∈ M
  case pos h =>
    obtain ⟨M, mF, xM⟩ := h
    exists M
    constructor
    assumption
    intro s hs x_singleton_sub
    have : M ∩ {x} = {x} := by
      refine (inter_eq_right_iff_subset M {x}).mpr ?_
      simp [xM]
    rw [this] at ⊢ x_singleton_sub
    apply Eq.symm
    exact (inter_eq_right_iff_subset s {x}).mpr x_singleton_sub
  case neg h =>
    obtain ⟨s, hs⟩ := F_nonempty
    exists s
    constructor
    assumption
    intro s' hs' sx_sub_s'
    have hxs: ¬x ∈ s := fun hx => h ⟨s, hs, hx⟩
    have hxs': ¬x ∈ s' := fun hx => h ⟨s', hs', hx⟩
    simp
    exact (iff_false_right hxs').mpr hxs

theorem finite_union_finite {S₁ S₂: Set X} (finite₁: finite S₁) (finite₂: finite S₂): finite (S₁ ∪ S₂) := by
  apply finite.mk
  intro F F_nonempty
  obtain ⟨m₁, hm₁, m₁_maximal₁⟩ := finite₁.max_exists F F_nonempty
  let F' := Set.mk fun m => m ∈ F ∧  ∀s, s ∈ F → m ∩ S₁ ⊆ s → m ∩ S₁ = s ∩ S₁
  obtain ⟨M, ⟨hM, M_maximal₁⟩, M_maximal₂⟩ := finite₂.max_exists F' ⟨m₁, hm₁, m₁_maximal₁⟩
  clear hm₁ m₁_maximal₁ m₁
  exists M
  constructor
  exact hM
  simp [Set.inter_union_left, Set.union_subset_iff]
  intro s hs hMs₁ hMs₂
  replace M_maximal₂ := M_maximal₂ s ⟨hs, ?_⟩ hMs₂
  replace M_maximal₁ := M_maximal₁ s hs hMs₁
  rw [M_maximal₁, M_maximal₂]

  intro m' hm' s_sub_m'
  have hMm': M ∩ S₁ = m' ∩ S₁ := by
    apply M_maximal₁ m' hm'
    calc
      M ∩ S₁ = s ∩ S₁ := M_maximal₁ s hs hMs₁
      s ∩ S₁ ⊆ m' := s_sub_m'
  have hMs: M ∩ S₁ = s ∩ S₁ := M_maximal₁ s hs hMs₁
  rw [← hMm', ← hMs]

theorem finite_of_subset_finite {S₁ S₂: Set X} (sub: S₁ ⊆ S₂) (finite₂: finite S₂): finite S₁ := by
  have inter_Ss: ∀s, (s ∩ S₁) ∩ S₂ = s ∩ S₁ := by
    intro s
    ext x
    simp
    intro hs
    exact @sub x

  apply finite.mk
  intro F F_nonempty
  obtain ⟨M, ⟨M', hM', heq⟩, M_maximal⟩ := finite₂.max_exists (Set.image (fun s => s ∩ S₁) F) (by
    exact (Set.nonempty_image_iff_nonempty (fun s => s ∩ S₁) F).mpr F_nonempty
  )
  dsimp at heq
  subst heq
  simp [inter_Ss] at *
  exists M', hM'
  intro s hs h_sub
  apply M_maximal s hs
  refine @Set.subset_inter X s S₁ (M' ∩ S₁) h_sub ?_
  exact @Set.inter_subset_right X M' S₁


-- theorem finite_imp_subtype_finite {X: Type u} {S: Set X} (S_finite: finite S): Finite (S.subtype) := by
--   rw [finite_iff_maximal_exists]
--   intro F ⟨s, hs⟩
--   have this : @Surjective (Set (Set X)) (Set (Set S.subtype)) (Set.preimage $ Set.image Subtype.val) := by
--     refine (Set.preimage_surj_iff_inj (Set.image Subtype.val)).mpr ?_
--     refine (Set.image_inj_iff_inj Subtype.val).mpr ?_
--     exact Subtype.val_inj
--   induction F using this.ind
--   case k F =>
--   clear this
--   simp_all [Set.image_preimage_eq_inter_full_image, Set.preimage_sub_preimage_iff, Set.preimage_eq_preimage_iff]
--   rw [subtype_full_image_val]
--   obtain ⟨M, hM, heq⟩ := S_finite.max_exists (Set.image (· ∩ S) F) (by
--     exists Set.image Subtype.val s, Set.image Subtype.val s
--     simp [hs]
--     intro ⟨x, hx⟩ hsx
--     exact hx
--   )
--   obtain ⟨M, hM, rfl⟩ := hM


--   exists M ∩ S
--   simp_all


theorem bounded_inj_imp_finite {A: Type} {f: A → Nat} (f_inj: Injective f) (bounded: ∃bound, ∀x, f x ≤ bound): Finite A := by
  rcases bounded with ⟨bound, bounded⟩
  apply finite_of_injective_finite (fun x => (⟨f x, ?_⟩: Fin (bound + 1)))
  apply Injective.intro
  simp
  exact f_inj.eq_of_ap_eq
  exact finite_fin (bound + 1)
  exact Nat.lt_succ_of_le (bounded x)


def Nat.fin_set (n: Nat): Set Nat := Set.mk fun i => i < n

@[simp]
theorem Nat.fin_set_def (n x: Nat): x ∈ n.fin_set ↔ x < n := Iff.rfl

@[simp]
theorem Nat.fin_set_zero : Nat.fin_set 0 = Set.empty := by simp [Set.ext_iff]

@[simp]
theorem Nat.fin_set_one : Nat.fin_set 1 = {0} := by simp [Set.ext_iff]

theorem Nat.fin_set_succ_eq (n: Nat): Nat.fin_set (n + 1) = Nat.fin_set n ∪ {n} := by
  simp [Set.ext_iff]
  omega


theorem fin_set_finite' (n: Nat): finite' (Nat.fin_set n) := by
  induction n
  case zero =>
    simp
    exact empty_finite'
  case succ n' ih =>
    rw [Nat.fin_set_succ_eq]
    apply finite'_union_finite'
    · exact ih
    · exact singleton_finite' n'

theorem Nat.fin_set_finite (bound: Nat): finite (Nat.fin_set bound) := by
  induction bound
  · simp
    exact Set.empty_finite
  case succ n ih =>
    simp [Nat.fin_set_succ_eq]
    refine finite_union_finite ih ?_
    exact Set.singleton_finite n


theorem bounded_set_imp_finite (S: Set Nat) (bounded: ∃bound, ∀x ∈ S, x ≤ bound): finite S := by
  obtain ⟨bound, h_bound⟩ := bounded
  apply finite_of_subset_finite (S₂ := Nat.fin_set (bound + 1))
  · intro x hx
    simp
    specialize h_bound x hx
    exact Nat.lt_succ_of_le h_bound
  · exact Nat.fin_set_finite (bound + 1)




theorem finite_imp_bounded {A: Type} (A_finite: Finite A) (f: A → Nat): ∃bound, ∀a: A, f a < bound := by

    let nats: Set (Set Nat) := Set.full_image fun (n: Nat) => Set.mk fun i => i < n
    obtain ⟨M, ⟨M', hM', heq⟩, maximal⟩ := A_finite.max_exists (Set.image (Set.preimage f) nats) ⟨Set.empty, by
      exists Set.empty
      constructor
      exists 0
      simp [Set.ext_iff]
      exact rfl
    ⟩

    subst heq
    simp [nats] at hM'
    obtain ⟨bound, h_bound⟩ := hM'
    subst h_bound
    exists bound
    intro a


    simp at maximal
    apply Classical.byContradiction
    intro h
    replace maximal := maximal (Set.mk fun i => i < f a + 1) (by exists f a + 1) (by
      intro x hx
      simp at hx ⊢
      omega
    )
    simp [Set.ext_iff] at maximal
    replace maximal := maximal a
    simp_all
    omega

theorem transgen_eq_succ_eq_lt : Relation.TransGen (fun (n m: Nat) => n.succ = m) = (· < ·) := by
  ext n m
  constructor
  · intro h
    induction h
    case h.h.a.mp.single m' heq =>
      subst heq
      exact Nat.lt_add_one n
    case h.h.a.mp.tail m' m_ hm heq ih =>
      subst heq
      exact Nat.lt_succ_of_lt ih
  · intro hlt
    induction hlt
    case h.h.a.mpr.refl =>
      exact Relation.TransGen.single rfl
    case h.h.a.mpr.step m' hle ih =>
      apply Relation.TransGen.tail (b := m') <;> trivial


-- /--
--   For any function into a well-ordered set, there exists a covering of that set
-- -/
-- theorem finite_imp_covering_WF {A B: Type} (A_finite: Finite A) (r: B → B → Prop) (r_wf: WellFounded r) (r_trans: ∀a b c, r a b → r b c → r a c)
--   (f: A → B): ∃covering: Set B, finite covering ∧ ∀a: A, ∃bound ∈ covering, r (f a) bound := by
--   -- accs is the set of all sets of the form
--   by_cases Nonempty B
--   case neg h_empty =>
--     exists Set.empty
--     constructor
--     sorry
--     sorry
--   case pos nonempty =>


--   let accs := Set.full_image fun (b: B) => Set.mk fun i => r i b

--   -- We need to prove that this is nonempty
--   have empty_in_accs : Set.empty ∈ Set.image (Set.preimage f) accs := by
--     exists Set.empty
--     simp [accs, Set.ext_iff]
--     apply Classical.byContradiction
--     intro h
--     simp [Classical.skolem] at h
--     obtain ⟨descend, h_chain⟩ := h
--     rcases nonempty with ⟨b⟩
--     have acc := Acc.transGen $ r_wf.apply b
--     induction acc using @Acc.rec
--     case h.intro b' hb ih =>
--     apply ih (descend b') (h_chain b')

--   obtain ⟨M, ⟨M', hM', heq⟩, maximal⟩ := A_finite.max_exists (Set.image (Set.preimage f) accs) ⟨Set.empty, empty_in_accs⟩
--   subst heq
--   simp [accs] at hM'
--   obtain ⟨bound, h_bound⟩ := hM'
--   subst h_bound
--   exists bound
--   intro a
--   simp at maximal
--   change ∀s, _ at maximal

--   by_cases ∃a', Relation.TransGen r (f a) (f a')
--   case pos hxist =>
--     obtain ⟨a', ha'⟩ := hxist
--     apply Classical.byContradiction
--     intro h
--     replace maximal := maximal (Set.mk fun i => Relation.TransGen r i (f a')) (by exists f a') (by
--       intro x hx
--       simp at ⊢ hx
--       have p₁: ¬ Relation.TransGen r (f a') bound := by
--         intro bad
--         exact h (Relation.TransGen.trans ha' bad)
--       have p₂: ¬ Relation.TransGen r (f a') (f x) := by
--         intro bad
--         exact p₁ (Relation.TransGen.trans bad hx)
--       -- We need totality here to solve this
--       sorry
--     )
--     simp at maximal

--   case neg h =>
--     simp at h

--     replace maximal := maximal (Set.mk fun b => Relation.TransGen r (f a) b) (by sorry)
--     simp [Set.subset_def, h] at maximal


/-
theorem finite_imp_bounded_WF {A B: Type} [nonempty: Nonempty B] (A_finite: Finite A) (r: B → B → Prop) (B_wf: WellFounded r)
  (f: A → B): ∃bound, ∀a: A, Relation.TransGen r (f a) bound := by

  -- We need to prove that this is nonempty
  have empty_in_accs : Set.empty ∈ Set.image (Set.preimage f) accs := by
    exists Set.empty
    simp [accs, Set.ext_iff]
    apply Classical.byContradiction
    intro h
    simp [Classical.skolem] at h
    obtain ⟨descend, h_chain⟩ := h
    rcases nonempty with ⟨b⟩
    have acc := Acc.transGen $ B_wf.apply b
    induction acc using @Acc.rec
    case h.intro b' hb ih =>
    apply ih (descend b') (h_chain b')

  obtain ⟨M, ⟨M', hM', heq⟩, maximal⟩ := A_finite.max_exists (Set.image (Set.preimage f) accs) ⟨Set.empty, empty_in_accs⟩
  subst heq
  simp [accs] at hM'
  obtain ⟨bound, h_bound⟩ := hM'
  subst h_bound
  exists bound
  intro a
  simp at maximal
  change ∀s, _ at maximal

  by_cases ∃a', Relation.TransGen r (f a) (f a')
  case pos hxist =>
    obtain ⟨a', ha'⟩ := hxist
    apply Classical.byContradiction
    intro h
    replace maximal := maximal (Set.mk fun i => Relation.TransGen r i (f a')) (by exists f a') (by
      intro x hx
      simp at ⊢ hx
      have p₁: ¬ Relation.TransGen r (f a') bound := by
        intro bad
        exact h (Relation.TransGen.trans ha' bad)
      have p₂: ¬ Relation.TransGen r (f a') (f x) := by
        intro bad
        exact p₁ (Relation.TransGen.trans bad hx)
      -- We need totality here to solve this
      sorry
    )
    simp at maximal

  case neg h =>
    simp at h

    replace maximal := maximal (Set.mk fun b => Relation.TransGen r (f a) b) (by sorry)
    simp [Set.subset_def, h] at maximal
-/

theorem exists_injection_with_hole_at_zero {A: Type} {n: Nat} (f: A → Fin (n + 1))
  (f_inj: Injective f) (not_surj: ¬Surjective f):
  ∃f': A → Fin (n + 1), Injective f' ∧ ∀a, f' a ≠ 0 := by
    rw [Surjective.not_surj_iff_exists_hole] at not_surj
    obtain ⟨hole, hole_hole⟩ := not_surj
    exists fun a => Fin.cases hole Fin.succ (f a)
    constructor
    · apply Injective.intro _
      intro a₁ a₂ heq
      apply f_inj.eq_of_ap_eq
      simp at heq
      generalize h₁: f a₁ = fa₁, h₂: f a₂ = fa₂ at *
      induction fa₁ using Fin.cases <;> induction fa₂ using Fin.cases <;> simp_all
    · intro a
      simp
      intro k
      apply hole_hole a
      generalize h: f a = fa at *
      induction fa using Fin.cases <;> simp_all
      case right.succ fa' =>
        exfalso
        exact Fin.succ_ne_zero _ k

theorem exists_injection_fin_succ_imp_exists_injection_fin_or_surjective {A: Type} {n: Nat} (f: A → Fin (n + 1))
  (f_inj: Injective f): (∃f': A → Fin n, Injective f') ∨ Surjective f := by
    apply Classical.or_iff_not_imp_right.mpr
    intro not_surj
    obtain ⟨f', h₁, h₂⟩ := exists_injection_with_hole_at_zero f f_inj not_surj
    exists fun a => (f' a).pred (h₂ a)
    apply Injective.intro ?_
    intro a₁ a₂ heq
    rw [Fin.pred_inj] at heq
    exact h₁.eq_of_ap_eq _ _ heq


theorem Nat.min_lt_max_of_ne {a b: Nat} (hneq: a ≠ b): min a b < max a b := by
  omega

theorem exists_surjection_fin_succ_imp_exists_surjection_fin_or_injective {A: Type} {n: Nat} (f: Fin (n + 1) → A)
  (f_surj: Surjective f): (∃f': Fin n → A, Surjective f') ∨ Injective f := by
    apply Classical.or_iff_not_imp_right.mpr
    intro not_inj
    replace not_inj := fun a => not_inj (Injective.intro a)
    simp at not_inj
    rcases not_inj with ⟨x₁, x₂, h_equiv, hneq⟩
    exists fun i => f $ if i.val < max x₁.val x₂.val then i.castSucc else i.succ
    apply Surjective.intro
    intro a
    by_cases a = f x₁
    case pos h =>
      subst h
      have : min x₁.val x₂.val < n := by
        omega

      exists ⟨min x₁.val x₂.val, ?_⟩
      have : min x₁.val x₂.val < max x₁.val x₂.val := Nat.min_lt_max_of_ne ?_
      simp [this]
      by_cases hcmp: x₁.val ≤ x₂.val <;> simp [Nat.min_def, hcmp]
      exact Eq.symm h_equiv
      exact Fin.val_ne_of_ne hneq
    case neg h =>
      obtain ⟨⟨i, hlt⟩, hi⟩ := f_surj.exists_ap_eq a
      subst hi
      if hlt₂: i < max x₁.val x₂.val then
        replace hlt : i < n := by
          omega
        exists ⟨i, hlt⟩

        simp [hlt₂]
      else
        simp at hlt₂
        exists Fin.pred ⟨i, hlt⟩ ?_
        simp
        omega -- b/c hneq and hlt₂
        rw [if_neg, Fin.succ_pred]
        dsimp
        intro hlt₃
        have heq : max x₁.val x₂.val = i := by omega
        subst heq
        clear hlt₂ hlt₃
        by_cases hcmp: x₁.val ≤ x₂.val <;> simp_all [Nat.max_def]

theorem finite_imp_exists_injection {A: Type} (A_finite: Finite A): ∃f: A → Nat, Injective f := by
  let Family: Set (Set A) := Set.full_image (fun f: A → Nat => Set.mk fun a => ∀a', f a = f a' → a = a')

  obtain ⟨M, ⟨f, rfl⟩, maximal⟩ := (finite_iff_maximal_exists A).mp A_finite Family (by
    exists Set.mk fun a => ∀a', (fun _ => 0) a = (fun _ => 0) a' → a = a'
    exists (fun _ => 0)
  )
  simp_all
  exists f
  apply Injective.intro
  intro a₁
  have f_not_surj := finite_imp_not_surjective A A_finite f
  rw [Surjective.not_surj_iff_exists_hole] at f_not_surj
  obtain ⟨hole, hole_hole⟩ := f_not_surj
  let f' (a: A) : Nat := open Classical in   if a = a₁ then hole else f a

  have : (Set.mk fun a => ∀a', f a = f a' → a = a') ⊆ (Set.mk fun a => ∀a', f' a = f' a' → a = a') := by
    intro x
    simp [f']
    intro h y
    split <;> simp_all [@Eq.comm _ y]
    case isTrue heq =>
      subst heq
      intro h
      rw [← Classical.or_iff_not_imp_left] at h
      rcases h with rfl | h
      rfl
      exact False.elim $ hole_hole y h.symm
    case isFalse hneq =>
      intro k
      apply h
      split at k
      case a.isTrue heq =>
        subst heq
        exact False.elim (hole_hole x k)
      case a.isFalse hneq =>
        exact k
  replace maximal := maximal (Set.mk fun a => ∀a', f' a = f' a' → a = a') (by exists f') this
  simp [funext_iff, f'] at maximal
  replace maximal := maximal a₁
  simp [← Classical.or_iff_not_imp_left] at maximal
  rw [← maximal]
  clear this maximal f'
  intro a₂ rfl
  exact False.elim (hole_hole a₂ rfl)


theorem finite_iff_exists_injection_fin {A: Type}: Finite A ↔ ∃n, ∃f: A → Fin n, Injective f where
  mp A_finite := by
    obtain ⟨f, f_inj⟩ := finite_imp_exists_injection A_finite
    have ⟨bound, bounded⟩ := finite_imp_bounded A_finite f
    exists bound + 1
    exists fun a => ⟨f a, by
      replace bounded := bounded a
      omega
    ⟩
    apply Injective.intro
    simp
    exact f_inj.eq_of_ap_eq
  mpr:= by
    rintro ⟨n, f, f_inj⟩
    apply finite_of_injective_finite f f_inj (finite_fin n)

/--
  This is just the same as being well-founded
-/
theorem exists_minimal_nat {p: Nat → Prop}: (∃m, p m) → ∃n, p n ∧ ∀m, p m → n ≤ m := by
  intro ⟨m, pm⟩
  induction m using Nat.strongRecOn
  case ind m hm =>
    by_cases ∀n < m, ¬p n
    case pos h =>
      exists m
      constructor; assumption
      intro m' pm'
      replace h := fun le => h m' le pm'
      exact Nat.le_of_not_lt h
    case neg h =>
      simp at h
      obtain ⟨n, hlt, pn⟩ := h
      replace hm := hm n hlt pn
      exact hm

theorem finite_iff_exists_bijection_fin {A: Type}: Finite A ↔ ∃n, ∃f: A → Fin n, Bijective f where
  mp A_finite := by
    obtain ⟨n, ⟨f, f_inj⟩, h₂⟩ := exists_minimal_nat $ (finite_iff_exists_injection_fin).mp A_finite
    exists n, f
    constructor; exact f_inj
    cases n
    case zero =>
      apply Surjective.vacuous
      exact fun a => nomatch a
    case succ n =>
      cases exists_injection_fin_succ_imp_exists_injection_fin_or_surjective f f_inj
      case inr => assumption
      case inl h' =>
        replace h₂ := h₂ n h'
        omega
  mpr := by
    intro ⟨n, f, f_inj, f_surj⟩
    rw [finite_iff_exists_injection_fin]
    exists n, f

/--
  Interpretting a function `f: Fin n → X` as a list of values, inserts the value `x` at position `i`
-/
def insert_fin (f: Fin n → X) (i: Fin (n + 1)) (x: X): Fin (n + 1) → X :=
  fun j =>
    if hneq: j = i then
      x
    else if hlt: j < i then
      have : j < n := by omega

      f (Fin.castLT j this)
    else
      have : j ≠ 0 := by
        induction i <;> induction j <;> simp [Fin.ext_iff] at * <;> omega
      f (Fin.pred j this)

theorem insert_fin_idx (f: Fin n → X) (i: Fin (n + 1)) (x: X) : insert_fin f i x i = x := by
  unfold insert_fin
  simp

theorem insert_fin_lt (f: Fin n → X) (i j: Fin (n + 1)) (x: X) (h: j < i):
  have : j < n := by
    induction i <;> omega
  insert_fin f i x j = f (Fin.castLT j this) := by
  have : j ≠ i := by omega
  simp [insert_fin, this, h]





noncomputable def graph_eval (s: Set (A × B)) (input: ∀a, ∃b, (a,b) ∈ s) (a: A): B := (input a).choose



noncomputable def fun_graph_ind {motive: (A → B) → Sort u}
  (graph: (s: Set (A × B)) →
          (input: ∀a, ∃b, (a,b) ∈ s) →
          (unique: ∀a b₁ b₂, (a, b₁) ∈ s → (a, b₂) ∈ s → b₁ = b₂) →
          motive (fun a => graph_eval s input a)) (f: A → B): motive f := by
  replace graph := graph (Set.mk fun (a,b) => f a = b) (by
    intro a
    exists f a
  ) (by
    intro a b₁ b₂ h₁ h₂
    simp_all
  )

  have : f = fun a => (Exists.intro (f a) (Eq.refl (f a))).choose := by
    funext a
    exact (Exists.intro (f a) (Eq.refl (f a))).choose_spec
  rw [this]
  exact graph

theorem fin_fn_not_inj {f: Fin (n + 1) → Fin n}: ¬Injective f := by
  intro f_inj
  induction n
  case zero =>
    nomatch f 0
  case succ n' ih =>
    by_cases n' = 0
    case pos heq =>
      subst heq
      have t₀: f 0 = 0 := Fin.fin_one_eq_zero (f 0)
      have t₁: f 1 = 0 := Fin.fin_one_eq_zero (f 1)
      rw [← t₁] at t₀
      apply @Fin.zero_ne_one 0
      apply f_inj.eq_of_ap_eq _ _ t₀
    case neg hlt =>
    replace hlt : 0 < n' := by omega

    generalize hk: f 0 = k
    induction k using Fin.cases
    case zero =>
      have h: ∀i: Fin (n' + 1), f i.succ ≠ 0 := by
        rw [← hk]
        intro i h
        apply Fin.succ_ne_zero i
        exact f_inj.eq_of_ap_eq _ _ h
      let g (a: Fin (n' + 1)): Fin n' := (f a.succ).pred (h a)
      apply @ih g
      apply Injective.intro
      intro a₁ a₂ heq
      simp [g, f_inj] at heq
      exact heq
    case succ k =>
      let g (a: Fin (n' + 1)): Fin n' := if h: f a.succ = 0 then k else Fin.pred (f a.succ) h
      apply @ih g
      apply Injective.intro
      intro a₁ a₂ heq
      simp [g] at heq
      by_cases h₁: f a₁.succ = 0 <;> by_cases h₂: f a₂.succ = 0 <;> simp_all
      case pos =>
        rw [← Fin.succ_inj, ← f_inj.imp_eq_iff_app_eq _ _, h₁, h₂]
      case neg =>
        exfalso
        apply Fin.succ_ne_zero a₂
        exact id (Eq.symm hk)
      case pos =>
        subst heq
        simp [f_inj] at hk
        exfalso
        apply Fin.succ_ne_zero a₁
        exact hk.symm

theorem never_inj_imp_never_surj {A B: Type} (never_inj: ∀f: A → B, ¬Injective f): ∀g: B → A, ¬ Surjective g := by
  apply Classical.byContradiction
  intro h; simp at h
  revert never_inj
  simp
  obtain ⟨g, g_surj⟩ := h
  obtain ⟨g_inv, h⟩ := g_surj.exists_right_inv
  exists g_inv
  apply Injective.of_exists_left_inv g h

theorem never_surj_imp_never_inj {A B: Type} [inst: Nonempty (A → B)] (never_surj: ∀f: A → B, ¬Surjective f): ∀g: B → A, ¬Injective g := by
  apply Classical.byContradiction
  intro h; simp at h
  revert never_surj
  simp
  obtain ⟨g, g_inj⟩ := h
  obtain ⟨g_inv, h⟩ := g_inj.exists_left_inv
  exists g_inv
  exact Surjective.of_exists_right_inv g h

theorem never_inj_iff_never_surj {A B: Type} [inst: Nonempty (B → A)]: (∀f: A → B, ¬Injective f) ↔ (∀g: B → A, ¬Surjective g) where
  mp := never_inj_imp_never_surj
  mpr := never_surj_imp_never_inj

theorem fin_fn_not_surj {f: Fin n → Fin (n + 1)}: ¬Surjective f := by
  apply never_inj_imp_never_surj
  exact fun f => fin_fn_not_inj


-- I ACTUALLY DID IT!!!
theorem exists_inj_imp_le {n m: Nat} (f: Fin n → Fin m) (f_inj: Injective f): n ≤ m := by
  apply Nat.le_of_not_lt
  intro hlt
  induction hlt
  case a.refl =>
    exact fin_fn_not_inj f_inj
  case a.step m' h ih =>
    let f' := f ∘ Fin.castSucc
    have f'_inj : Injective f' := by
      apply Injective.comp_inj
      · apply Injective.intro
        intro a₁ a₂ heq
        exact Fin.castSucc_inj.mp heq
      assumption
    exact ih f' f'_inj


theorem exists_surj_imp_le {n m: Nat} (f: Fin n → Fin m) (f_surj: Surjective f): m ≤ n := by
  by_cases n = 0
  case pos heq =>
    subst heq
    apply Classical.byContradiction
    intro h
    rw [Nat.not_le] at h
    obtain ⟨what, _⟩ := f_surj.exists_ap_eq ⟨0, h⟩
    nomatch what
  case neg hneq =>
    have hlt : 0 < n := by exact Nat.zero_lt_of_ne_zero hneq
    have : Nonempty (Fin n) := ⟨⟨0, hlt⟩⟩

    have := surj_imp_inv_inj f_surj
    exact exists_inj_imp_le (inv f) this

theorem fin_le_imp_not_surj {n m: Nat} (h: n < m) {f: Fin n → Fin m}: ¬Surjective f := by
  intro f_surj
  have hle := exists_surj_imp_le f f_surj
  omega

def Option.swap_none {A} [DecidableEq A] (a: A): Option A → Option A
| some b =>
  if a = b then none else some b
| none => a

@[simp]
theorem Option.swap_none_self {A} [DecidableEq A] (a: A): swap_none a (some a) = none := by
  simp [Option.swap_none]

@[simp]
theorem Option.swap_none_none {A} [DecidableEq A] (a: A): swap_none a none = some a := by
  simp [Option.swap_none]

theorem Option.swap_none_neq {A} [DecidableEq A] (a b: A) (hneq: a ≠ b): swap_none a (some b) = some b := by
  simp [Option.swap_none, hneq]

theorem Option.swap_none_bij {A} [DecidableEq A] (a: A): Bijective (Option.swap_none a) where
  eq_of_ap_eq a₁ a₂ heq := by
    cases a₁ <;> cases a₂ <;> simp_all [swap_none]
    next a' =>
      exact heq.left (heq.right.symm)
    next a₁ a₂ =>
      split at heq
      next heq' =>
        subst heq'
        simp at heq
        exact heq
      next hneq =>
        split at heq
        next heq' =>
          subst heq'
          contradiction
        next hneq =>
          injection heq

  exists_ap_eq b := by
    cases b
    case none =>
      exists a
      simp [swap_none]
    case some a' =>
      by_cases a = a'
      case pos heq =>
        subst heq
        exists none
      case neg hneq =>
        exists a'
        exact swap_none_neq a a' hneq

#check Option.eq_some_iff_get_eq

theorem option_option_bij_imp_exists_bij {A B: Type u} (f: Option A → Option B) (f_bij: Bijective f): ∃f': A → B, Bijective f' := by
  open Classical in
  obtain ⟨k, hk⟩ := f_bij.exists_ap_eq none
  cases k
  case none =>
    let f' : A → B := fun a =>
      (f (some a)).get (by
        refine Option.isSome_iff_ne_none.mpr ?_
        intro heq
        apply Option.some_ne_none a
        rw [← hk] at heq
        exact f_bij.eq_of_ap_eq _ _ heq
      )
    exists f'
    apply Bijective.of_inj_and_surj
    · refine Injective.intro fun a₁ a₂ heq => ?_
      dsimp [f'] at *
      simp [Option.get_inj, f_bij.toInjective] at heq
      exact heq
    · refine Surjective.intro fun b => ?_
      obtain ⟨a', heq⟩ := f_bij.exists_ap_eq (some b)
      cases a'
      case none =>
        exfalso
        rw [hk] at heq
        contradiction
      case some a =>
        exists a
        simp [f', heq]

  case some a =>
    let f' : A → B := fun x =>
      (f (Option.swap_none a (some x))).get (by
        refine Option.isSome_iff_ne_none.mpr ?_
        intro heq
        dsimp [Option.swap_none] at heq
        rw [← hk, f_bij.imp_eq_iff_app_eq] at heq
        split at heq
        case isTrue rfl =>
          contradiction
        case isFalse hneq =>
          replace heq := (Option.some_inj.mp heq).symm
          exact hneq heq
      )
    exists f'
    apply Bijective.of_inj_and_surj
    · apply Injective.intro
      intro a₁ a₂ heq
      simp [f', Option.get_inj, f_bij.toInjective, (Option.swap_none_bij a).toInjective] at heq
      exact heq
    · apply Surjective.intro
      intro b
      obtain ⟨a', heq⟩ := f_bij.exists_ap_eq (some b)
      cases a'
      next =>
        exists a
        simp [f', heq]
      next a' =>
        have hneq : a ≠ a' := by
          intro rfl
          rw [hk] at heq
          contradiction
        exists a'
        simp [f']
        apply Option.get_of_eq_some
        rw [Option.swap_none_neq a a' hneq]
        exact heq

theorem fin_bijective_imp_equal {n m: Nat} (f: Fin n → Fin m) (f_bij: Bijective f): n = m := by
  induction m generalizing n
  case zero =>
    cases n
    case zero => rfl
    case succ n' => nomatch f ⟨0, by omega⟩
  case succ m' ih =>
    cases n
    case zero =>
      nomatch (f_bij.exists_ap_eq ⟨0, Nat.zero_lt_succ m'⟩).choose
    case succ n' =>
      apply Nat.succ_inj.mpr

      generalize hf': (Fin.castOption) ∘ f ∘ (inv Fin.castOption) = f'
      obtain rfl : (inv Fin.castOption) ∘ f' ∘ Fin.castOption = f := by
        subst hf'
        change ((inv Fin.castOption) ∘ Fin.castOption) ∘ f ∘ ((inv Fin.castOption) ∘ (Fin.castOption)) = f
        repeat rw [Fin.castOption_bij.inv_left_inv]
        rfl
      clear hf'
      replace f_bij: Bijective f' := by
        have : Bijective ((Fin.castOption ∘ (inv Fin.castOption)) ∘ f' ∘ (Fin.castOption ∘ (inv Fin.castOption))) := by
          refine
            Bijective.comp_bij ((inv Fin.castOption ∘ f' ∘ Fin.castOption) ∘ inv Fin.castOption)
              Fin.castOption ?_ (Fin.castOption_bij)
          refine
            Bijective.comp_bij (inv Fin.castOption) (inv Fin.castOption ∘ f' ∘ Fin.castOption) ?_
              f_bij
          refine inv_bij Fin.castOption Fin.castOption_bij
        simp [Fin.castOption_bij.inv_right_inv] at this
        exact this

      obtain ⟨f, yea⟩ := option_option_bij_imp_exists_bij f' f_bij
      exact @ih _ f yea

theorem full_image_repeat_descends {X: Type u} (f: X → X) (n: Nat): Set.full_image (Nat.repeat f (n + 1)) ⊆ Set.full_image (Nat.repeat f n) := by
  intro x ⟨x', heq⟩
  subst heq

  rw [Nat.repeat_succ_eq_comp_right]
  exact Set.always_in_image (Nat.repeat f n) (f x')

theorem full_image_repeat_monotone {X: Type u} (f: X → X) {n m: Nat}: n ≤ m → Set.full_image (Nat.repeat f m) ⊆ Set.full_image (Nat.repeat f n ) := by
  intro hle
  induction hle
  case refl => exact Set.subset_refl _
  case step m' hle' ih =>
    have := @full_image_repeat_descends _ f m'
    exact @Set.subset_trans _ _ _ _ @this ih

theorem Classical.prop_finite : Finite Prop := by
  apply finite_iff_exists_injection_fin.mpr
  exists 2
  exists fun (p: Prop) =>
    if p then 0 else 1
  apply Injective.intro
  intro p₁ p₂ heq
  by_cases h₁:p₁ <;> by_cases h₂: p₂ <;> simp_all


-- theorem finite_fn_finite_finite {X Y: Type} (X_finite: Finite X) (Y_finite: Finite Y): Finite (X → Y) := by
--   refine (finite_iff_maximal_exists (X → Y)).mpr ?_
--   intro F F_nonempty
--   sorry

-- i don't think that nilpotent is the right descriptor here
theorem finite_imp_nilpotent {X: Type u} (X_finite: Finite X)
(f: X → X): ∃n, Set.full_image (Nat.repeat f (n + 1)) = Set.full_image (Nat.repeat f n) := by

  -- First I define the family of subsets of X which are the images of each fⁿ
  let chain: Set (Set X) := Set.full_image fun (n: Nat) => Set.full_image (Nat.repeat f n)

  -- Then I use `finite_iff_minimal_exists` to prove that there exists a minimal subset in this family
  -- I need to prove that this set is nonempty, so I use `Set.all` as an example, which
  -- is in the family because the image of `f⁰` is the whole set
  obtain ⟨m, ⟨n, heq⟩, m_minimal⟩ := (finite_iff_minimal_exists X).mp X_finite chain ⟨Set.all, 0, (by simp [Nat.repeat, Set.ext_iff])⟩
  dsimp at heq

  -- I then substitute this minimal subset `m` with it's definition `Set.full_image (Nat.repeat f n)`
  subst heq

  -- Then to prove the goal, I say that this number `n` satisfies the condition
  exists n
  -- Then I use the fact that `m` is minimal and that the image of the next image is a subset
  -- to close the goal
  exact m_minimal (Set.full_image (Nat.repeat f (n + 1))) ⟨n + 1, rfl⟩ (@full_image_repeat_descends _ f n)

#print axioms finite_imp_nilpotent
#print axioms finite_iff_minimal_exists

theorem finite_fn_self_imp_injection_imp_surjection {X: Type u} (X_finite: Finite X) (f: X → X):
  Injective f → Surjective f := by
  intro f_inj
  obtain ⟨n, h⟩ := finite_imp_nilpotent X_finite f

  rw [Nat.repeat_succ_eq_comp_right, Set.full_image_comp, ← Set.image_all (Nat.repeat f n)] at h
  have : Injective (Set.image (Nat.repeat f n)) := by
    refine (Set.image_inj_iff_inj (Nat.repeat f n)).mpr ?_
    exact Injective.repeat_inj f_inj n
  rw [this.imp_eq_iff_app_eq] at h
  exact Surjective.of_full_image_eq_all f h


#print axioms finite_fn_self_imp_injection_imp_surjection
theorem finite_fn_self_imp_injection_iff_surjection {X: Type u} (X_finite: Finite X) (f: X → X):
  Injective f ↔ Surjective f where
  mp := finite_fn_self_imp_injection_imp_surjection X_finite f

  mpr f_surj := by
    have ⟨f_inv, h_inv⟩ := f_surj.exists_right_inv
    have f_inv_inj: Injective f_inv := by exact Injective.of_exists_left_inv f h_inv
    have f_inv_surj: Surjective f_inv := by exact
      finite_fn_self_imp_injection_imp_surjection X_finite f_inv f_inv_inj
    have f_inv_bij : Bijective f_inv := Bijective.of_inj_and_surj f_inv_inj f_inv_surj
    have : f_inv ∘ f = id := by
      have : f_inv ∘ f ∘ f_inv = f_inv ∘ id := by exact congrArg (Function.comp f_inv) h_inv
      change (f_inv ∘ f) ∘ f_inv = id ∘ f_inv at this
      rw [f_inv_surj.right_cancellative_iff] at this
      exact this
    exact Injective.of_exists_left_inv f_inv this
