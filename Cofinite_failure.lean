inductive CofinitePredicate {X: Type}: (X → Prop) → Prop where
| whole : CofinitePredicate (fun _ => True)
| remove_unique (pred: X → Prop) (x₀: X) : pred x₀ → CofinitePredicate pred →
  CofinitePredicate (fun x => x ≠ x₀ ∧ pred x)


def CofinitePredicate.remove (x₀: X): CofinitePredicate pred →
  CofinitePredicate (fun x => x ≠ x₀ ∧ pred x) := by
  intro pred_cofinite
  by_cases pred x₀
  case pos h =>
    exact remove_unique _ x₀ h pred_cofinite
  case neg h₁ =>
    have : (fun x => x ≠ x₀ ∧ pred x) = pred := by
      funext x
      apply propext
      constructor
      intro h₂; apply h₂.right
      intro h₂
      constructor
      intro heq; cases heq; case refl =>
        exact h₁ h₂
      exact h₂
    rw [this]
    assumption

theorem CofinitePredicate_intersection {X: Type} (p₁ p₂: X → Prop) (h₁: CofinitePredicate p₁)
  (h₂: CofinitePredicate p₂): CofinitePredicate (fun x => p₁ x ∧ p₂ x) := by
    induction h₁
    case whole =>
      simp
      exact h₂
    case remove_unique p₁' x h p₁'_finite ih =>
      have : (fun x_1 => p₁' x_1 ∧ p₂ x_1) =
        fun x_1 => ¬x_1 = x ∧ (p₁' x_1 ∧ p₂ x_1) := by
        funext _
        exact propext and_assoc
      rw [this]
      exact CofinitePredicate.remove x ih

theorem CofinitePredicate.add {X: Type} (x₀: X) (p: X → Prop) (h: CofinitePredicate p):
CofinitePredicate (fun x => x = x₀ ∨ p x) := by
  induction h
  case whole =>
    have : (fun x => x = x₀ ∨ (fun x => True) x) = fun x => True := by
      funext x
      exact or_true (x = x₀)
    rw [this]
    exact CofinitePredicate.whole
  case remove_unique pred x₁ pred_x₁ pred_cofinite ih =>
    by_cases x₀ = x₁
    case pos heq =>
      cases heq
      have : (fun x => x = x₀ ∨ ¬x = x₀ ∧ pred x) = (fun x => x = x₀ ∨ pred x) := by
        funext x
        refine propext (Iff.intro ?_ ?_)
        intro ha
        cases ha
        case inl h => exact Or.inl h
        case inr h => exact Or.inr h.right
        intro hb
        cases hb
        case inl h => exact Or.inl h
        case inr h =>
          by_cases x = x₀
          case pos _ => left; assumption
          case neg _ => right; constructor; assumption; assumption
      rw [this]
      exact ih
    case neg hneq =>
      have : (fun x => x = x₀ ∨ ¬x = x₁ ∧ pred x) = (fun x => ¬x = x₁ ∧ (x = x₀ ∨ pred x)) := by
        funext x
        refine propext (Iff.intro ?_ ?_)
        intro ha
        cases ha
        case inl heq =>
          cases heq
          exact And.intro hneq (Or.inl rfl)
        case inr hneq₂ =>
          refine And.intro hneq₂.left (Or.inr hneq₂.right)

        intro hb
        cases hb.right
        case inl heq =>
          exact Or.inl heq
        case inr hneq₂ =>
          exact Or.inr (And.intro hb.left hneq₂)
      rw [this]
      exact CofinitePredicate.remove _ ih


theorem superset_CofinitePredicate {X: Type} (p₁ p₂: X → Prop) (h₁: ∀x, p₂ x → p₁ x)
  (h₂: CofinitePredicate p₂): CofinitePredicate p₁ := by
    induction h₂
    case whole =>
      have : p₁ = fun x => True := by
        funext x
        exact eq_true (h₁ x trivial)
      rw [this]; exact CofinitePredicate.whole
    case remove_unique pred x₀ pred_x₀ pred_cofinite ih =>
      apply ih
      intro x h
      apply h₁






#check CofinitePredicate.add



theorem CofinitePredicate_union {X: Type} (p₁ p₂: X → Prop) (h₁: CofinitePredicate p₁):
CofinitePredicate (fun x => p₁ x ∨ p₂ x) := by
    induction h₁
    case whole =>
      have : (fun x => True ∨ p₂ x) = fun _ => True := by
        funext x
        exact true_or (p₂ x)
      rw [this]
      exact CofinitePredicate.whole
    case remove_unique pred x₀ pred_x₀ pred_cofinite ih =>
      simp [*]
      sorry




---






---
/-
inductive Finite (X: Type): Type where
  | singleton (x₀: X): Finite X
  | union: Finite X → Finite X → Finite X


def Finite.non_member {X: Type} (x: X): Finite X → Prop
  | singleton x₀ => x ≠ x₀
  | union c₁ c₂ => c₁.non_member x ∧ c₂.non_member x

-- "For an indexed collection of cofinite sets, there exists a cofinite
-- set which is the union of all of them"
def Finite.arb_union {X I: Type} (coll: I → Finite X): ∃f: Finite X,
  ∀x, Finite.non_member x f → ∃i: I, (coll i).non_member x := by
  apply Classical.not_not.mp
  intro h
  simp at h
  apply h

def cofinite_topology {X: Type} : Topology X := Topology.mk
  (is_open := fun p => ((∀x, p x) ∨ (∀x, ¬p x)) ∨ ∃c: Finite X, ∀x:X, c.non_member x → p x)
  (whole_set_open := by simp
  ) (intersection_open := by
    intro U U_open V V_open
    cases U_open <;> cases V_open
    case inl.inl h₁ h₂ =>
      left
      cases h₁ <;> cases h₂
      case inl.inl h₁ h₂ => exact Or.inl fun x => ⟨h₁ x, h₂ x⟩
      case inr.inl h₁ h₂ => exact Or.inr fun x => not_and.mpr fun a a_1 => h₁ x a
      case inl.inr h₁ h₂ => exact Or.inr fun x => not_and.mpr fun a => h₂ x
      case inr.inr h₁ h₂ => exact Or.inr fun x => not_and.mpr fun a => h₂ x
    case inr.inl h₁ h₂ =>
      cases h₂
      case inl h₂ =>
        right
        exists h₁.choose
        intro x what
        refine And.intro (h₁.choose_spec x what) (h₂ x)
      case inr h₂ =>
        left; right
        exact fun x => not_and.mpr fun a => h₂ x
    case inl.inr h₁ h₂ =>
      cases h₁
      case inl h₁ =>
        right
        exists h₂.choose
        intro x what
        exact And.intro (h₁ x) (h₂.choose_spec x what)
      case inr h₁ =>
        left; right
        exact fun x => not_and.mpr fun a a_1 => h₁ x a
    case inr.inr h₁ h₂ =>
      right
      exists Finite.union h₁.choose h₂.choose
      intro x what
      constructor
      unfold Finite.non_member at what
      exact h₁.choose_spec x what.left
      exact h₂.choose_spec x what.right
  ) (open_cover_subsets_imp_open := by
    simp
    intro U cond
    apply Classical.or_iff_not_imp_left.mpr
    intro h
    simp at h
    sorry
  )
-/
