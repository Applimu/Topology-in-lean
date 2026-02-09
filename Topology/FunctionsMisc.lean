
import Topology.Functions


/--
Restricts the output of a function into it's image
-/
def into_image {A B: Type u} (f: A → B): A → Set.subtype (Set.full_image f) := fun a => ⟨f a, a, rfl⟩

theorem surj_into_image {A B: Type u} (f: A → B): Surjective (into_image f) := by
  apply Surjective.intro
  rintro ⟨b, a, heq⟩
  subst heq
  simp [into_image]


--theorem into_image_eq_imp_f_eq : into_image f a = into_image f b → f a = f b := by
--  simp [into_image]
--  intro h
--  apply Subtype.val_inj.eq_of_ap_eq

def quot_from {A B: Type u} (f: A → B) : @Quot A (fun a₁ a₂ => f a₁ = f a₂) → B := Quot.lift f (fun a b h => by trivial)

theorem quot_from_inj {A B: Type u} (f: A → B) : Injective (quot_from f) := by
  apply Injective.intro
  intro a₁ a₂ heq
  induction a₁ using Quot.ind
  case eq_of_ap_eq.mk a₁ =>
  induction a₂ using Quot.ind
  case mk a₂ =>
  simp [quot_from] at *
  exact Quot.sound heq


--theorem quot_from_into_image_eq_into_image_quot_from : ∀a, HEq (quot_from (into_image f) a) (into_image (quot_from f) (cast _ a) ) := by


theorem cantors_paradox (f: X → Set X): ¬Surjective f := by
  intro f_surj
  let B: Set X := Set.mk fun x => ¬x ∈ f x
  obtain ⟨b, h⟩ := f_surj.exists_ap_eq B
  simp [Set.ext_iff, B] at h
  exact iff_not_self (h b)


theorem cantors_paradox' (f: Set X → X): ¬Injective f := by
  rw [← Set.preimage_surj_iff_inj]
  exact cantors_paradox (Set.preimage f)

section

variable {X Y: Type u} (U: Set X) (f: X → Y)

def restrict (U: Set X) (f: X → Y) : U.subtype → Y := fun ⟨x, _⟩ => f x

end

section






structure Idempotent {X: Type u} (f: X → X) where intro ::
  comp_self: f ∘ f = f

theorem idem_id {X: Type u}: Idempotent (@id X) where
  comp_self := by rfl

theorem Idempotent_inj_imp_eq_id {f: X → X} (f_idem: Idempotent f) (f_inj: Injective f): f = id := by
  apply Injective.left_cancellative f f_inj
  rw [f_idem.comp_self]
  rfl

theorem Idempotent_surj_imp_eq_id {f: X → X} (f_idem: Idempotent f) (f_surj: Surjective f): f = id := by
  apply Surjective.right_cancellative f f_surj
  rw [f_idem.comp_self]
  rfl

theorem exists_left_idempotent {X Y: Type u} (f: X → Y) [Nonempty (Y → X)]: ∃g: Y → X, Idempotent (g ∘ f) := by
  exists inv f
  apply Idempotent.intro
  change inv f ∘ (f ∘ inv f ∘ f) = _
  rw [self_inv_self]

theorem exists_right_idempotent {X Y: Type u} (f: X → Y) [Nonempty (Y → X)]: ∃g: Y → X, Idempotent (f ∘ g) := by
  exists inv f
  apply Idempotent.intro
  change (f ∘ inv f ∘ f) ∘ inv f = _
  rw [self_inv_self]

#print axioms exists_right_idempotent

theorem idem_of_comm_eq_id {X Y: Type u} (f: X → Y) (g: Y → X) (h_inv: f ∘ g = id): Idempotent (g ∘ f) := by
  apply Idempotent.intro
  change g ∘ (f ∘ g) ∘ f = _
  rw [h_inv]
  rfl

theorem idem_of_comm_idems {X: Type u} (f g: X → X) (comm: f ∘ g = g ∘ f): Idempotent f → Idempotent g → Idempotent (g ∘ f) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  apply Idempotent.intro
  change g ∘ (f ∘ g) ∘ f = _
  rw [comm]
  change (g ∘ g) ∘ (f ∘ f) = _
  rw [h₁, h₂]

theorem repeat_idem {X: Type u} (f: X → X) (f_idem: Idempotent f) (hn: 0 < n): Nat.repeat f n = f := by
  induction hn
  case refl => rfl
  case step n' h ih =>
  clear h -- always true
  funext x
  unfold Nat.repeat
  rw [ih]
  change (f ∘ f) x = f x
  rw [f_idem.comp_self]

theorem idem_full_image (e_idem: Idempotent e): ∀x ∈ Set.full_image e, e x = x := by
  intro y ⟨x, heq⟩
  subst heq
  exact congrFun (e_idem.comp_self) x

theorem idem_of_id_full_image {e: X → X} (h: ∀x ∈ Set.full_image e, e x = x): Idempotent e where
  comp_self := by
    ext x
    exact h (e x) (Set.always_in_image e x)

/-
  L:   ∀x, (∃s, sa = x) ↔ (∃s, sb = x)
  R:   ∀x, (∃s, as = x) ↔ (∃s, bs = x)
  L:   ∀x, (∃s₁ s₂, s₁as₂ = x) ↔ (∃s₁ s₂, s₁bs₂ = x)
-/

/--
  Every function is the composition of a surjection and then an injection.
-/
theorem factors {A B: Type u} (f: A → B): ∃Z: Type u, ∃i: Z → B, Injective i ∧ ∃s: A → Z, Surjective s ∧  i ∘ s = f := by
  -- There are weird universe level things if you try to make `A` and `B` have different levels.
  exists Set.subtype (@Set.full_image A B f)
  exists Subtype.val
  constructor
  exact Subtype.val_inj
  exists fun a => ⟨f a, a, rfl⟩
  constructor
  apply Surjective.intro
  intro ⟨b, a, heq⟩
  subst heq
  exists a
  funext x
  rfl


def idk {X Y: Type u} (g₁ g₂: Y → X): Prop := ∀f: X → Y, f ∘ g₁ ∘ f = f ↔ f ∘ g₂ ∘ f = f

theorem idk_iff {X Y: Type u} (g₁ g₂: Y → X) : idk g₁ g₂ ↔ ∀Z: Type u, ∀i: Z → Y, Injective i → ∀s: X → Z, Surjective s → (s ∘ g₁ ∘ i = id ↔ s ∘ g₂ ∘ i = id) where
  mp h := by
    intro Z i i_inj s s_surj
    replace h := h (i ∘ s)
    change i ∘ (s ∘ g₁ ∘ i) ∘ s = i ∘ id ∘ s ↔ i ∘ (s ∘ g₂ ∘ i) ∘ s = i ∘ id ∘ s  at h
    rw [Injective.left_cancellative_iff i i_inj, Injective.left_cancellative_iff i i_inj] at h
    rw [Surjective.right_cancellative_iff s s_surj, Surjective.right_cancellative_iff s s_surj] at h
    exact h
  mpr h := by
    intro f
    have ⟨Z, i, i_inj, s, s_surj, heq⟩ := factors f
    subst heq
    replace h := h Z i i_inj s s_surj
    change i ∘ (s ∘ g₁ ∘ i) ∘ s = i ∘ id ∘ s ↔ i ∘ (s ∘ g₂ ∘ i) ∘ s = i ∘ id ∘ s
    rw [Injective.left_cancellative_iff i i_inj, Injective.left_cancellative_iff i i_inj]
    rw [Surjective.right_cancellative_iff s s_surj, Surjective.right_cancellative_iff s s_surj]
    exact h



instance idk_equiv {X Y: Type u} [Nonempty (X → Y)]: Equivalence (@idk X Y) where
  refl g := by
    intro f
    rfl
  symm {g₁ g₂} := by
    intro idg f
    exact Iff.symm (idg f)
  trans {g₁ g₂ g₃} := by
    intro h₁ h₂ f
    apply Iff.trans (b := f ∘ g₂ ∘ f = f)
    exact h₁ f
    exact h₂ f

theorem idk_comp {X Y Z: Type u} (f₁ g₁: Y → Z) (f₂ g₂: X → Y) (h: ∃i: Z → Y, Injective i):
idk f₁ g₁ → idk f₂ g₂ → idk (f₁ ∘ f₂) (g₁ ∘ g₂) := by
  intro h₁ h₂
  intro r
  rw [idk_iff] at *

  have : ∀i: Z → Y, Injective i → (f₁ ∘ i = id ↔ g₁ ∘ i = id) := by
    intro i i_inj

    have hi := h₁ i
    replace hi : f₁ ∘ i = id ↔ g₁ ∘ i = id := by
      rw [← Injective.left_cancellative_iff i i_inj]
      apply Iff.symm
      rw [← Injective.left_cancellative_iff i i_inj]
      dsimp
      exact Iff.symm hi
    exact hi





  have hf₂ := h₁ (f₂ ∘ r)
  have hg₂ := h₁ (g₂ ∘ r)
  have hf₁ := h₂ (r ∘ f₁)
  have hg₁ := h₂ (r ∘ g₁)


  constructor
  . intro heq
    replace hf₂ : f₂ ∘ (r ∘ g₁ ∘ f₂ ∘ r) = f₂ ∘ r := by
      change f₂ ∘ (r ∘ (f₁ ∘ f₂) ∘ r) = _ ↔ _ at hf₂
      rw [heq] at hf₂
      simp at hf₂
      exact hf₂
    replace hf₁: (r ∘ f₁ ∘ g₂ ∘ r) ∘ f₁ = r ∘ f₁ := by
      change  (r ∘ (f₁ ∘ f₂) ∘ r) ∘ f₁ = r ∘ f₁ ↔ _ at hf₁
      rw [heq] at hf₁
      simp at hf₁
      exact hf₁







theorem idk_imp_eq {X Y: Type u} {g₁ g₂: Y → X} : idk g₁ g₂ → g₁ = g₂ := by
  intro h
  funext y
  dsimp [idk] at h
  by_cases Nonempty (X → Y)
  case neg h_mt =>
    exfalso
    exact h_mt ⟨fun _ => y⟩
  case pos h_nmt =>
    have := h (inv g₁ ∘ g₁ ∘ inv g₁)
    change (inv g₁ ∘ ((g₁ ∘ inv g₁ ∘ g₁) ∘ inv g₁ ∘ g₁) ∘ inv g₁ = _) ↔ _ at this
    rw [self_inv_self, self_inv_self] at this
    simp at this
    replace := congrFun this (g₁ y)
    change (inv g₁ ∘ g₁ ∘ (inv g₁ ∘ g₂ ∘ inv g₁) ∘ (g₁ ∘ inv g₁ ∘ g₁)) y = _ at this
    rw [self_inv_self] at this




end

section

structure Constant {X: Type u} {Y: Type v} (f: X → Y) where intro::
  ap_eq_ap: ∀x₁ x₂, f x₁ = f x₂

namespace Constant

variable {X Y Z: Type} (f: X → Y) (g: Y → Z)

theorem constant_comp_left (g_const: Constant g): Constant (g ∘ f) := Constant.intro fun x₁ x₂ => g_const.ap_eq_ap (f x₁) (f x₂)

theorem constant_comp_right (f_const: Constant f): Constant (g ∘ f) := Constant.intro fun x₁ x₂ => congrArg g $ f_const.ap_eq_ap x₁ x₂

theorem from_subsingleton (X_sub: Subsingleton X): Constant f := Constant.intro fun x₁ x₂ =>
  congrArg f (X_sub.allEq x₁ x₂)

theorem to_subsingleton (Y_sub: Subsingleton Y): Constant f := Constant.intro fun x₁ x₂ =>
  Y_sub.allEq (f x₁) (f x₂)

theorem preimage_all_or_empty (f_const: Constant f) (U: Set Y): Set.all_or_empty (Set.preimage f U) := by
  apply Set.of_nonempty_imp_eq_all
  intro ⟨x₁, hx₁⟩
  ext x₂
  simp
  have : f x₁ = f x₂ := f_const.ap_eq_ap x₁ x₂
  rw [← this]
  exact hx₁

theorem of_preimage_all_or_empty (h: ∀U: Set Y, Set.all_or_empty (Set.preimage f U)): Constant f := Constant.intro fun x₁ x₂ => by
  replace h := h {f x₂}
  have : Set.nonempty (Set.preimage f {f x₂}) := by
    exact Set.nonempty_intro (Set.preimage f {f x₂}) rfl
  simp [this, Set.nonempty_imp_all_or_empty_iff_eq_all, Set.ext_iff] at h
  exact h x₁

theorem imp_idem {X: Type u} (f: X → X) (f_const: Constant f): Idempotent f := by
  apply Idempotent.intro
  funext x
  dsimp
  exact f_const.ap_eq_ap (f x) x

theorem left_nullify (g: X → X) (f_const: Constant f): f ∘ g = f := by
  funext x
  exact f_const.ap_eq_ap (g x) x

theorem left_nullify' (g h: Z → X) (f_const: Constant f): f ∘ g = f ∘ h := by
  funext z
  exact f_const.ap_eq_ap (g z) (h z)

theorem of_left_nullify (h: ∀g: X → X, f ∘ g = f): Constant f := by
  apply Constant.intro
  intro x₁ x₂
  exact congrFun (h (fun _ => x₁)) x₂

end Constant
end

theorem injective_constant_imp_subsingleton {f: X → Y} (f_const: Constant f)
(f_inj: Injective f): Subsingleton X := Subsingleton.intro fun x₁ x₂ =>
  f_inj.eq_of_ap_eq x₁ x₂ (f_const.ap_eq_ap x₁ x₂)

theorem surjective_constant_imp_subsingleton {X Y: Type u} {f: X → Y} (f_const: Constant f)
(f_surj: Surjective f): Subsingleton Y := Subsingleton.intro fun y₁ y₂ => by
  induction y₁ using f_surj.ind
  induction y₂ using f_surj.ind
  case k.k x₁ x₂ =>
    exact f_const.ap_eq_ap x₁ x₂

namespace Set

variable {X Y Z} (f: X → Y) (g: Y → Z)

def uniques : Set X := Set.mk fun a => ∀a', f a = f a' → a = a'

@[simp]
theorem uniques_def (a: X) : a ∈ uniques f ↔ ∀a', f a = f a' → a = a' := by rfl

theorem injective_of_uniques_eq_all: uniques f = Set.all → Injective f := by
  intro h
  simp [Set.ext_iff] at h
  exact Injective.intro h

theorem injective_imp_uniques_eq_all : Injective f → uniques f = Set.all := by
  intro ⟨h⟩
  ext x
  simp
  exact h x

theorem uniques_comp_sub: uniques (g ∘ f) ⊆ uniques f := by
  intro x
  simp
  intro hx a' heq
  apply hx
  exact congrArg g heq

theorem preimage_image_uniques : preimage f (image f (uniques f)) = uniques f := by
  ext x
  simp
  constructor
  · intro ⟨x', hx, heq⟩ a' h
    obtain rfl := hx x heq
    obtain rfl := hx a' h
    rfl
  · intro k
    exists x

end Set


theorem full_image_sub_iff_factors_left {A B X: Type u} (f: A → X) (g: B → X):
Set.full_image g ⊆ Set.full_image f ↔ ∃k: B → A, g = f ∘ k where
  mp h := by
    have : ∀b: B, ∃a: A, f a = g b := by
      intro b
      exact @h (g b) (Set.always_in_image g b)
    obtain ⟨k, hk⟩ := Classical.axiomOfChoice this
    clear this
    exists k
    funext x
    exact Eq.symm (hk x)
  mpr := by
    intro ⟨k, heq⟩
    subst heq
    exact @Set.full_image_sub_comp B A k X f

def fun_relation {X : Type u} {Y: Type v} (f: X → Y): Set (X × X) := Set.mk fun ⟨x₁,x₂⟩ => f x₁ = f x₂

@[simp]
theorem fun_relation_def : (x₁, x₂) ∈ fun_relation f ↔ f x₁ = f x₂ := by rfl

theorem inj_iff_fun_relation_eq_diagonal {f: X → Y} : Injective f ↔ fun_relation f = Set.diagonal where
  mp h := by
    simp [Set.ext_iff]
    exact Injective.imp_eq_iff_app_eq h
  mpr h := by
    simp [Set.ext_iff] at h
    exact (Injective.iff_eq_iff_app_eq f).mpr h

theorem fun_relation_sub_comp : fun_relation f ⊆ fun_relation (k ∘ f) := by
  intro ⟨x₁, x₂⟩ hs
  exact congrArg k hs


theorem uniques_sub_iff_factors_right {A B X: Type u} [inst: Nonempty B] (f: X → A) (g: X → B): fun_relation f ⊆ fun_relation g ↔ ∃k: A → B, g = k ∘ f where
  mp h := by
    have : ∀a: A, ∃b: B, ∀x: X, f x = a → g x = b := by
      intro a
      simp [Set.subset_def, fun_relation] at h
      by_cases a ∈ Set.full_image f
      case pos himg =>
        obtain ⟨x, rfl⟩ := himg
        exists g x
        intro x'
        exact h x' x
      case neg h =>
        obtain ⟨b⟩ := inst
        exists b
        intro x hx
        exfalso
        exact h ⟨x, hx⟩
    obtain ⟨k, hk⟩ := Classical.axiomOfChoice this
    clear this
    exists k
    funext x
    exact hk (f x) x rfl
  mpr := by
    intro ⟨k, heq⟩
    subst heq
    exact fun {x} => congrArg k



theorem exists_sum {p: A ⊕ B → Prop}: (∃x: A ⊕ B, p x) ↔ (∃a, p (Sum.inl a)) ∨ (∃b, p (Sum.inr b)) where
  mp := by
    rintro ⟨(a|b), h⟩
    exact Or.inl ⟨a, h⟩
    exact Or.inr ⟨b, h⟩
  mpr := by
    rintro (⟨a, ha⟩ | ⟨b, hb⟩)
    exists Sum.inl a
    exists Sum.inr b


theorem full_image_sum (f: A → X) (g: B → X): Set.full_image (Sum.elim f g) = Set.full_image f ∪ Set.full_image g := by
  ext x
  simp [exists_sum]


theorem fun_relation_prod (f: X → A) (g: X → B): fun_relation (fun x => (f x, g x)) = fun_relation f ∩ fun_relation g := by
  ext ⟨x₁, x₂⟩
  simp

theorem fun_relation_eq_all_iff_constant {f: X → Y}: fun_relation f = Set.all ↔ Constant f where
  mp h := by
    apply Constant.intro
    change ∀x₁ x₂, (x₁, x₂) ∈ fun_relation f
    rw [h]
    exact fun x₁ x₂ => trivial
  mpr h := by
    ext ⟨x₁, x₂⟩
    simp
    exact h.ap_eq_ap x₁ x₂
