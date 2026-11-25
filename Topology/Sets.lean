-- This file contains all definitions about sets


/--
  `A: Set X` represents a subset of the type `X`
-/
structure Set.{u} (X: Type u) where
  elem: X → Prop

namespace Set

variable {X: Type u}

instance : Membership X (Set X) where
  mem := elem

@[simp]
theorem set_mem_def {A: Set X} {x: X}: A.elem x ↔ x ∈ A := by rfl

@[simp]
theorem mem_set {x: X} {f: X → Prop}: x ∈ ({elem := f}: Set X) ↔ f x := by rfl

@[simp]
theorem set_eta {A: Set X} : {elem x := x ∈ A} = A := by rfl

variable (A B C: Set X)

@[ext]
theorem ext (h: ∀x, x ∈ A ↔ x ∈ B): A = B := by
  cases A <;> cases B
  case mk.mk A B =>
  simp_all only [mem_set, mk.injEq]
  funext x
  exact propext (h x)

def subset: Prop := ∀⦃x⦄, x ∈ A → x ∈ B

instance : HasSubset (Set X) where
  Subset := subset

instance : Coe (∀x ∈ A, x ∈ B) (A ⊆ B) where
  coe h := fun {x} => h x

@[simp]
theorem subset_refl : A ⊆ A := by
  intro
  exact id

theorem rfl {A: Set X}: A ⊆ A := subset_refl A

theorem subset_trans: A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h₁ h₂ x hx
  exact  h₂ (h₁ hx)

theorem subset_antisymm : A ⊆ B → B ⊆ A → A = B := by
  intro h₁ h₂
  ext x
  constructor
  intro ha
  exact h₁ ha
  intro hb
  exact h₂ hb

def subset_def {A B: Set X}: A ⊆ B ↔ (∀x ∈ A, x ∈ B) := Iff.rfl

instance : HasSSubset (Set X) where
  SSubset A B := A ⊆ B ∧ ¬A = B

theorem ssubset_def (A B: Set X): A ⊂ B ↔ A ⊆ B ∧ A ≠ B := by
  simp [instHasSSubset, subset_def]

def union := mk fun x => x ∈ A ∨ x ∈ B

instance : Union (Set X) where
  union := union

@[simp]
theorem union_def {A B: Set X} (x: X): x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  simp_all [union, instUnion]

theorem in_union_of_in_left (x: X) : x ∈ A → x ∈ A ∪ B := Or.inl
theorem in_union_of_in_right (x: X) : x ∈ B → x ∈ A ∪ B := Or.inr

def inter := mk fun x => x ∈ A ∧ x ∈ B

instance : Inter (Set X) where
  inter := inter

@[simp]
theorem inter_def {A B: Set X} (x: X): x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := by
  simp_all [inter, instInter]


def all: Set X := mk fun _ => True

@[simp]
theorem all_def (x: X): x ∈ all := trivial


def empty: Set X := mk fun _ => False

@[simp]
theorem empty_def (x: X): ¬x ∈ empty := by
  intro h
  nomatch h

instance : Inhabited (Set X) := ⟨Set.empty⟩

-- I'm honestly not sure which direction of equality would be best
-- (like `x = y` versus `y = x`)
def singleton (x: X) := mk fun y => x = y

instance : Singleton X (Set X) where
  singleton := singleton

@[simp]
instance : EmptyCollection (Set X) where
  emptyCollection := empty

instance : Insert X (Set X) where
  insert x A := {x} ∪ A

@[simp]
theorem mem_singleton (x y: X): x ∈ ({y}: Set X) ↔ x = y := by
  simp [instSingleton]
  exact eq_comm

@[simp]
theorem singleton_sub (x: X): {x} ⊆ A ↔ x ∈ A := by
  simp [Set.subset_def]

@[simp]
theorem singleton_eq_singleton (x: X): singleton x = {x} := Eq.refl _

@[simp]
theorem singleton_neq_empty (x: X): {x} ≠ Set.empty := by
  simp [Set.ext_iff]

@[simp]
theorem singleton_eq_iff_eq (x y: X): {x} = ({y}: Set X) ↔ x = y := by
  simp [Set.ext_iff]
  constructor
  · intro hseq
    exact (hseq x).mp (Eq.refl _)
  · intro heq
    subst heq
    simp

@[simp]
theorem mem_insert (x: X) (S: Set X) : x ∈ Insert.insert y S ↔ x = y ∨ x ∈ S := by
  simp [Insert.insert]

-- @[simp]
-- theorem mem_pair (x y z: X): x ∈ ({y, z}: Set X) ↔ x = y ∨ x = z := by
--   simp

instance : @Trans (Set X) (Set X) (Set X) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans {A B C} := subset_trans A B C

instance : @Trans X (Set X) (Set X) (· ∈ ·) (· ⊆ ·) (· ∈ ·) where
  trans {_ _ _} ha hab := hab ha

instance : @Trans X (Set X) (Set X) (· ∈ ·) (· ⊂ ·) (· ∈ ·) where
  trans {_ _ _} ha hab := hab.left ha

instance : @Trans (Set X) (Set X) (Set X) (· ⊂ ·) (· ⊆ ·) (· ⊂ ·) where
  trans {A B C} := fun ⟨hab, hneq⟩ hbc => ⟨subset_trans A B C hab hbc, by
    intro rfl
    exact hneq (subset_antisymm A B hab hbc)
  ⟩

instance : @Trans (Set X) (Set X) (Set X) (· ⊆ ·) (· ⊂ ·) (· ⊂ ·) where
  trans {A B C} hab := fun ⟨hbc, hneq⟩ => ⟨subset_trans A B C hab hbc, by
    intro rfl
    exact hneq (subset_antisymm B A hbc hab)
  ⟩

instance : @Trans (Set X) (Set X) (Set X) (· ⊂ ·) (· ⊂ ·) (· ⊂ ·) where
  trans {A B C} := fun ⟨hab, hneq₁⟩ ⟨hbc, hneq₂⟩ => ⟨subset_trans A B C hab hbc, by
    intro rfl
    exact hneq₁ (subset_antisymm A B hab hbc)
  ⟩

@[simp]
theorem empty_subset : empty ⊆ A := by
  intro x hx
  nomatch hx


theorem subset_empty : A ⊆ empty → A = empty := by
  intro h
  ext x
  constructor
  exact @h x
  intro h'
  nomatch h'

@[simp]
theorem comprehension_empty_iff {f: X → Prop} : {elem := f} ⊆ empty ↔ ∀x, ¬ f x := by
  simp_all [subset_def]

@[simp]
theorem subset_all : A ⊆ all := by
  intro x hx
  trivial

theorem all_subset : all ⊆ A → A = all := by
  intro h
  ext x
  constructor
  intro _
  trivial
  exact @h x

@[simp]
theorem all_subset_iff : all ⊆ A ↔ A = all where
  mp := all_subset A
  mpr heq := by subst heq; exact subset_refl all


def complement (A: Set X): Set X := mk fun x => ¬ A.elem x

@[simp]
theorem complement_def (x: X): x ∈ A.complement ↔ ¬x ∈ A := Iff.rfl


@[simp]
theorem complement_empty : complement (@empty X) = @all X := by
  ext
  simp

@[simp]
theorem complement_eq_all_iff (U: Set X): complement U = all ↔ U = empty := by simp [Set.ext_iff]

@[simp]
theorem complement_eq_empty_iff (U: Set X): complement U = empty ↔ U = all := by simp [Set.ext_iff]

@[simp]
theorem complement_all : complement (@all X) = @empty X := by
  ext
  simp

@[simp]
theorem complement_complement : complement (complement A) = A := by
  ext
  simp

@[simp]
theorem complement_inj : complement A = complement B ↔ A = B := by
  open Classical in
  simp [Set.ext_iff, Decidable.not_iff_not]

def complement_induction {motive: Set X → Sort v} (hc: ∀S: Set X, motive S.complement) (S: Set X): motive S := by
  have := hc S.complement
  rw [complement_complement] at this
  exact this

@[simp]
theorem complement_eq_iff : complement A = B ↔ A = complement B := by
  induction B using complement_induction <;> simp

@[simp]
theorem complement_union  : complement (A ∪ B) = (complement A) ∩ (complement B) := by
  ext
  simp

@[simp]
theorem complement_union_eq_all : complement A ∪ A = Set.all := by
  ext x
  simp
  exact Or.symm (Classical.em (x ∈ A))

@[simp]
theorem complement_inter : complement (A ∩ B) = (complement A) ∪ (complement B) := by
  ext
  simp only [complement_def, inter_def, union_def]
  exact Classical.not_and_iff_not_or_not

@[simp]
theorem complement_inter_eq_empty : complement A ∩ A = Set.empty := by
  ext x
  simp

@[simp]
theorem complement_subset_complement : complement B ⊆ complement A ↔ A ⊆ B := by
  constructor
  intro h x ha
  replace h := @h x
  simp_all
  intro h x hnb
  replace h := @h x
  simp_all

@[simp]
theorem Bool.complement_singleton_true : ({true}: Set Bool).complement = {false} := by
  ext x
  simp

@[simp]
theorem Bool.complement_singleton_false : ({false}: Set Bool).complement = {true} := by
  ext x
  simp

theorem forall_iff_forall_complement {p: Set X → Prop} : (∀s: Set X, p s) ↔ (∀s: Set X, p (complement s)) where
  mp h s := h s.complement
  mpr h s := by
    suffices p (s.complement.complement) by (simp at this; exact this)
    exact h s.complement

theorem union_comm : A ∪ B = B ∪ A := by
  ext
  exact Or.comm

theorem union_assoc : A ∪ (B ∪ C) = (A ∪ B) ∪ C := by
  ext
  simp [or_assoc]

theorem subset_union_left : A ⊆ A ∪ B := by
  intro x h
  left
  exact h

theorem subset_union_right : B ⊆ A ∪ B := by
  intro x h
  right
  exact h

theorem union_subset : A ⊆ C → B ⊆ C → (A ∪ B) ⊆ C := by
  intro h₁ h₂ x hx
  replace h₁ := @h₁ x
  replace h₂ := @h₂ x
  cases hx <;> simp_all

theorem union_subset_iff : (A ∪ B) ⊆ C ↔ (A ⊆ C ∧ B ⊆ C) := by
  constructor
  · intro h
    constructor
    exact subset_trans _ _ _ (subset_union_left _ _) h
    exact subset_trans _ _ _ (subset_union_right _ _) h

  · intro ⟨h₁, h₂⟩
    exact @union_subset _ _ _ _ h₁ h₂

@[simp]
theorem union_empty : A ∪ empty = A := by
  ext
  simp

@[simp]
theorem empty_union : empty ∪ A = A := by
  ext
  simp

@[simp]
theorem union_all : A ∪ all = all := by
  ext
  simp

@[simp]
theorem all_union : all ∪ A = all := by
  ext
  simp

@[simp]
theorem union_self : A ∪ A = A := by
  apply subset_antisymm
  exact union_subset A A A (Set.subset_refl _) (Set.subset_refl _)
  exact subset_union_right A A

@[simp]
theorem union_self_right : (A ∪ B) ∪ B = A ∪ B := by
  rw [← union_assoc, union_self]

@[simp]
theorem union_eq_iff_subset : A ∪ B = A ↔ B ⊆ A := by
  constructor
  case mp =>
    intro h x hb
    rw [Set.ext_iff] at h
    replace h := (h x).mp
    simp at *
    exact h (Or.inr hb)
  case mpr =>
    intro h
    ext x
    simp
    exact @h x


theorem inter_comm : A ∩ B = B ∩ A := by
  ext x
  exact And.comm

theorem inter_assoc : A ∩ (B ∩ C) = (A ∩ B) ∩ C := by
  ext x
  simp [and_assoc]

theorem inter_subset_left : A ∩ B ⊆ A := by
  intro x h
  simp_all

theorem inter_subset_right : A ∩ B ⊆ B := by
  intro x h
  simp_all

theorem subset_inter : C ⊆ A → C ⊆ B → C ⊆ A ∩ B := by
  intro h₁ h₂ x hc
  replace h₁ := h₁ hc
  replace h₂ := h₂ hc
  exact ⟨h₁, h₂⟩

theorem subset_inter_iff : C ⊆ A ∩ B ↔ (C ⊆ A ∧ C ⊆ B) := by
  constructor
  intro h
  constructor
  exact subset_trans _ _ _ h (inter_subset_left _ _)
  exact subset_trans _ _ _ h (inter_subset_right _ _)
  intro h
  exact subset_inter _ _ _ h.1 h.2

@[simp]
theorem inter_empty : A ∩ empty = empty := by
  ext x
  simp

@[simp]
theorem empty_inter : empty ∩ A = empty := by
  ext x
  simp

@[simp]
theorem inter_all : A ∩ all = A := by
  ext x
  simp

@[simp]
theorem all_inter : all ∩ A = A := by
  ext x
  simp

@[simp]
theorem inter_self : A ∩ A = A := by
  ext x
  simp

@[simp]
theorem inter_self_right : A ∩ B ∩ B = A ∩ B := by
  rw [← inter_assoc, inter_self]

@[simp]
theorem inter_eq_left_iff_subset : A ∩ B = A ↔ A ⊆ B := by
  constructor
  case mp =>
    intro h x hx
    rw [Set.ext_iff] at h
    replace h := (h x).mpr
    simp_all
  case mpr =>
    intro h
    ext x
    simp_all [subset_def]

@[simp]
theorem inter_eq_right_iff_subset : A ∩ B = B ↔ B ⊆ A := by
  constructor
  case mp =>
    intro h x hx
    rw [Set.ext_iff] at h
    replace h := (h x).mpr
    simp_all
  case mpr =>
    intro h
    ext x
    simp_all [subset_def]

theorem inter_union_left : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp
  exact and_or_left

theorem union_inter_right : (B ∪ C) ∩ A = (B ∩ A) ∪ (C ∩ A) := by
  ext x
  simp
  exact or_and_right

theorem union_inter_left : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp
  exact or_and_left

theorem inter_union_right : (B ∩ C) ∪ A = (B ∪ A) ∩ (C ∪ A) := by
  ext x
  simp
  exact and_or_right

theorem inter_sub_union : A ∩ B ⊆ A ∪ B := by
  intro x hx
  left
  exact hx.left

theorem subset_inter_right : A ⊆ B → A ∩ C ⊆ B ∩ C := by
  simp [Set.subset_def]
  intro hx x ha hc
  exact ⟨hx x ha, hc⟩

theorem subset_inter_left : A ⊆ B → C ∩ A ⊆ C ∩ B := by
  simp [Set.subset_def]
  intro hx x ha hc
  exact ⟨ha, hx x hc⟩

instance : Coe (List α) (Set α) where
  coe l := Set.mk (· ∈ l)

def nonempty : Prop := ∃a, a ∈ A

@[simp]
theorem nonempty_intro {x: X} (hx: x ∈ A): nonempty A := Exists.intro x hx

@[simp]
theorem not_nonempty: ¬ @nonempty X empty := by
  rintro ⟨x, hx⟩
  exact hx

@[simp]
theorem nonempty_imp_all_nonempty [inst: Nonempty X]: nonempty (@Set.all X) := by
  obtain ⟨x⟩ := inst
  exists x

@[simp]
theorem not_nonempty_iff_eq_empty : ¬ nonempty A ↔ A = empty where
  mp := by
    intro h
    simp [Set.ext_iff]
    intro x hx
    exact h ⟨x, hx⟩
  mpr := by
    intro rfl
    exact not_nonempty

@[simp]
theorem nonempty_iff_neq_empty: A ≠ empty ↔ nonempty A where
  mp := by
    rintro hneq
    simp only [ne_eq, Set.ext_iff, empty_def, iff_false, Classical.not_forall,
      Classical.not_not] at hneq
    exact hneq
  mpr := by
    rintro ⟨a, ha⟩ heq
    subst heq
    exact ha

theorem singleton_nonempty {a: X} : nonempty {a} := by exists a

instance Nonempty_of_nonempty_set : nonempty A → Nonempty X := Exists.nonempty

theorem union_nonempty_left : nonempty A → nonempty (A ∪ B) := by
  rintro ⟨a, ha⟩
  exists a
  exact Or.inl ha

theorem union_nonempty_right : nonempty B → nonempty (A ∪ B) := by
  rintro ⟨b, hb⟩
  exists b
  exact Or.inr hb

theorem union_nonempty_iff : nonempty (A ∪ B) ↔ (nonempty A ∨ nonempty B) where
  mp := by
    rintro ⟨x, ha | hb⟩
    · left; exists x
    · right; exists x
  mpr := by
    rintro (⟨x, h⟩ | ⟨x, h⟩) <;> exists x
    exact Or.inl h
    exact Or.inr h

theorem inter_nonempty_imp_left : nonempty (A ∩ B) → nonempty A := by
  intro ⟨x, hA, hB⟩
  exists x

theorem inter_nonempty_imp_right : nonempty (A ∩ B) → nonempty B := by
  intro ⟨x, hA, hB⟩
  exists x

@[simp]
theorem inter_singleton_nonempty_iff {a: X} : nonempty (A ∩ {a}) ↔ a ∈ A where
  mp := by
    rintro ⟨x, h₁, heq⟩
    subst heq
    exact h₁
  mpr h := by
    exists a

@[simp]
theorem subset_singleton_iff (x: X): A ⊆ {x} ↔ A = Set.empty ∨ A = {x} where
  mp h := by
    apply Classical.or_iff_not_imp_left.mpr
    simp
    rintro ⟨a, ha⟩
    obtain rfl := h ha
    replace ha : {x} ⊆ A := by exact @Iff.mpr ({x} ⊆ A) (x ∈ A) (singleton_sub A x) ha
    exact subset_antisymm A {x} h ha
  mpr := by
    rintro (rfl | rfl) <;> simp

@[simp]
theorem eq_iff_iff (x: X): A ∩ {x} = B ∩ {x} ↔ (x ∈ A ↔ x ∈ B) where
  mp h := by
    simp_all [Set.ext_iff]
  mpr h := by simp_all [Set.ext_iff]


section
variable {X: Type u} {Y: Type v}  (f: X → Y) (A A₁ A₂: Set X) (B B₁ B₂: Set Y)

def product : Set (X × Y) := Set.mk fun (x,y) => x ∈ A ∧ y ∈ B

@[simp]
theorem product_def (x: X) (y: Y): (x,y) ∈ product A B ↔ x ∈ A ∧ y ∈ B := by
  simp [product]

def fst_tube (S: Set (X × Y)): Set X := Set.mk fun x => ∀y: Y, (x,y) ∈ S

@[simp]
theorem fst_tube_def (S: Set (X × Y)) (x: X): x ∈ fst_tube S ↔ ∀y: Y, (x,y) ∈ S := by
  simp [fst_tube]

def snd_tube (S: Set (X × Y)): Set Y := Set.mk fun y => ∀x: X, (x,y) ∈ S

@[simp]
theorem snd_tube_def (S: Set (X × Y)) (y: Y): y ∈ snd_tube S ↔ ∀x: X, (x,y) ∈ S := by
  simp [snd_tube]

def diagonal: Set (X × X) := Set.mk fun p => p.fst = p.snd

@[simp]
theorem diagonal_def' : (x,y) ∈ diagonal ↔ x = y := Iff.rfl

@[simp]
theorem diagonal_def : p ∈ diagonal ↔ p.fst = p.snd := Iff.rfl

def full_image : Set Y := Set.mk fun y => ∃x : X, f x = y

@[simp]
theorem full_image_def (y: Y): y ∈ full_image f ↔ ∃x : X, f x = y := Iff.rfl

@[simp]
theorem always_in_image : ∀x, f x ∈ full_image f := fun x => ⟨x, Eq.refl _⟩

theorem full_image_ind {motive: (y: Y) → (y ∈ full_image f) → Prop} (h: (x: X) → motive (f x) ⟨x, Eq.refl _⟩) (y: Y) (hy: y ∈ full_image f): motive y hy := by
  rcases hy with ⟨x, rfl⟩
  exact h x

def image : Set Y := Set.mk fun y => ∃x ∈ A, f x = y

@[simp]
theorem image_def (y: Y): y ∈ image f A ↔ ∃x ∈ A, f x = y := Iff.rfl

theorem image_ind {motive : (y: Y) → y ∈ image f A → Prop} (h: (x: X) → (hx: x ∈ A) → motive (f x) ⟨x, hx, Eq.refl _⟩) (y: Y) (hy: y ∈ image f A): motive y hy := by
  rcases hy with ⟨x, hx, rfl⟩
  exact h x hx

@[simp]
theorem image_empty: image f empty = empty := by
  refine subset_empty (image f empty) ?_
  intro x hx
  exact hx.choose_spec.left

@[simp]
theorem image_all : image f all = full_image f := by
  ext x
  simp

theorem image_monotone : A₁ ⊆ A₂ → image f A₁ ⊆ image f A₂ := by
  intro h y ⟨x₁, hx₁, heq⟩
  subst heq
  exists x₁
  exact ⟨h hx₁, Eq.refl _⟩

theorem image_subset_full_image : image f A ⊆ full_image f := by
  intro y ⟨x, hx, heq⟩
  exists x

@[simp]
theorem image_union : image f (A₁ ∪ A₂) = (image f A₁) ∪ (image f A₂) := by
  apply subset_antisymm
  intro y ⟨x, hx, heq⟩
  cases hx
  case a.inl h =>
    left
    exists x
  case a.inr h =>
    right
    exists x
  intro y hy
  rcases hy with ⟨x, hx, heq⟩ | ⟨x, hx, heq⟩ <;> subst heq <;> exists x <;> refine ⟨?_, Eq.refl _⟩
  exact Or.inl hx
  exact Or.inr hx

/--
  This could be non-equal if there's an `x₁ ∈ A₁` and `x₂ ∈ A₁` where `f x₁ = f x₂` but neither
  are in the intersection
-/
@[simp]
theorem image_intersection : image f (A₁ ∩ A₂) ⊆ (image f A₁) ∩ (image f A₂) := by
  intro y ⟨x, ⟨h₁, h₂⟩, heq⟩
  constructor <;> exists x

@[simp]
theorem image_id : image id A = A := by
  ext x
  simp

theorem image_comp {g: Y → Z} : image (g ∘ f) A = image g (image f A) := by
  ext x
  simp
  constructor
  · rintro ⟨a, a_in_A, heq⟩
    subst heq
    exists f a
    simp
    exists a
  · rintro ⟨y, ⟨a, a_in_A, heq₁⟩, heq₂⟩
    subst heq₁ heq₂
    exists a

@[simp]
theorem image_const (A_nonempty: nonempty A) {y: Y}: image (@Function.const Y X y) A = {y} := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    rfl
  · rintro rfl
    obtain ⟨a, ha⟩ := A_nonempty
    exists a

@[simp]
theorem full_image_id : @full_image X X id = Set.all := by
  ext x
  simp

@[simp]
theorem full_image_comp : full_image (g ∘ f) = image g (full_image f) := by
  ext x
  simp [← exists_and_right]
  constructor
  · intro ⟨z, heq⟩
    exists f z, z
  · intro ⟨z, y, heq₁, heq₂⟩
    exists y
    exact Eq.trans (congrArg g heq₁) heq₂


theorem full_image_sub_comp : full_image (g ∘ f) ⊆ full_image g := by
  intro x ⟨y, heq⟩
  subst heq
  exists f y

@[simp]
theorem full_image_const [inst: Nonempty X] (y: Y) : full_image (@Function.const Y X y) = {y} := by
  rw [← image_all]
  replace inst : Set.nonempty (@all X) := nonempty_imp_all_nonempty
  exact image_const all inst

theorem diagonal_eq_full_image : @diagonal X = full_image fun (x: X) => (x,x) := by
  ext ⟨x,y⟩
  simp

@[simp]
theorem nonempty_image_iff_nonempty : nonempty (image f A) ↔ nonempty A where
  mp := by
    intro ⟨y, x, hx, heq⟩
    exact ⟨x, hx⟩
  mpr := by
    rintro ⟨x, hx⟩
    exists f x, x

def preimage : Set X := Set.mk fun x => f x ∈ B

@[simp]
theorem preimage_def {B: Set Y} (x: X): x ∈ preimage f B ↔ f x ∈ B := Iff.rfl

@[simp]
theorem preimage_empty : preimage f empty = empty := by
  ext x
  simp

@[simp]
theorem preimage_all : preimage f all = all := by
  ext x
  simp

@[simp]
theorem preimage_id {U: Set X} : preimage id U = U := by
  ext x
  simp

@[simp]
theorem preimage_comp (f: X → Y) (g: Y → Z) {U: Set Z} : preimage (g ∘ f) U = preimage f (preimage g U) := by
  ext x
  simp

theorem preimage_monotone : B₁ ⊆ B₂ → preimage f B₁ ⊆ preimage f B₂ := by
  intro h x hx
  exact h hx

@[simp]
theorem image_sub_iff_sub_preimage : image f A ⊆ B ↔ A ⊆ preimage f B where
  mp h := by
    intro x hx
    exact h ⟨x, hx, Eq.refl _⟩
  mpr h := by
    rintro fx ⟨x, hx, rfl⟩
    exact h hx

theorem preimage_sub_preimage_iff : preimage f B₁ ⊆ preimage f B₂ ↔ B₁ ∩ Set.full_image f ⊆ B₂ where
  mp := by
    simp [Set.subset_def]
    intro h y hy x rfl
    exact h x hy
  mpr := by
    intro h
    intro x hx
    exact h ⟨hx, x, Eq.refl _⟩

@[simp]
theorem preimage_union : preimage f (B₁ ∪ B₂) = preimage f B₁ ∪ preimage f B₂ := by
  ext x
  simp

@[simp]
theorem preimage_inter : preimage f (B₁ ∩ B₂) = preimage f B₁ ∩ preimage f B₂ := by
  ext x
  simp

@[simp]
theorem complement_preimage : complement (preimage f B) = preimage f (complement B)  := by
  ext x
  simp

@[simp]
theorem preimage_full_image : preimage f (full_image f) = all := by
  ext x
  simp

@[simp]
theorem preimage_eq_all_iff : preimage f B = all ↔ full_image f ⊆ B := by
  simp [Set.ext_iff, Set.subset_def]

@[simp]
theorem preimage_eq_empty_iff : preimage f B = empty ↔ full_image f ∩ B = empty := by
  simp [Set.ext_iff]

theorem preimage_eq_preimage_iff : preimage f B₁ = preimage f B₂ ↔ B₁ ∩ full_image f = B₂ ∩ full_image f := by
  simp [Set.ext_iff]

theorem nonempty_preimage_imp_nonempty : nonempty (preimage f B) → nonempty B := by
  intro ⟨x, hx⟩
  exists f x


theorem nonempty_preimage_iff : nonempty (preimage f B) ↔ nonempty (B ∩ full_image f) where
  mp h := by
    apply nonempty_preimage_imp_nonempty f
    simp [h]
  mpr h := by
    obtain ⟨y, hx, x, rfl⟩ := h
    exists x

theorem image_preimage_eq_inter_full_image : image f (preimage f B) = B ∩ full_image f := by
  ext x
  simp
  constructor
  · rintro ⟨x', hx, rfl⟩
    simp [hx]
  · intro ⟨hx, x', heq⟩
    subst heq
    exists x'

theorem sub_preimage_image : A ⊆ preimage f (image f A) := by
  intro a ha
  exists a

end

section

def power_set (A: Set X): Set (Set X) := Set.mk fun B => B ⊆ A

@[simp]
theorem power_set_def : B ∈ power_set A ↔ B ⊆ A := by rfl

@[simp]
theorem power_set_inter : power_set (A ∩ B) = power_set A ∩ power_set B := by
  ext C
  simp
  exact subset_inter_iff A B C

theorem power_set_monotone : A ⊆ B → power_set A ⊆ power_set B := by
  simp [subset_def]
  intro h C i x x_in_C
  apply h
  apply i x x_in_C

@[simp]
theorem power_set_sub_iff : power_set A ⊆ power_set B ↔ A ⊆ B where
  mp := by
    intro h a ha
    exact @h A (subset_refl _) a ha
  mpr := power_set_monotone A B

@[simp]
theorem powerset_nonempty : nonempty (power_set A) := ⟨empty, empty_subset _⟩

@[simp]
theorem powerset_empty : (@power_set X) Set.empty = {Set.empty} := by
  ext s
  simp
  constructor
  · exact subset_empty s
  · exact fun (Eq.refl _) => Set.subset_refl _

@[simp]
theorem powerset_singleton (x: X): (@power_set X) {x} = {Set.empty, {x}} := by
  ext s
  simp

end


section

variable (F F₁ F₂: Set (Set X))

def set_union: Set X := Set.mk fun x => ∃s ∈ F, x ∈ s

@[simp]
theorem set_union_def (x: X) : x ∈ set_union F ↔ ∃s ∈ F, x ∈ s := by rfl

@[simp]
theorem set_union_empty : @set_union X empty = empty := by
  ext x
  simp

@[simp]
theorem set_union_all : @set_union X all = all := by
  ext x
  simp
  exists Set.all

theorem set_union_eq_all_of_all_in (hall: all ∈ F): set_union F = all := by
  ext x
  simp
  exists all

@[simp]
theorem set_union_union : set_union (F₁ ∪ F₂) = set_union F₁ ∪ set_union F₂ := by
  ext x
  simp [exists_or, or_and_right]

theorem set_union_inter : set_union (F₁ ∩ F₂) ⊆ set_union F₁ ∩ set_union F₂ := by
  intro x ⟨s, ⟨h₁, h₂⟩, hs⟩
  constructor <;> exists s

/--
  This is the monad associativity property for the direct image monad
-/
@[simp]
theorem set_union_image_set_union_eq_set_union_set_union (FF: Set (Set (Set X))):
  set_union (image set_union FF) = set_union (set_union FF) := by
  ext x
  simp
  constructor
  · intro ⟨s, ⟨F, hF, heq⟩, hxs⟩
    subst heq
    obtain ⟨s', h₁, h₂⟩ := hxs
    exists s'
    constructor
    exists F
    assumption
  · intro ⟨s, ⟨F, h₁, h₂⟩, hxs⟩
    exists set_union F
    constructor
    exists F
    exists s

@[simp]
theorem set_union_image_singletons : set_union (image (fun x => {x}) A) = A := by
  ext x
  constructor
  · intro ⟨s, ⟨a, ha, heq⟩, hxs⟩
    subst heq hxs
    exact ha
  · intro hx
    exists {x}
    constructor
    exists x
    rfl


@[simp]
theorem set_union_image_singletons' : set_union (image singleton A) = A := by
  ext x
  constructor
  · intro ⟨s, ⟨a, ha, heq⟩, hxs⟩
    subst heq hxs
    exact ha
  · intro hx
    exists {x}
    constructor
    exists x
    rfl


def set_inter : Set X := Set.mk fun x => ∀s ∈ F, x ∈ s

@[simp]
theorem set_inter_def (x: X) : x ∈ set_inter F ↔ ∀s ∈ F, x ∈ s := by simp [set_inter]

@[simp]
theorem set_inter_empty : @set_inter X empty = all := by
  ext x
  simp

@[simp]
theorem set_inter_all : @set_inter X all = empty := by
  ext x
  simp
  exists empty
  exact empty_def x

theorem set_inter_eq_empty_of_empty_in (hempty: empty ∈ F): set_inter F = empty := by
  ext x
  simp
  exists empty
  simp [hempty]

@[simp]
theorem set_inter_union : set_inter (F₁ ∪ F₂) = set_inter F₁ ∩ set_inter F₂ := by
  ext x
  constructor
  · intro h
    constructor <;> intro s hs <;> apply h
    exact in_union_of_in_left F₁ F₂ s hs
    exact in_union_of_in_right F₁ F₂ s hs
  · intro ⟨h₁, h₂⟩ s
    exact fun o => Or.elim o (h₁ s) (h₂ s)




theorem complement_set_union : complement (set_union F) = set_inter (image complement F) := by
  ext x
  simp [-complement_eq_iff]

theorem complement_set_inter : complement (set_inter F) = set_union (image complement F) := by
  ext x
  constructor
  · intro h
    simp at h
    obtain ⟨s, hs, hs'⟩ := h
    exists s.complement
    simp [hs, hs']
  · intro ⟨s', ⟨s, hs, heq⟩, hs'⟩
    subst heq
    simp
    exists s

theorem set_inter_sub_set_union (F_nonempty: nonempty F) : set_inter F ⊆ set_union F := by
  intro x hx
  obtain ⟨s, hs⟩ := F_nonempty
  exists s
  exact ⟨hs, hx s hs⟩

@[simp]
theorem set_union_power_set : set_union (power_set A) = A := by
  ext x
  simp
  constructor
  · intro ⟨s, h₁, h₂⟩
    exact h₁ h₂
  · intro hx
    exists {x}
    constructor
    · exact @Iff.mpr ({x} ⊆ A) (x ∈ A) (singleton_sub A x) hx
    · rfl

@[simp]
theorem set_inter_power_set : set_inter (power_set A) = Set.empty := by
  ext x
  simp
  exists Set.empty
  simp

end

instance : Monad Set where
  pure := fun x => {x}
  bind s f := Set.set_union (Set.image f s)

@[simp]
theorem pure_def {x: X}: (Pure.pure x: Set X) = {x} := by rfl

@[simp]
theorem bind_def : (Bind.bind s f) = Set.set_union (Set.image f s) := by rfl

@[simp]
theorem map_def : (Functor.map: (X → Y) → Set X → Set Y) = Set.image := by
  simp [instMonad, image_comp]


instance : LawfulMonad Set := LawfulMonad.mk' Set (
  id_map := by simp
) (
  pure_bind := by
    intro α β a f
    ext b
    simp
) (
  bind_assoc := by
    intro α β γ as f g
    ext c
    simp
    constructor
    intro ⟨s, ⟨b, ⟨bs, ⟨a, ha, heq₂⟩, bbs⟩, heq₁⟩, hcs⟩
    subst heq₁ heq₂
    exists set_union (image g (f a))
    constructor
    · exists a
    · exists g b
      constructor
      exists b
      assumption

    intro ⟨s, ⟨a, ha, heq⟩, hcs⟩
    subst heq
    obtain ⟨k, ⟨b, hb, heq⟩, hck⟩ := hcs
    subst heq
    exists g b
    constructor
    exists b
    constructor
    exists f a
    constructor
    exists a
    all_goals trivial
)

section

inductive all_or_empty {X: Type u}: Set X → Prop where
  | all: all_or_empty all
  | empty: all_or_empty empty

@[simp]
theorem all_all_or_empty: @all_or_empty X all := all_or_empty.all

@[simp]
theorem empty_all_or_empty: @all_or_empty X empty := all_or_empty.empty

theorem all_or_empty_of_eq_all : A = Set.all → all_or_empty A := by
  intro rfl
  exact all_all_or_empty

theorem all_or_empty_of_eq_empty : A = Set.empty → all_or_empty A := by
  intro rfl
  exact empty_all_or_empty

theorem of_nonempty_imp_eq_all : (A.nonempty → A = Set.all) → all_or_empty A := by
  intro h
  by_cases nonempty A
  case pos h' =>
    exact all_or_empty_of_eq_all A (h h')
  case neg h' =>
    simp at h'
    subst h'
    exact all_or_empty.empty

@[simp]
theorem nonempty_imp_all_or_empty_iff_eq_all (A_nonempty: nonempty A): all_or_empty A ↔ A = Set.all where
  mp aoe := by
    induction aoe
    case all => rfl
    case empty =>
      exfalso
      revert A_nonempty
      exact not_nonempty
  mpr := by
    intro rfl
    exact all_all_or_empty


theorem inter_all_or_empty (A_aoe: all_or_empty A) (B_aoe: all_or_empty B): all_or_empty (A ∩ B) := by
  induction A_aoe <;>
  induction B_aoe <;>
  simp

theorem union_all_or_empty (A_aoe: all_or_empty A) (B_aoe: all_or_empty B): all_or_empty (A ∪ B) := by
  induction A_aoe <;>
  induction B_aoe <;>
  simp

theorem complement_all_or_empty (A_aoe: all_or_empty A): all_or_empty A.complement := by
  induction A_aoe <;>
  simp

@[simp]
theorem all_or_empty_complement_iff : all_or_empty A.complement ↔ all_or_empty A := by
  constructor
  · intro h
    generalize heq: A.complement = A' at h
    induction h <;>
    simp_all
  · intro h
    induction h <;> simp


@[simp]
theorem subsingleton_all_or_empty [h: Subsingleton X] (A: Set X): all_or_empty A := by
  by_cases nonempty A
  case pos a =>
    apply all_or_empty_of_eq_all
    simp [Set.ext_iff]
    intro x
    rcases a with ⟨x', hx'⟩
    have := h.elim x x'
    subst this
    exact hx'
  case neg a =>
    simp at a
    subst a
    exact all_or_empty.empty

def subsingleton_set_ind [h: Subsingleton X] {motive: Set X → Prop} (a: motive Set.all)
  (e: motive Set.empty) (A: Set X): motive A := by
  have := subsingleton_all_or_empty A
  induction this <;> assumption

theorem all_all_or_empty_iff_subsingleton: (∀S, @all_or_empty X S) ↔ Subsingleton X where
  mp h := by
    apply Subsingleton.intro
    intro a b
    have h₁ := h {b}
    simp [Set.ext_iff] at h₁
    exact h₁ a
  mpr h := subsingleton_all_or_empty



theorem not_all_or_empty_imp_nonempty : ¬ all_or_empty A → nonempty A := by
  intro h
  apply Classical.byContradiction
  intro h_mt
  simp at h_mt
  subst h_mt
  exact h empty_all_or_empty

@[simp]
theorem eq_all_or_eq_empty_iff_all_or_empty: (A = all ∨ A = empty) ↔ all_or_empty A where
  mp := by
    rintro (rfl | rfl)
    exact all_all_or_empty
    exact all_or_empty.empty
  mpr := by
    intro aoe
    induction aoe
    exact Or.inl (Eq.refl _)
    exact Or.inr (Eq.refl _)

@[simp]
theorem eq_empty_or_eq_all_iff_all_or_empty : (A = empty ∨ A = all) ↔ all_or_empty A := by
  rw [Or.comm]
  exact eq_all_or_eq_empty_iff_all_or_empty A

end


/--
  For any monotonic function `φ: Set X → Set X`, there must exist some fixed point where
  `φ A = A`
-/
theorem exists_fixed_point (φ: Set X → Set X) (mono: ∀S₁ S₂, S₁ ⊆ S₂ → φ S₁ ⊆ φ S₂): ∃A, φ A = A := by
  let A := Set.mk fun a => ∀S, φ S ⊆ S → a ∈ S -- `A` is the intersection of all sets which are contracted by `φ`
  have φA_sub: φ A ⊆ A := by
    intro x hx S φS_sub
    apply φS_sub
    apply mono A
    intro a a_in_A
    exact a_in_A S φS_sub
    exact hx
  exists A
  apply Set.subset_antisymm
  exact φA_sub
  intro a a_in_A
  exact a_in_A (φ A) (mono _ _ φA_sub)






end Set

/--
  `DecidableMem` is the typeclass of sets for which membership is decidable.
-/
abbrev DecidableMem {X: Type u} (A: Set X) := ∀x: X, Decidable (x ∈ A)

instance {X Y} {A: Set Y} {f: X → Y} [inst: DecidableMem A]: DecidableMem (Set.preimage f A) := by
  intro i
  exact inst (f i)

instance {X} {A B: Set X} [DecidableMem A] [DecidableMem B]: DecidableMem (A ∩ B) := by
  intro i
  exact instDecidableAnd

instance {X} {A B: Set X} [DecidableMem A] [DecidableMem B]: DecidableMem (A ∪ B) := by
  intro i
  exact instDecidableOr

instance {X} : @DecidableMem X Set.empty := fun _ => Decidable.isFalse id
instance {X} : @DecidableMem X Set.all := fun _ => Decidable.isTrue trivial

instance [DecidableMem A]: DecidableMem A.complement := by
  intro i
  exact instDecidableNot

instance {X} {x: X} [inst: ∀i, Decidable (x = i)] : @DecidableMem X {x} := inst

instance {X} {x: X} [inst: ∀i, Decidable (i = x)] : @DecidableMem X {x} := fun i =>
  let inst': ∀i, Decidable (x = i) := fun i => propext Eq.comm ▸ inst i
  inst' i

instance {X} {A: Set X} {x: X} [DecidableEq X] [inst: DecidableMem A]: DecidableMem (Insert.insert x A) := by
  intro i
  simp [Set.instInsert]
  exact instDecidableOr

instance : @DecidableMem X {} := fun _ => Decidable.isFalse id
