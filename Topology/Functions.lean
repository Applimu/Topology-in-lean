
import Topology.Sets



instance {X: Type u} : Nonempty (X → X) := ⟨id⟩

instance {A B} [inst: Nonempty A]: Nonempty (B → A) := by
  obtain ⟨a⟩ := inst
  exact Nonempty.intro fun _ => a

instance {A B} (inst: B → False): Nonempty (B → A) := by
  exact Nonempty.intro fun b => False.elim (inst b)

def nonempty_comp {X: Type u} {Y: Type v} {Z: Type w} [inst₁: Nonempty (X → Y)] [inst₂: Nonempty (Y → Z)]: Nonempty (X → Z) := by
  obtain ⟨fi⟩ := inst₁
  obtain ⟨gi⟩ := inst₂
  exact Nonempty.intro (gi ∘ fi)

noncomputable def inv {A: Type u} {B: Type v} (f: A → B) [inst: Nonempty (B → A)] (b: B): A :=
  open Classical in
  if h: b ∈ Set.full_image f then
    Exists.choose h
  else
    Classical.choice inst b

def IsPseudoInverse {A: Type u} {B: Type v} (f: A → B) (g: B → A): Prop := f ∘ g ∘ f = f

@[simp]
theorem inv_id {A: Type u} : inv (@id A) = id := by
  funext a
  dsimp [inv]
  have h : a ∈ Set.full_image id := ⟨a, rfl⟩
  rw [dif_pos h]
  exact h.choose_spec

@[simp]
theorem self_inv_self {X: Type u} {Y: Type v} (f: X → Y) [Nonempty (Y → X)]: f ∘ inv f ∘ f = f := by
  funext x
  unfold inv
  dsimp
  have : f x ∈ Set.full_image f := ⟨x, rfl⟩
  rw [dif_pos this]
  exact this.choose_spec

theorem exists_self_inv_self {X: Type u} {Y: Type v} (f: X → Y) [Nonempty (Y → X)]: ∃g, f ∘ g ∘ f = f := by
  exists inv f
  exact self_inv_self f

theorem exists_pseudoinverse {A: Type u} {B: Type v} (f: A → B) [inst: Nonempty (B → A)] : ∃g, IsPseudoInverse f g := exists_self_inv_self f


theorem exists_inv_self_inv {X: Type u} {Y: Type v} (f: X → Y) [Nonempty (Y → X)]: ∃g, g ∘ f ∘ g = g := by
  exists inv f ∘ f ∘ inv f
  change inv f ∘ ((f ∘ inv f ∘ f) ∘ inv f ∘ f) ∘ inv f = _
  simp only [self_inv_self]

theorem Nat.repeat_succ_eq_comp_right {X: Type u} (f: X → X) (n: Nat) : Nat.repeat f (n + 1) = Nat.repeat f n ∘ f := by
  funext x
  induction n
  case zero => rfl
  case succ n' ih =>
    simp_all [Nat.repeat]

theorem Nat.repeat_succ_eq_comp_left {X: Type u} (f: X → X) (n: Nat) : Nat.repeat f (n + 1) = f ∘ Nat.repeat f n := by
  funext x
  rfl

structure Injective {A: Type u} {B: Type v} (f: A → B): Prop where intro ::
  eq_of_ap_eq (a₁ a₂: A): f a₁ = f a₂ → a₁ = a₂

namespace Injective

variable {A: Type u} {B: Type v} {C: Type w} (f: A → B) (g: B → C)

@[simp]
theorem imp_eq_iff_app_eq {f: A → B} (f_inj: Injective f) (a₁ a₂): f a₁ = f a₂ ↔ a₁ = a₂ where
  mp := f_inj.eq_of_ap_eq a₁ a₂
  mpr := congrArg f

theorem iff_eq_iff_app_eq : Injective f ↔ ∀a₁ a₂, f a₁ = f a₂ ↔ a₁ = a₂ where
  mp h := h.imp_eq_iff_app_eq
  mpr h := Injective.intro fun a₁ a₂ => (h a₁ a₂).mp


theorem id_inj: Injective (@id A) where
  eq_of_ap_eq a b heq := by
    exact heq

theorem comp_inj (f_inj: Injective f) (g_inj: Injective g): Injective (g ∘ f) := by
  apply Injective.intro
  intro a₁ a₂ heq
  repeat rw [Function.comp_apply] at heq
  rw [g_inj.imp_eq_iff_app_eq (f a₁) (f a₂), f_inj.imp_eq_iff_app_eq a₁ a₂] at heq
  exact heq

theorem repeat_inj {e: A → A} (e_inj: Injective e) (n: Nat): Injective (Nat.repeat e n) := by
  induction n
  case zero => exact id_inj
  case succ n' ih =>
    rw [Nat.repeat_succ_eq_comp_left]
    exact comp_inj (Nat.repeat e n') e ih e_inj

theorem not_nonempty_fun_iff: ¬ (Nonempty (B → A)) ↔ Nonempty B ∧ ¬Nonempty A := by
  constructor
  · rintro f
    constructor
    · apply Classical.byContradiction
      intro h
      apply f
      apply Nonempty.intro fun b => ?_
      exact False.elim (h ⟨b⟩)
    · intro ha
      apply f
      apply Nonempty.intro fun b => ?_
      exact Classical.ofNonempty
  · rintro ⟨ha, hb⟩ h
    apply hb
    apply Nonempty.intro
    exact Classical.choice h (Classical.choice ha)

theorem nonempty_iff : Nonempty X → False ↔ (X → False) := by
  constructor
  · intro not_nonempty x
    exact not_nonempty ⟨x⟩
  · intro not_X ⟨x⟩
    exact not_X x

#print axioms nonempty_iff

theorem exists_left_inv [inst: Nonempty (B → A)] (f_inj: Injective f): ∃r: B → A, r ∘ f = id := by
  exists fun b => by
    by_cases b ∈ Set.full_image f
    case pos h => exact h.choose
    case neg =>
      exact Classical.choice inst b
  funext x
  dsimp
  have := Set.always_in_image f x
  rw [dif_pos this]
  apply f_inj.eq_of_ap_eq
  exact this.choose_spec

theorem of_exists_left_inv {f: A → B} (r: B → A) (k: r ∘ f = id): Injective f where
  eq_of_ap_eq a₁ a₂ heq := by
    rw [← id_eq a₁, ← id_eq a₂, ← k, Function.comp_apply, Function.comp_apply, heq]

theorem of_inv_left_inv {f: A → B} [Nonempty (B → A)] (h_inv: inv f ∘ f = id): Injective f where
  eq_of_ap_eq a₁ a₂ heq := by
    replace heq : (inv f ∘ f) a₁ = (inv f ∘ f) a₂ := congrArg (inv f) heq
    rw [h_inv] at heq
    exact heq

theorem left_cancellative (f_inj: Injective f) (h₁ h₂: C → A) (heq: f ∘ h₁ = f ∘ h₂): h₁ = h₂ := by
  funext x
  apply f_inj.eq_of_ap_eq
  change (f ∘ h₁) x = (f ∘ h₂) x
  exact congrFun heq x

@[simp]
theorem left_cancellative_iff (f_inj: Injective f) (h₁ h₂: C → A): f ∘ h₁ = f ∘ h₂ ↔ h₁ = h₂ where
  mp := left_cancellative f f_inj h₁ h₂
  mpr := by
    intro rfl
    rfl

theorem inj_imp_left_composition_inj (f_inj: Injective f): Injective (fun h: C → A => f ∘ h) := by
  apply Injective.intro
  exact left_cancellative f f_inj

@[simp]
theorem inv_left_inv {A B: Type u} {f: A → B} (f_inj: Injective f) [inst: Nonempty (B → A)] : inv f ∘ f = id := by
  apply left_cancellative f f_inj
  exact self_inv_self f

theorem vacuous (h_empty: A → False): Injective f := by
  apply Injective.intro
  intro a
  exact False.elim (h_empty a)

--- This theorem is somewhat useless as `vacuous` would almost always be more direct, though
--- it is an interesting dual to `Surjective.of_full_image_eq_all`
theorem of_full_image_eq_empty : Set.full_image f = Set.empty → Injective f := by
  intro heq
  apply vacuous
  intro a
  have := Set.always_in_image f a
  rw [heq] at this
  exact this

theorem option_map_inj_of_inj (f_inj: Injective f): Injective (Option.map f) where
  eq_of_ap_eq a₁ a₂ heq := by
    cases a₁ <;> cases a₂ <;> simp_all

theorem comp_inj_imp_right_inj (gof_inj: Injective (g ∘ f)) : Injective f where
  eq_of_ap_eq a₁ a₂ heq := by
    have : (g ∘ f) a₁ = (g ∘ f) a₂ := congrArg g heq
    exact gof_inj.eq_of_ap_eq a₁ a₂ this

theorem map_inj_of_inj {α β: Type} {F: Type → Type} [Functor F] [LawfulFunctor F]
  (f: α → β) (f_inj: Injective f) [Nonempty (β → α)]: Injective (Functor.map f: F α → F β) := by
  obtain ⟨h, hh⟩ := f_inj.exists_left_inv
  apply of_exists_left_inv (Functor.map h)
  funext x
  dsimp
  rw [← LawfulFunctor.comp_map, hh, LawfulFunctor.id_map]

#print axioms map_inj_of_inj
end Injective



inductive What (T: Type) where
  | nmt (hT: Nonempty T) (d: Option T): What T
  | mt (hT: ¬Nonempty T) (b: Bool): What T


noncomputable def What.map (f: α → β): What α → What β
  | What.nmt hα d => What.nmt (by
      obtain ⟨a⟩ := hα
      exact ⟨f a⟩
    ) (Option.map f d)
  | What.mt hα b => open Classical in
    if hβ: Nonempty β then
      What.nmt hβ none
    else
      What.mt hβ b


noncomputable instance : Functor What where
  map := What.map

instance: LawfulFunctor What where
  id_map := by
    intro α x
    cases x
    case nmt hα d =>
      simp [Functor.map, What.map]
    case mt hα b =>
      simp [Functor.map, What.map, hα]
  comp_map := by
    intro α β γ g h x
    cases x
    case nmt hα d =>
      simp [Functor.map, What.map]
    case mt hα b =>
      simp [Functor.map, What.map]
      split <;> split <;> simp_all
      case h_1 hγ xβ hβ dβ heq =>
        subst heq
        rfl
      case h_1 hγ xβ hβ dβ heq =>
        subst heq
        apply hγ
        obtain ⟨b⟩ := hβ
        exact ⟨h b⟩
  map_const := by
    intro α β
    funext x
    simp [Functor.map, Functor.mapConst]

theorem mt_to_unit_inj : Injective (Empty.elim : Empty → Unit) := by
  constructor
  exact Empty.rec

theorem What.map_mt_to_unit_not_inj : ¬ Injective (What.map Empty.elim: What Empty → What Unit) := by
  intro ⟨h⟩
  have : ¬Nonempty Empty := by
    intro ⟨e⟩
    exact Empty.elim e
  specialize h (What.mt this true) (What.mt this false)
  have : Nonempty Unit := ⟨()⟩
  simp [What.map, this] at h


structure Surjective {A: Type u} {B: Type v} (f: A → B): Prop where intro ::
  exists_ap_eq (b: B): ∃a: A, f a = b


namespace Surjective

variable {A: Type u} {B: Type v} {C: Type w} (f: A → B) (g: B → C)

theorem id_surj : Surjective (@id A) where
  exists_ap_eq x := ⟨x, rfl⟩

theorem comp_surj (f_surj: Surjective f) (g_surj: Surjective g): Surjective (g ∘ f) where
  exists_ap_eq c := by
    obtain ⟨b, hb⟩ := g_surj.exists_ap_eq c
    obtain ⟨a, ha⟩ := f_surj.exists_ap_eq b
    exists a
    rw [Function.comp_apply, ha, hb]

theorem exists_right_inv (f_surj: Surjective f): ∃h: B → A, f ∘ h = id := by
  replace f_surj := f_surj.exists_ap_eq
  exists fun b => (f_surj b).choose
  funext b
  simp only [Function.comp_apply, (f_surj b).choose_spec, id_eq]

theorem of_exists_right_inv {f: A → B} (h: B → A) (k: f ∘ h = id): Surjective f where
  exists_ap_eq b := by
    exists h b
    rw [← @Function.comp_apply _ _ _ f h, k, id_eq]

theorem of_inv_right_inv {f: A → B} [Nonempty (B → A)] (h_inv: f ∘ inv f = id): Surjective f where
  exists_ap_eq b := by
    exists inv f b
    change (f ∘ inv f) b = b
    rw [h_inv]
    rfl


theorem surj_exists {p: B → Prop} (f_surj: Surjective f): (∃b, p b) ↔ ∃a, p (f a) where
  mp h := by
    obtain ⟨b, pb⟩ := h
    obtain ⟨a, ha⟩ := f_surj.exists_ap_eq b
    subst ha
    exists a
  mpr h := by
    obtain ⟨a, pfa⟩ := h
    exists f a

theorem nonempty_of_surj_nonempty  (f_surj: Surjective f) [inst: Nonempty B]: Nonempty A := by
  obtain ⟨b⟩ := inst
  exact Exists.nonempty $ f_surj.exists_ap_eq b

instance imp_nonempty_inv {A: Type u} {B : Type v} {f: A → B} (f_surj: Surjective f): Nonempty (B → A) := Nonempty.intro fun b => (f_surj.exists_ap_eq b).choose

theorem right_cancellative (f_surj: Surjective f) (h₁ h₂: B → C) (heq: h₁ ∘ f = h₂ ∘ f): h₁ = h₂ := by
  funext b
  obtain ⟨a, ha⟩ := f_surj.exists_ap_eq b
  subst ha
  change (h₁ ∘ f) a = (h₂ ∘ f) a
  exact congrFun heq a

@[simp]
theorem right_cancellative_iff (f: A → B) (f_surj: Surjective f) (h₁ h₂: B → C): h₁ ∘ f = h₂ ∘ f ↔ h₁ = h₂ where
  mp := right_cancellative f f_surj h₁ h₂
  mpr := by
    intro rfl
    rfl

theorem right_composition_injective (f_surj: Surjective f): Injective (fun h: B → C => h ∘ f) := by
  apply Injective.intro
  exact right_cancellative f f_surj

@[simp]
theorem inv_right_inv {f: A → B} (f_surj: Surjective f): f ∘ @inv _ _ f (Surjective.imp_nonempty_inv f_surj) = id := by
  apply right_cancellative f f_surj
  have : Nonempty (B → A) := imp_nonempty_inv f_surj
  change (f ∘ inv f ∘ f) = f
  exact @self_inv_self _ _ f this

noncomputable def ind {motive: B → Sort} {f: A → B} (f_surj: Surjective f) (k: (a: A) → motive (f a)) (b: B): motive b := by
  obtain ⟨a, ha⟩ := f_surj.exists_ap_eq b
  subst ha
  exact k a

theorem surj_ind_comp {C: B → Sort} {k: (a: A) → C (f a)} (f_surj: Surjective f) : ∀a, ind f_surj k (f a) = k a := by
  intro x
  simp

theorem of_full_image_eq_all: Set.full_image f = Set.all → Surjective f := by
  intro heq
  simp [Set.ext_iff, Set.full_image_def] at heq
  exact Surjective.intro heq

@[simp]
theorem imp_full_image_eq_all (f_surj : Surjective f): Set.full_image f = Set.all := by
  ext x
  simp
  exact f_surj.exists_ap_eq x

theorem all_in_full_image (f_surj: Surjective f): ∀x, x ∈ Set.full_image f := f_surj.exists_ap_eq

theorem full_image_comp (f_surj: Surjective f) : Set.full_image (g ∘ f) = Set.full_image g := by
  ext x
  simp
  constructor
  · intro ⟨b, ⟨c, heq₂⟩, heq₁⟩
    subst heq₁ heq₂
    exists f c
  · intro ⟨b, heq⟩
    subst heq
    exists b
    exact ⟨f_surj.exists_ap_eq b, rfl⟩



theorem not_surj_iff_exists_hole : ¬ Surjective f ↔ ∃hole, ∀x, f x ≠ hole where
  mp := by
    intro not_surj
    apply Classical.byContradiction
    intro h'
    apply not_surj
    apply Surjective.intro
    simp at h'
    exact h'
  mpr := by
    rintro ⟨hole, h_hole⟩ surj
    induction hole using ind surj
    case k a => exact h_hole a rfl

theorem of_right_cancellative (c_not_subsingleton: ¬Subsingleton C) (right_cancellative: ∀h₁ h₂: B → C, h₁ ∘ f = h₂ ∘ f → h₁ = h₂): Surjective f := by
  open Classical in
  apply byContradiction
  intro f_nsurj
  rw [not_surj_iff_exists_hole] at f_nsurj
  obtain ⟨hole, h_hole⟩ := f_nsurj
  apply c_not_subsingleton
  apply Subsingleton.intro
  intro c₁ c₂
  have h := right_cancellative (fun _ => c₁) (fun r => if r = hole then c₂ else c₁)
  simp [funext_iff] at h
  apply h
  intro a heq
  exact False.elim (h_hole a heq)

theorem vacuous (h_empty: B → False): Surjective f := by
  apply Surjective.intro
  intro b
  exact False.elim (h_empty b)

theorem option_map_surj_of_surj (f_surj: Surjective f): Surjective (Option.map f) where
  exists_ap_eq
    | none => ⟨none, rfl⟩
    | some b => by
      obtain ⟨a, heq⟩ := f_surj.exists_ap_eq b
      subst heq
      exists some a

theorem map_surj_of_surj {α β: Type u} {F: Type u → Type v} [Functor F] [LawfulFunctor F]
  (f: α → β) (f_surj: Surjective f): Surjective (Functor.map f: F α → F β) := by
  obtain ⟨h, hh⟩ := f_surj.exists_right_inv
  apply of_exists_right_inv (Functor.map h)
  funext x
  dsimp
  rw [← LawfulFunctor.comp_map, hh, LawfulFunctor.id_map]

theorem comp_surj_imp_left_surj (gof_surj: Surjective (g ∘ f)): Surjective g := by
  apply Surjective.intro
  intro c
  obtain ⟨a, rfl⟩ := gof_surj.exists_ap_eq c
  exists f a

theorem of_preimage_singletons_nonempty (h: ∀b, Set.nonempty (Set.preimage f {b})): Surjective f := by
  apply Surjective.intro
  intro b
  obtain ⟨a, ha⟩ := h b
  exists a
  exact Eq.symm ha

theorem nonempty_into_subsingleton_surj [inst₁: Nonempty A] [inst₂: Subsingleton B]: Surjective f where
  exists_ap_eq b := by
    obtain ⟨a⟩ := inst₁
    exists a
    exact inst₂.allEq (f a) b

theorem comp_self_surj_iff {e: A → A}: Surjective e ↔ Surjective (e ∘ e) where
  mp h := comp_surj e e h h
  mpr h := comp_surj_imp_left_surj e e h

end Surjective

theorem Injective.right_composition_surj {A B C: Type u} [Nonempty (B → A)] (f: A → B) (f_inj: Injective f): Surjective (fun h: B → C => h ∘ f) := by
  apply Surjective.intro
  intro b'
  exists b' ∘ inv f
  change b' ∘ (inv f ∘ f) = b'
  rw [Injective.inv_left_inv f_inj]
  rfl

theorem Surjective.left_composition_surj {A B C: Type u} [Nonempty (B → A)] (f: A → B) (f_surj: Surjective f): Surjective (fun h: C → A => f ∘ h) := by
  apply Surjective.intro
  intro b'
  exists inv f ∘ b'
  change (f ∘ inv f) ∘ _ = _
  rw [Surjective.inv_right_inv f_surj]
  rfl

instance {f: X → Y} (f_surj: Surjective f): DecidableMem (Set.full_image f) := fun y =>
  Decidable.isTrue (f_surj.exists_ap_eq y)




structure Bijective {A B: Type u} (f: A → B) extends Injective f, Surjective f where of_inj_and_surj ::

namespace Bijective

variable {A B C: Type u} (f: A → B) (g: B → C)

theorem id_bij : Bijective (@id A) := of_inj_and_surj Injective.id_inj Surjective.id_surj

theorem comp_bij (f_bij: Bijective f) (g_bij: Bijective g): Bijective (g ∘ f) where
  toInjective := Injective.comp_inj f g f_bij.toInjective g_bij.toInjective
  toSurjective := Surjective.comp_surj f g f_bij.toSurjective g_bij.toSurjective


theorem exists_inv (f_bij: Bijective f): ∃fi: B → A, f ∘ fi = id ∧ fi ∘ f = id := by
  rcases f_bij with ⟨f_inj, f_surj⟩
  obtain ⟨i_f, hi_f⟩ := f_surj.exists_right_inv
  have : Nonempty (B → A) := ⟨i_f⟩
  obtain ⟨f_i, hf_i⟩ := f_inj.exists_left_inv
  have : f_i = i_f := by
    change f_i ∘ id = id ∘ i_f
    rw [← hi_f, ← hf_i]
    rfl
  subst this
  exists f_i

#print axioms exists_inv

theorem of_exists_inv {f: A → B} (fi: B → A) (hr: f ∘ fi = id) (hl: fi ∘ f = id): Bijective f where
  toInjective := Injective.of_exists_left_inv fi hl
  toSurjective := Surjective.of_exists_right_inv fi hr

theorem of_inv_inv {f: A → B} [Nonempty (B → A)] (hr: f ∘ inv f = id) (hl: inv f ∘ f = id): Bijective f where
  toInjective := Injective.of_inv_left_inv hl
  toSurjective := Surjective.of_exists_right_inv (inv f) hr

theorem iff_exists_inv: Bijective f ↔ ∃fi: B → A, f ∘ fi = id ∧ fi ∘ f = id where
  mp := exists_inv f
  mpr h :=
    let ⟨fi, ffi, fif⟩ := h
    of_exists_inv fi ffi fif

theorem iff_inv_inv [Nonempty (B → A)]: Bijective f ↔ (f ∘ inv f = id ∧ inv f ∘ f = id) where
  mp h := ⟨Surjective.inv_right_inv h.toSurjective, Injective.inv_left_inv h.toInjective⟩
  mpr := fun ⟨hr, hl⟩ => of_inv_inv hr hl

theorem option_map_bijective_of_bijective (f_bij: Bijective f): Bijective (Option.map f) where
  toInjective := Injective.option_map_inj_of_inj f f_bij.toInjective
  toSurjective := Surjective.option_map_surj_of_surj f f_bij.toSurjective

@[simp]
theorem inv_comp {f: A → B} {g: B → C} [inst₁: Nonempty (B → A)] [inst₂: Nonempty (C → B)]
(f_bij: Bijective f) (g_bij: Bijective g): @inv A C (g ∘ f) (nonempty_comp (Y := B)) = inv f ∘ inv g := by
  have gof_inj : Injective (g ∘ f) := by
    apply Injective.comp_inj
    exact f_bij.toInjective
    exact g_bij.toInjective
  have gof_surj : Surjective (g ∘ f) := by
    apply Surjective.comp_surj
    exact f_bij.toSurjective
    exact g_bij.toSurjective
  apply Injective.left_cancellative (g ∘ f) gof_inj
  apply Surjective.right_cancellative (g ∘ f) gof_surj
  rw [Surjective.inv_right_inv gof_surj]
  change g ∘ f = g ∘ ((f ∘ inv f) ∘ (inv g ∘ g)) ∘ f
  rw [Surjective.inv_right_inv f_bij.toSurjective, Injective.inv_left_inv g_bij.toInjective]
  rfl

theorem unique_self_inv_self {X Y: Type u} (f: X → Y) (f_bij: Bijective f) (g₁ g₂: Y → X) (hg₁: f ∘ g₁ ∘ f = f) (hg₂: f ∘ g₂ ∘ f = f): g₁ = g₂ := by
  funext y
  induction y using f_bij.ind
  case h.k x =>
  apply f_bij.eq_of_ap_eq
  change (f ∘ g₁ ∘ f) x = (f ∘ g₂ ∘ f) x
  rw [hg₁, hg₂]


theorem unique_pseudoinverse {X Y: Type u} (f: X → Y) (f_bij: Bijective f) (g₁ g₂: Y → X) (hg₁: IsPseudoInverse f g₁) (hg₂: IsPseudoInverse f g₂): g₁ = g₂ := by
  funext y
  induction y using f_bij.ind
  case h.k x =>
  apply f_bij.eq_of_ap_eq
  change (f ∘ g₁ ∘ f) x = (f ∘ g₂ ∘ f) x
  rw [hg₁, hg₂]

end Bijective

theorem inj_imp_inv_surj {A B: Type u} {f: A → B} [Nonempty (B → A)] (f_inj: Injective f): Surjective (inv f) where
exists_ap_eq b := by
  exists f b
  change (inv f ∘ f) b = b
  rw [Injective.inv_left_inv f_inj]
  rfl

theorem surj_imp_inv_inj {A B: Type u} {f: A → B} (f_surj: Surjective f) [Nonempty (B → A)]: Injective (inv f) where
  eq_of_ap_eq b₁ b₂ heq := by
    have : (f ∘ inv f) b₁ = (f ∘ inv f) b₂ := congrArg f heq
    rw [Surjective.inv_right_inv f_surj] at this
    exact this

@[simp]
theorem inv_bij (f: A -> B) (f_bij: Bijective f) [Nonempty (B → A)]: Bijective (inv f) where
  toInjective := by
    apply surj_imp_inv_inj
    exact f_bij.toSurjective
  toSurjective := by
    apply inj_imp_inv_surj
    exact f_bij.toInjective

theorem eq_inv_iff_comp_eq_id₁ (f: A → B) (g: B → A) [Nonempty (B → A)] (f_bij: Bijective f): inv f = g ↔ f ∘ g = id where
  mp heq := by
    subst heq
    refine Surjective.inv_right_inv f_bij.toSurjective
  mpr h := by
    apply Injective.left_cancellative f f_bij.toInjective
    rw [h]
    exact Surjective.inv_right_inv f_bij.toSurjective

theorem eq_inv_iff_comp_eq_id₂ (f: A → B) (g: B → A) [Nonempty (B → A)] (f_bij: Bijective f): inv f = g ↔ g ∘ f = id where
  mp heq := by
    subst heq
    refine Injective.inv_left_inv f_bij.toInjective
  mpr h := by
    apply Surjective.right_cancellative f f_bij.toSurjective
    rw [h]
    exact Injective.inv_left_inv f_bij.toInjective

@[simp]
theorem inv_inv (f: A → B) (f_bij: Bijective f) [Nonempty (B → A)]: @inv _ _ (inv f) ⟨f⟩ = f := by
  rw [eq_inv_iff_comp_eq_id₁]
  exact (eq_inv_iff_comp_eq_id₂ f (inv f) f_bij).mp rfl
  exact inv_bij f f_bij

namespace Set

variable {A B C: Type u} (f: A → B) (g: B → C)

theorem preimage_of_surj {B₁ B₂: Set B} (f_surj: Surjective f):
  Set.preimage f B₁ = Set.preimage f B₂ → B₁ = B₂ := by
  intro h
  simp [Set.ext_iff] at *
  intro b
  induction b using f_surj.ind
  case k a =>
  exact h a

@[simp]
theorem preimage_inj_iff_surj : Injective (Set.preimage f) ↔ Surjective f := by
  constructor
  · intro h
    apply Surjective.intro
    intro b
    have := h.eq_of_ap_eq {b} Set.empty
    simp at this
    exact this
  · intro f_surj
    apply Injective.intro
    exact fun a₁ a₂ a => preimage_of_surj f f_surj a

@[simp]
theorem inj_imp_preimage_image {A B: Type u} (f: A → B) (f_inj: Injective f) (S: Set A): Set.preimage f (Set.image f S) = S := by
  ext x
  constructor
  intro ⟨k, h, heq⟩
  simp [f_inj] at heq
  subst heq
  exact h
  intro h
  exists x

theorem preimage_surj_iff_inj : Surjective (Set.preimage f) ↔ Injective f := by
  constructor
  · intro h
    apply Injective.intro
    intro a₁ a₂ heq
    have ha := h.exists_ap_eq {a₂}
    rcases ha with ⟨fia, hfia⟩
    simp [Set.ext_iff] at hfia
    have ha₁ := hfia a₁
    have ha₂ := hfia a₂
    apply ha₁.mp
    rw [heq]
    apply ha₂.mpr
    rfl
  · intro f_inj
    apply Surjective.intro
    intro b
    exists Set.image f b
    exact inj_imp_preimage_image f f_inj b

@[simp]
theorem surj_imp_image_preimage {A B: Type u} (f: A → B) (f_surj: Surjective f) (S: Set B): Set.image f (Set.preimage f S) = S := by
  ext x
  induction x using f_surj.ind
  case h.k a =>

  constructor
  intro ⟨k, h, heq⟩
  rw [← heq]
  exact h

  intro h
  exists a

theorem image_surj_iff_surj : Surjective (Set.image f) ↔ Surjective f := by
  constructor
  · intro image_surj
    apply Surjective.intro
    intro b
    obtain ⟨sa, hsa⟩ := image_surj.exists_ap_eq {b}
    replace hsa := Set.ext_iff.mp hsa b
    simp at hsa
    rcases hsa with ⟨a, _, heq⟩
    exact ⟨a, heq⟩
  . intro f_surj
    apply Surjective.of_exists_right_inv (Set.preimage f)
    funext x
    simp
    exact surj_imp_image_preimage f f_surj x

@[simp]
theorem singleton_inj : @Injective X (Set X) Set.singleton := by
  apply Injective.intro
  simp

theorem image_inj_iff_inj: Injective (Set.image f) ↔ Injective f := by
  constructor
  · intro image_inj
    apply Injective.intro
    intro a₁ a₂ heq
    apply singleton_inj.eq_of_ap_eq
    apply image_inj.eq_of_ap_eq
    simp [Set.ext_iff]
    intro k
    exact Eq.to_iff (congrFun (congrArg Eq heq) k)
  · intro f_inj
    apply Injective.intro
    intro s₁ s₂ heq
    simp [Set.ext_iff] at *
    intro x
    replace heq := heq (f x)
    obtain ⟨h₁, h₂⟩ := heq
    constructor <;> simp_all



end Set

theorem Surjective.set_ind {A B: Type u} {f: A → B} {motive : Set B → Prop} (f_surj: Surjective f) (images: (a: Set A) → motive (Set.image f a)) (b: Set B): motive b := by
  rw [← Set.surj_imp_image_preimage f f_surj b]
  exact images (Set.preimage f b)

def Set.subtype {X: Type u} (A: Set X): Type u := {x: X // x ∈ A}

theorem Subtype.val_inj {p: X → Prop}: Injective (@Subtype.val X p) := by
  apply Injective.intro
  intro a₁ a₂ heq
  exact Subtype.eq heq

def subtype_ind {motive: Set (@Subtype X p) → Sort u}
(full: ∀S: Set X, motive (Set.preimage Subtype.val S)) (S: Set (Subtype p)): motive S := by
  replace full := full (Set.image Subtype.val S)
  simp [Set.inj_imp_preimage_image, Subtype.val_inj] at full
  exact full


@[simp]
theorem subtype_full_image_val : Set.full_image (@Subtype.val X fun x => x ∈ S) = S := by
  simp [Set.ext_iff]

@[simp]
theorem subtype_full_image_val' : Set.full_image (@Subtype.val X p) = {elem := p} := by
  simp [Set.ext_iff]

@[simp]
theorem forall_subtype {S: Set X} {p: S.subtype → Prop} : (∀x: Set.subtype S, p x) ↔ ∀x, ∀h: x ∈ S, p ⟨x,h⟩ where
  mp h x hx := h ⟨x, hx⟩
  mpr h x := h x.val x.property

@[simp]
theorem exists_subtype {S: Set X} {p: S.subtype → Prop} : (∃x: Set.subtype S, p x) ↔ ∃x, ∃h: x ∈ S, p ⟨x,h⟩ where
  mp h := by
    obtain ⟨⟨x, hx⟩, h⟩ := h
    exists x, hx
  mpr h := by
    obtain ⟨x, h, hx⟩ := h
    exists ⟨x, h⟩

@[simp]
theorem forall_set_subtype {S: Set X} {p: (Set S.subtype) → Prop} : (∀U: (Set (Set.subtype S)), p U) ↔ ∀U: Set X, p (Set.preimage Subtype.val U) where
  mp h U := h (Set.preimage Subtype.val U)
  mpr h U := subtype_ind h U

@[simp]
theorem exists_set_subtype {S: Set X} {p: (Set S.subtype) → Prop} : (∃U: (Set (Set.subtype S)), p U) ↔ ∃U: Set X, p (Set.preimage Subtype.val U) where
  mp h := by
    obtain ⟨U, hU⟩ := h
    exists Set.image (@Subtype.val X (fun x => x ∈ S)) U
    rw [Set.inj_imp_preimage_image _ (Subtype.val_inj)]
    exact hU
  mpr h := by
    obtain ⟨U, hU⟩ := h
    exists Set.preimage Subtype.val U

theorem Function.curry_bij {A B C: Type u}: Bijective (@Function.curry A B C) := by
  apply Bijective.of_exists_inv (Function.uncurry)
  rfl
  rfl

theorem Function.uncurry_bij {A B C: Type u}: Bijective (@Function.uncurry A B C) := by
  apply Bijective.of_exists_inv (Function.curry)
  rfl
  rfl

@[simp]
theorem inv_curry {A B C: Type u}: @inv _ _  (@Function.curry A B C) ⟨Function.uncurry⟩ = Function.uncurry := by
  funext f
  dsimp [inv]
  have h : f ∈ Set.full_image Function.curry := by
    exact Surjective.all_in_full_image _ (Function.curry_bij.toSurjective) f
  rw [dif_pos h]
  apply Injective.eq_of_ap_eq Function.curry_bij.toInjective
  dsimp
  exact h.choose_spec

@[simp]
theorem inv_uncurry {A B C: Type u}: @inv _ _ (@Function.uncurry A B C) ⟨Function.curry⟩ = Function.curry := by
  funext f
  dsimp [inv]
  have h : f ∈ Set.full_image Function.uncurry := by
    exact Surjective.all_in_full_image _ (Function.uncurry_bij.toSurjective) f
  rw [dif_pos h]
  apply Injective.eq_of_ap_eq Function.uncurry_bij.toInjective
  dsimp
  exact h.choose_spec


private theorem nonempty_bernstein_lemma {X Y: Type u} [Nonempty Y] (f: X → Y)
(f_inj: Injective f) (g: Y → X) (g_inj: Injective g): ∃b: X → Y, Bijective b := by
  -- Proof based on fixed-point proof in ncatlab article
  let φ (U: Set X): Set X := Set.complement (Set.image g (Set.complement (Set.image f U)))

  have φ_mono: ∀S₁ S₂, S₁ ⊆ S₂ → φ S₁ ⊆ φ S₂ := by
    intro S₁ S₂ sub
    unfold φ
    simp [g_inj, f_inj, sub]
  obtain ⟨U, hU⟩ := Set.exists_fixed_point φ φ_mono

  obtain ⟨g_inv, hg⟩ := g_inj.exists_left_inv

  replace hg : ∀u, g_inv (g u) = u := by
    intro u
    rw [← @Function.comp_apply _ _ _ g_inv g, hg, id_def]


  let h x := open Classical in if x ∈ U then f x else g_inv x

  exists h
  apply Bijective.of_inj_and_surj
  · apply Injective.intro
    intro a₁ a₂ heq
    dsimp [h] at heq
    clear h
    split at heq <;> split at heq
    · exact f_inj.eq_of_ap_eq a₁ a₂ heq
    · rename a₁ ∈ U => a₁U
      rename ¬a₂ ∈ U => a₂U
      rw [← hU] at a₂U
      simp [φ] at a₂U
      rcases a₂U with ⟨y, hy, heq'⟩
      subst heq'
      rw [hg] at heq
      subst heq
      exact False.elim (hy a₁ a₁U rfl)
    · rename ¬a₁ ∈ U => a₁U
      rename a₂ ∈ U => a₂U
      rw [← hU] at a₁U
      simp [φ] at a₁U
      rcases a₁U with ⟨y, hy, heq⟩
      subst heq
      rw [hg] at heq
      subst heq
      exact False.elim (hy a₂ a₂U rfl)
    · rename ¬a₁ ∈ U => a₁U
      rename ¬a₂ ∈ U => a₂U
      rw [← hU] at a₁U a₂U
      simp [φ] at a₁U a₂U
      rcases a₁U with ⟨y₁, hy₁, heq₁⟩
      rcases a₂U with ⟨y₂, hy₂, heq₂⟩
      subst heq₁ heq₂
      rw [hg, hg] at heq
      exact congrArg g heq
  · apply Surjective.intro
    intro b
    simp [h]
    clear h
    by_cases b ∈ Set.image f U
    case pos h =>
      rcases h with ⟨a, aU, rfl⟩
      exists a
      exact if_pos aU
    case neg h =>
      exists g b
      rw [hg]
      apply if_neg
      rw [← hU]
      simp [φ]
      exists b
      simp at h
      exact ⟨h, rfl⟩

theorem bernstein_lemma {X Y: Type u} (f: X → Y) (f_inj: Injective f) (g: Y → X)
(g_inj: Injective g): ∃b: X → Y, Bijective b := by
  by_cases X → False
  case pos h =>
    exists fun x => False.elim $ h x
    apply Bijective.of_exists_inv fun y => False.elim $ (h (g y)) <;> funext p <;> exfalso
    exact h (g p)
    exact h p
  case neg h =>
    rw [Classical.not_forall] at h
    rcases h with ⟨x, _⟩
    have : Nonempty Y := ⟨f x⟩
    exact nonempty_bernstein_lemma f f_inj g g_inj
