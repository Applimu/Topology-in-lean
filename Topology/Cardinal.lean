
import Topology.Functions

instance : Equivalence (fun A B => ∃f: A → B, Bijective f) where
  refl A := by
    exists id
    exact Bijective.id_bij
  symm := by
    intro A B ⟨f, hf⟩
    obtain ⟨fi, ffi, fif⟩ := hf.exists_inv
    exists fi
    apply Bijective.of_exists_inv f <;> assumption
  trans := by
    intro A B C ⟨f₁, f₁_bij⟩ ⟨f₂, f₂_bij⟩
    exists f₂ ∘ f₁
    exact Bijective.comp_bij f₁ f₂ f₁_bij f₂_bij

instance : Setoid (Type u) where
  r A B := ∃f: A → B, Bijective f
  iseqv := instEquivalenceExistsForallBijective

def Cardinal := Quotient instSetoidType_topology

def card : Type u → Cardinal.{u} := Quotient.mk _

def Cardinal.ind {motive: Cardinal.{v} → Prop} (c: ∀A: Type v, motive $ card.{v} A) (a: Cardinal): motive a := by
  induction a using Quotient.ind
  case a A =>
  exact c A

def Cardinal.liftOn.{u} (a: Cardinal.{u}) (f: Type u → β) (h: ∀A B, A ≈ B → f A = f B): β :=
  Quotient.liftOn a f h

def Cardinal.liftOn₂.{u} (a b: Cardinal.{u}) (f: Type u → Type u → β)
(h: ∀A₁ B₁ A₂ B₂, A₁ ≈ A₂ → B₁ ≈ B₂ → f A₁ B₁ = f A₂ B₂): β :=
  Quotient.liftOn₂ a b f h

theorem Cardinal.card_eq_card_iff : card A = card B ↔ A ≈ B := ⟨Quotient.exact, Quotient.sound⟩

def Cardinal.succ (a: Cardinal): Cardinal := Quotient.liftOn a (fun A => card (Option A)) (by
  intro A B ⟨f, f_bij⟩
  apply Quotient.sound
  exists Option.map f
  exact Bijective.option_map_bijective_of_bijective f f_bij
)

def Cardinal.add (a b: Cardinal): Cardinal := Quotient.liftOn₂ a b (fun A B => card (A ⊕ B)) (by
  intro A₁ B₁ A₂ B₂ ⟨f, f_bij⟩ ⟨g, g_bij⟩
  apply Quotient.sound
  exists fun
    | Sum.inl a => Sum.inl $ f a
    | Sum.inr b => Sum.inr $ g b
  obtain ⟨fi, ffi, fif⟩ := f_bij.exists_inv
  obtain ⟨gi, ggi, gig⟩ := g_bij.exists_inv
  apply Bijective.of_exists_inv fun
    | Sum.inl a => Sum.inl $ fi a
    | Sum.inr b => Sum.inr $ gi b
  · simp [funext_iff] at *
    rintro (a | b)
    simp
    exact ffi a
    simp
    exact ggi b
  · simp [funext_iff] at *
    rintro (a | b)
    simp
    exact fif a
    simp
    exact gig b
)

instance : Add Cardinal where
  add := Cardinal.add

theorem Cardinal.add_def (A B: Type u): card A + card B = card (A ⊕ B) := by
  simp [card, HAdd.hAdd, Add.add, Cardinal.add]
  rfl

theorem Sum.swap_bij (A B): Bijective (@Sum.swap A B) := by
  apply Bijective.of_exists_inv swap
  exact swap_swap_eq
  exact swap_swap_eq

theorem Cardinal.add_comm (a b: Cardinal): a + b = b + a := by
  induction a using Cardinal.ind
  case c A =>
  induction b using Cardinal.ind
  case c B =>
  apply Quotient.sound
  exact ⟨Sum.swap, Sum.swap_bij A B⟩

def Sum.assoc : (A ⊕ B) ⊕ C → A ⊕ (B ⊕ C)
| Sum.inl (Sum.inl a) => Sum.inl a
| Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
| Sum.inr c => Sum.inr (Sum.inr c)

theorem Sum.assoc_bij : Bijective (@Sum.assoc A B C) := by
  apply Bijective.of_inj_and_surj
  · apply Injective.intro
    intro a₁ a₂ heq
    rcases a₁ with (a₁ | b₁) | c₁ <;> rcases a₂ with (a₂ | b₂) | c₂ <;> simp_all [Sum.assoc]
  · apply Surjective.intro
    intro b
    rcases b with a | (b | c)
    exists Sum.inl (Sum.inl a)
    exists Sum.inl (Sum.inr b)
    exists Sum.inr c


theorem Cardinal.add_assoc (a b c: Cardinal): (a + b) + c = a + (b + c) := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  induction c using Cardinal.ind
  case c.c.c A B C =>
  apply Quotient.sound
  exists Sum.assoc
  exact Sum.assoc_bij

def Cardinal.fin (n: Nat): Cardinal := card (Fin n)

instance : OfNat Cardinal n where
  ofNat := Cardinal.fin n

@[simp]
theorem Cardinal.add_zero (a: Cardinal) : a + 0 = a := by
  induction a using Cardinal.ind
  case c A =>
  apply Quotient.sound
  exists fun | Sum.inl a => a
  apply Bijective.of_exists_inv Sum.inl <;> simp [funext_iff]
  refine fun | Sum.inl a => rfl

theorem Cardinal.zero_add (a: Cardinal) : 0 + a = a := by
  rw [Cardinal.add_comm]
  exact add_zero a

def Cardinal.countable_inf : Cardinal := card Nat

def Cardinal.le (a b: Cardinal): Prop := Quotient.liftOn₂ a b (fun A B => ∃f: A → B, Injective f) (by
  intro A₁ B₁ A₂ B₂ ⟨fA, fA_bij⟩ ⟨gB, gB_bij⟩
  simp
  constructor
  · rintro ⟨f, f_inj⟩
    obtain ⟨fAi, ffAi, fAif⟩ := fA_bij.exists_inv
    exists gB ∘ f ∘ fAi
    apply Injective.comp_inj
    apply Injective.comp_inj
    exact Injective.of_exists_left_inv fA ffAi
    exact f_inj
    exact gB_bij.toInjective
  · rintro ⟨f, f_inj⟩
    obtain ⟨gBi, ggBi, gBig⟩ := gB_bij.exists_inv
    exists gBi ∘ f ∘ fA
    apply Injective.comp_inj
    apply Injective.comp_inj
    exact fA_bij.toInjective
    exact f_inj
    exact Injective.of_exists_left_inv gB ggBi
)

instance : LE Cardinal where
  le := Cardinal.le

theorem Cardinal.le_def : card A ≤ card B ↔ ∃f: A → B, Injective f := Iff.rfl

theorem Cardinal.le_refl (a: Cardinal): a ≤ a := by
  induction a using Cardinal.ind
  case c A =>
  exists id
  exact Injective.id_inj

theorem Cardinal.le_trans (a b c: Cardinal): a ≤ b → b ≤ c → a ≤ c := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  induction c using Cardinal.ind
  case c.c.c A B C =>
  rintro ⟨f₁, f₁_inj⟩ ⟨f₂, f₂_inj⟩
  exists f₂ ∘ f₁
  exact Injective.comp_inj f₁ f₂ f₁_inj f₂_inj

theorem Cardinal.antisymm (a b: Cardinal): a ≤ b → b ≤ a → a = b := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  case c.c A B =>
  rintro ⟨f₁, f₁_inj⟩ ⟨f₂, f₂_inj⟩
  apply Quotient.sound
  change ∃f, _
  apply bernstein_lemma f₁ f₁_inj f₂ f₂_inj

theorem Fin.castLE_inj {h: n ≤ m}: Injective (Fin.castLE h) := by
  apply Injective.intro
  intro a₁ a₂ heq
  simp [castLE] at heq
  exact eq_of_val_eq heq

theorem Cardinal.fin_mono : n ≤ m → fin n ≤ fin m := by
  intro hle
  change ∃f, _
  exists Fin.castLE hle
  exact Fin.castLE_inj

theorem Cardinal.le_add_right {n m: Cardinal} : n ≤ n + m := by
  induction n using Cardinal.ind
  induction m using Cardinal.ind
  case c.c A B =>
  apply Cardinal.le_def.mpr
  exists Sum.inl
  constructor
  intro a₁ a₂ heq
  injection heq

theorem Cardinal.le_add_left {n m: Cardinal} : m ≤ n + m := by
  induction n using Cardinal.ind
  induction m using Cardinal.ind
  case c.c A B =>
  apply Cardinal.le_def.mpr
  exists Sum.inr
  constructor
  intro a₁ a₂ heq
  injection heq

theorem Cardinal.le_iff_exists {a b: Cardinal}: a ≤ b ↔ ∃c, a + c = b := by
  constructor
  · intro hle
    induction a using Cardinal.ind
    induction b using Cardinal.ind
    next A B =>
    obtain ⟨f, hf⟩ := hle
    suffices ∃C:  type_of%A , (A ⊕ C) ≈ B by
      obtain ⟨C, hC⟩ := this
      exists card C
      apply Quotient.sound
      exact hC
    exists {x:B // ∀a: A, f a ≠ x}
    exists fun
      | Sum.inl a => f a
      | Sum.inr b => b.val
    constructor <;> constructor
    · intro a₁ a₂ heq
      split at heq <;> split at heq <;> simp_all
      next h1 h2 h3 b =>
        apply b.property
        exact heq
      next _ b _ _ =>
        apply b.property
        rw [eq_comm] at heq
        exact heq
      next =>
        apply Subtype.eq heq
    · intro b
      by_cases ∃a, f a = b
      case pos ex =>
        obtain ⟨a, ha⟩ := ex
        subst ha
        exists Sum.inl a
      case neg ex =>
        simp at ex
        exists Sum.inr ⟨b, ex⟩
  · intro ⟨c, heq⟩
    subst heq
    exact le_add_right

theorem Cardinal.zero_le {a: Cardinal}: 0 ≤ a := by
  rw [le_iff_exists]
  exists a
  rw [zero_add]

theorem Cardinal.eq_zero_iff_le_zero {a: Cardinal} : a = 0 ↔ a ≤ 0 := by
  constructor
  · intro rfl
    exact le_refl 0
  · intro hle
    apply antisymm _ _ hle zero_le




def Cardinal.isInfinite (a: Cardinal): Prop := Cardinal.countable_inf ≤ a

theorem Cardinal.fin_le_countable_inf (n: Nat): Cardinal.fin n ≤ Cardinal.countable_inf := by
  exists Fin.val
  apply Injective.intro
  exact fun a₁ a₂ a => Fin.eq_of_val_eq a

@[simp]
theorem Cardinal.fin_add_countable_inf (n: Nat): fin n + countable_inf = countable_inf := by
  apply antisymm
  · exists fun
      | Sum.inl v => v
      | Sum.inr i => n + i
    constructor
    intro a₁ a₂ heq
    split at heq <;> split at heq
    all_goals {
      norm_cast at heq
      simp_all [Fin.ext_iff, @Eq.comm _  (n + _)]
      try omega
    }
  · exact le_add_left


theorem Cardinal.fin_add_infinite (b: Cardinal) (n: Nat) (b_inf: b.isInfinite): Cardinal.fin n + b = b := by
  apply Cardinal.antisymm
  · rw [isInfinite, le_iff_exists] at b_inf
    obtain ⟨c, rfl⟩ := b_inf
    rw [← Cardinal.add_assoc, fin_add_countable_inf]
    exact Cardinal.le_refl _

  · exact le_add_left


theorem Prod.map_inj_of_inj : Injective f → Injective g → Injective (Prod.map f g) := by
  intro f_inj g_inj
  apply Injective.intro
  intro (a₁, b₁) (a₂, b₂) heq
  simp at *
  constructor
  exact f_inj.eq_of_ap_eq _ _ heq.left
  exact g_inj.eq_of_ap_eq _ _ heq.right

theorem Prod.map_surj_of_surj : Surjective f → Surjective g → Surjective (Prod.map f g) := by
  intro f_surj g_surj
  apply Surjective.intro
  intro ⟨b₁, b₂⟩
  obtain ⟨a₁, heq₁⟩ := f_surj.exists_ap_eq b₁
  obtain ⟨a₂, heq₂⟩ := g_surj.exists_ap_eq b₂
  subst heq₁ heq₂
  exists (a₁, a₂)

theorem Prod.map_bij_of_bij : Bijective f → Bijective g → Bijective (Prod.map f g) := by
  intro f_bij g_bij
  apply Bijective.of_inj_and_surj
  refine map_inj_of_inj ?_ ?_
  exact f_bij.toInjective
  exact g_bij.toInjective
  refine map_surj_of_surj ?_ ?_
  exact f_bij.toSurjective
  exact g_bij.toSurjective


def Cardinal.mul (a b: Cardinal): Cardinal := Cardinal.liftOn₂ a b (fun A B => card (A × B)) (by
  intro A₁ B₁ A₂ B₂ ⟨fA, fA_bij⟩ ⟨fB, fB_bij⟩
  apply Quotient.sound
  exists Prod.map fA fB
  exact Prod.map_bij_of_bij fA_bij fB_bij
)

instance : Mul Cardinal where
  mul := Cardinal.mul

theorem Cardinal.mul_def {A B: Type u}: card A * card B = card (A × B) := by
  apply Quotient.sound
  exact Setoid.refl (A × B)

theorem Cardinal.mul_comm (a b: Cardinal): a * b = b * a := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  case c.c A B =>
  apply Quotient.sound
  exists Prod.swap
  apply Bijective.of_exists_inv Prod.swap <;> rfl

def Prod.assoc : (A × B) × C → A × (B × C)
  | ((a, b),c) => (a,(b, c))

theorem Prod.assoc_bij: Bijective (@Prod.assoc A B C) := by
  apply Bijective.of_exists_inv fun (a, (b,c)) => ((a,b),c) <;> rfl

theorem Cardinal.mul_assoc (a b c: Cardinal): a * b * c = a * (b * c) := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  induction c using Cardinal.ind
  case c.c.c A B C =>
  apply Quotient.sound
  exact ⟨Prod.assoc, Prod.assoc_bij⟩

@[simp]
theorem Cardinal.mul_one (a: Cardinal): a * 1 = a := by
  induction a using Cardinal.ind
  apply Quotient.sound
  exists fun (a, _) => a
  apply Bijective.of_exists_inv fun a => (a, 0) <;> funext a <;> simp
  · rcases a with ⟨a', z⟩
    simp
    omega

@[simp]
theorem Cardinal.one_mul (a: Cardinal): 1 * a = a := by
  rw [mul_comm, mul_one]

@[simp]
theorem Cardinal.zero_mul (a: Cardinal): 0 * a = 0 := by
  induction a using Cardinal.ind
  apply Quotient.sound
  exists fun a => nomatch a
  apply Bijective.of_exists_inv fun a => nomatch a <;> funext c <;> nomatch c

@[simp]
theorem Cardinal.mul_zero (a: Cardinal): a * 0 = 0 := by
  rw [mul_comm, zero_mul]

def prod_sum : A × (B ⊕ C) → A × B ⊕ A × C
| (a, Sum.inl b) => Sum.inl (a,b)
| (a, Sum.inr c) => Sum.inr (a,c)

theorem prod_sum_bij: Bijective (@prod_sum A B C) := by
  apply Bijective.of_exists_inv fun
    | Sum.inl (a,b) => (a, Sum.inl b)
    | Sum.inr (a,c) => (a, Sum.inr c)
  <;> funext x
  cases x <;> rfl
  rcases x with ⟨a, (b | c)⟩ <;> rfl

theorem Cardinal.mul_add (a b c: Cardinal): a * (b + c) = a * b + a * c := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  induction c using Cardinal.ind
  case c.c.c A B C =>
  apply Quotient.sound
  exists prod_sum
  exact prod_sum_bij

theorem Cardinal.add_mul (a b c: Cardinal): (a + b) * c = a * c + b * c := by
  repeat rw [Cardinal.mul_comm _ c]
  exact Cardinal.mul_add c a b

theorem Cardinal.card_neq_zero_iff : card A ≠ 0 ↔ Nonempty A := by
  constructor
  · intro (hneq: ¬card A = card (Fin 0))
    simp [card_eq_card_iff] at hneq
    replace hneq := fun f x₁ x₂ => hneq ⟨f, x₁, ⟨x₂⟩⟩
    simp at hneq
    apply Classical.byContradiction fun h => ?_
    apply hneq fun a => False.elim $ h ⟨a⟩
    constructor <;> simp
    exact fun a => False.elim $ h ⟨a⟩
  · intro ⟨a⟩ heq
    rw [eq_zero_iff_le_zero] at heq
    obtain ⟨f, hf⟩ := heq
    nomatch f a


theorem Cardinal.mul_eq_zero {a b: Cardinal} : a * b = 0 ↔ (a = 0 ∨ b = 0) := by
  constructor
  · intro heq
    induction a using Cardinal.ind
    induction b using Cardinal.ind
    next A B =>
    rw [mul_def] at heq
    apply Classical.byContradiction fun h => ?_
    simp at h
    simp [← ne_eq, card_neq_zero_iff] at h
    revert heq
    simp [card_neq_zero_iff]
    obtain ⟨h₁, h₂⟩ := h
    apply @instNonemptyProd
  · rintro (rfl | rfl) <;> simp


def Cardinal.pow (a b: Cardinal): Cardinal := Cardinal.liftOn₂ a b (fun A B => card (B → A)) (by
  intro A₁ B₁ A₂ B₂ ⟨fA, A_bij⟩ ⟨fB, B_bij⟩
  apply Quotient.sound
  have ⟨fBi, ffBi, fBif⟩ := B_bij.exists_inv
  have ⟨fAi, ffAi, fAif⟩ := A_bij.exists_inv

  exists fun g => fA ∘ g ∘ fBi

  apply Bijective.of_exists_inv fun (g: B₂ → A₂) => fAi ∘ g ∘ fB <;> funext x
  change (fA ∘ fAi) ∘ x ∘ (fB ∘ fBi) = x
  rw [ffAi, ffBi]
  rfl
  change (fAi ∘ fA) ∘ x ∘ (fBi ∘ fB) = x
  rw [fAif, fBif]
  rfl
)

instance : HomogeneousPow Cardinal where
  pow := Cardinal.pow

theorem Cardinal.pow_add (a b c: Cardinal) : a ^ (b + c) = a ^ b * a ^ c := by
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  induction c using Cardinal.ind
  case c.c.c A B C =>
  apply Quotient.sound
  exists fun f => (fun b => f (Sum.inl b), fun c => f (Sum.inr c))
  apply Bijective.of_exists_inv fun (f₁, f₂) => fun
    | Sum.inl a => f₁ a
    | Sum.inr b => f₂ b
  <;> simp [funext_iff]
  intro f x
  cases x <;> rfl

theorem Cardinal.pow_pow (a b c: Cardinal): (a ^ b) ^ c = a ^ (b * c) := by
  rw [Cardinal.mul_comm]
  induction a using Cardinal.ind
  induction b using Cardinal.ind
  induction c using Cardinal.ind
  case c.c.c A B C =>
  apply Quotient.sound
  exists @Function.uncurry C B A
  apply Bijective.of_exists_inv Function.curry <;> rfl

theorem Cardinal.pow_one (a: Cardinal): a ^ 1 = a := by
  induction a using Cardinal.ind
  case c A =>
  apply Quotient.sound
  exists fun f => f ⟨0, Nat.zero_lt_one⟩
  apply Bijective.of_exists_inv fun a _ => a
  rfl
  funext f x
  dsimp
  have : x = 0 := by exact Fin.fin_one_eq_zero x
  rw [this]

theorem Cardinal.pow_zero (a: Cardinal) : a ^ 0 = 1 := by
  induction a using Cardinal.ind
  case c A =>
  apply Quotient.sound
  exists fun _ => 0
  apply Bijective.of_exists_inv (fun x y => nomatch y) <;> simp [funext_iff]


theorem Cardinal.one_pow (a: Cardinal) : 1 ^ a = 1 := by
  induction a using Cardinal.ind
  case c A =>
  apply Quotient.sound
  exists fun _ => 0
  apply Bijective.of_exists_inv (fun x y => 0) <;> simp [funext_iff]
  intro f a
  exact Eq.symm (Fin.fin_one_eq_zero (f a))



def Cardinal.top.{u} : Cardinal.{u + 1} := card ((T: Type u) × T)

def Cardinal.plift (a: Cardinal.{u}): Cardinal.{u + 1} := Cardinal.liftOn a (fun A => card (PLift A)) (by
  intro A B ⟨f, hf⟩
  apply Quotient.sound
  exists fun ⟨a⟩ => ⟨f a⟩
  constructor <;> constructor <;> simp
  · intro ⟨a₁⟩ ⟨a₂⟩ heq
    obtain rfl := hf.eq_of_ap_eq a₁ a₂ heq
    rfl
  · intro ⟨b⟩
    obtain ⟨a, rfl⟩ := hf.exists_ap_eq b
    exists ⟨a⟩
)



theorem Cardinal.le_max.{u} (a: Cardinal.{u}): plift a ≤ Cardinal.top := by
  induction a using Cardinal.ind
  next A =>
  exists fun a => ⟨A, a.down⟩
  constructor
  intro ⟨a₁⟩ ⟨a₂⟩ heq
  injection heq with h₁ h₂
  simpa using h₂


def Cardinal.ulift (a: Cardinal.{u}): Cardinal.{max u v} := Cardinal.liftOn a (fun A => card (ULift A)) (by
  intro A B ⟨f, hf⟩
  apply Quotient.sound
  exists fun ⟨a⟩ => ⟨f a⟩
  constructor <;> constructor <;> simp
  · intro ⟨a₁⟩ ⟨a₂⟩ heq
    obtain rfl := hf.eq_of_ap_eq a₁ a₂ heq
    rfl
  · intro ⟨b ⟩
    obtain ⟨a, rfl⟩ := hf.exists_ap_eq b
    exists ⟨a⟩
)

-- theorem ULift.down_inj (A: Type u) : Injective.{u, max u v} (ULift.down (ULift.{v,u} A: Type (max u v))) := by
--   apply Injective.of_exists_left_inv (ULift.up)

-- theorem Cardinal.ulift_inj.{u,v}: Injective (ulift.{u,v}) := by
--   constructor
--   intro c₁ c₂ heq
--   induction c₁ using Cardinal.ind
--   induction c₂ using Cardinal.ind
--   next A₁ A₂ =>
--     apply Quotient.sound
--     replace heq := Quotient.exact heq
--     simp [Quotient.exact, ulift] at heq
--     obtain ⟨f, hf⟩ := heq
--     let f': A₁ → A₂ := fun a₁ => ULift.down (f ⟨a₁⟩)
--     exists f'
--     constructor <;> constructor
--     · simp [f']
--       intro x₁ x₂ heq
