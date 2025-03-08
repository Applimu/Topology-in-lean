

structure PreRational where
  num: Int
  den: Int
  zero_lt_den: 0 < den

def PreRational.den_neq_zero (p: PreRational): p.den ≠ 0 :=
  (Int.ne_of_lt p.zero_lt_den).symm

instance : Setoid PreRational where
  r r₁ r₂ := r₁.num * r₂.den = r₂.num * r₁.den
  iseqv := (by
    refine { refl := congrFun rfl, symm := ?symm, trans := ?trans }
    case symm =>
      intro x y h
      exact Eq.symm h
    case trans =>
      intro x y z h₁ h₂
      rw [← Int.mul_eq_mul_right_iff y.den_neq_zero, Int.mul_right_comm, h₁]
      rw [Int.mul_right_comm z.num, ← h₂, Int.mul_right_comm]
    )



def Rational := Quotient instSetoidPreRational

def Rational.mk (num den: Int) (h: den ≠ 0): Rational :=
  Quotient.mk' <| if h₂: den > 0 then
    PreRational.mk num den h₂
  else
    PreRational.mk num (-den) (by omega)

infix : 10 " /// " => Rational.mk

instance : LT PreRational where
  lt x y := x.num * y.den < y.num * x.den

instance : LT Rational where
  lt := Quotient.lift₂ (fun x y =>
    x.num * y.den < x.den * y.num
  ) (by
    intro a b c d hac hbd
    have this₁ : a.num * c.den = c.num * a.den := by
      exact hac
    have this₂ : _ = _ := hbd
    simp
    constructor
    case mp =>
      intro hlt
      apply Int.lt_of_mul_lt_mul_right (a :=  a.den * b.den)
      case h => exact Int.mul_nonneg (Int.le_of_lt a.zero_lt_den) (Int.le_of_lt b.zero_lt_den)
      case w =>
        rw [← Int.mul_assoc, Int.mul_right_comm c.num, ← hac, Int.mul_right_comm, Int.mul_right_comm a.num, Int.mul_assoc]
        rw [← Int.mul_assoc (c.den * _), Int.mul_right_comm c.den, Int.mul_assoc (c.den * _), ← hbd, Int.mul_comm (c.den * _)]
        rw [Int.mul_assoc b.num, ← Int.mul_assoc d.den, Int.mul_comm d.den, Int.mul_comm (c.den * _), ← Int.mul_assoc b.num, Int.mul_comm b.num]
        refine Int.mul_lt_mul_of_pos_right hlt ?h₂
        exact Int.mul_pos c.zero_lt_den d.zero_lt_den
    case mpr =>
      intro hlt
      apply Int.lt_of_mul_lt_mul_left (a := c.den * d.den)
      rw [Int.mul_right_comm, ← Int.mul_assoc, Int.mul_comm c.den, hac, Int.mul_right_comm (c.num * _), Int.mul_right_comm c.num, Int.mul_assoc]
      rw [Int.mul_comm a.den b.num, ← Int.mul_assoc (c.den * _), Int.mul_assoc c.den, Int.mul_comm d.den, hbd, ← Int.mul_assoc c.den, Int.mul_assoc (c.den * _), Int.mul_comm b.den]
      refine Int.mul_lt_mul_of_pos_right hlt ?_
      exact Int.mul_pos a.zero_lt_den b.zero_lt_den
  )

instance : OfNat PreRational n where
  ofNat := PreRational.mk n 1 (Int.zero_lt_one)

instance : OfNat Rational n where
  ofNat := Quotient.mk _ (OfNat.ofNat n)

instance : Add Rational where
  add := Quotient.lift (fun a =>
    Quotient.lift (fun b =>
      Rational.mk (
        a.num * b.den + a.den * b.num
      ) (a.den * b.den) (
        Int.mul_ne_zero (a.den_neq_zero) (b.den_neq_zero)
      )
    ) (by
      intro b₁ b₂ _
      simp
    )
  ) (by
    intro a₁ b₂ related
    rfl
  )

theorem Rational.zero_lt_one: (0: Rational) < 1 := Int.zero_lt_one

theorem Rational.num_gt_zero (x y: Int) (h: y ≠ 0): 0 < x → 0 < (x /// y) h := by
  intro h₂


#check (3 /// 5)
