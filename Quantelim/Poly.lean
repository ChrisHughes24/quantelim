import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Order.PiLex
import Mathlib.Data.Vector.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-- Polynomials in n variables as a polynomial in var 0 over the ring of polynomials in the remaining variables -/
inductive PolyAux : (n : ℕ) → Type
  | ofInt' : ℤ  → PolyAux 0
  | const : {n : ℕ} → PolyAux n → PolyAux (n+1)
  -- Never use when second part is zero
  | constAddXMul : {n : ℕ} → PolyAux n → PolyAux (n + 1) → PolyAux (n + 1)
  deriving DecidableEq

namespace PolyAux

variable {n : ℕ} {K : Type*} [CommRing K]

@[simp]
def eval : {n : ℕ} → PolyAux n → (vars : Fin n → K) → K
  | _, ofInt' q, _ => q
  | _, const p, vars => p.eval (fun i => vars i.succ)
  | _, constAddXMul p q, vars =>
    p.eval (fun i => vars i.succ) + vars 0 * q.eval vars

def ofInt : ∀ {n : ℕ}, ℤ  → PolyAux n
  | 0, x => ofInt' x
  | _+1, x => const (ofInt x)

instance {n : ℕ} : IntCast (PolyAux n) := ⟨ofInt⟩

@[simp]
theorem eval_ofInt : ∀ {n : ℕ} (x : ℤ) (vars : Fin n → K),
    eval (ofInt x) vars = x
  | 0, _, _ => by simp [eval]
  | n+1, x, vars => by
    rw [ofInt, eval, eval_ofInt]

@[simp]
theorem eval_intCast : ∀ {n : ℕ} (x : ℤ) (vars : Fin n → K),
    eval (x : PolyAux n) vars = x :=
  eval_ofInt

instance {n : ℕ} : Zero (PolyAux n) := ⟨(0 : ℤ)⟩

theorem zero_def : (0 : PolyAux n) = ofInt 0 := rfl

@[simp]
theorem eval_zero {n : ℕ} (vars : Fin n → K) :
    eval (0 : PolyAux n) vars = 0 := by
  erw [eval_intCast 0]; simp

inductive Good : ∀ {n : ℕ}, PolyAux n → Prop
  | ofInt : ∀ (x : ℤ), Good (ofInt' x)
  | const : ∀ {p}, Good p → Good (const p)
  | constAddXMul : ∀ {p q}, Good p → Good q → q ≠ 0 → Good (constAddXMul p q)

instance {n : ℕ} : One (PolyAux n) := ⟨(1 : ℤ )⟩

theorem one_def : (1 : PolyAux n) = ofInt 1 := rfl

@[simp]
theorem eval_one {n : ℕ} (vars : Fin n → K) :
    eval (1 : PolyAux n) vars = 1 := by
  erw [eval_intCast 1]; simp

theorem ofInt_injective : ∀ {n : ℕ}, Function.Injective (@ofInt n)
  | 0, x, y, h => by injection h
  | n+1, x, y, h => by
    rw [ofInt] at h
    injection h with _ h
    exact ofInt_injective h

def constAddXMul' {n : ℕ} (p : PolyAux n) (q : PolyAux (n + 1)) : PolyAux (n+1) :=
  if q = 0 then const p else constAddXMul p q

@[simp]
theorem eval_constAddXMul' {n : ℕ} (p : PolyAux n) (q : PolyAux (n + 1)) (vars : Fin (n+1) → K) :
    eval (constAddXMul' p q) vars = p.eval (fun i => vars i.succ) + vars 0 * q.eval vars := by
  simp [constAddXMul']
  split_ifs <;>
  simp_all [eval]

theorem apply_eval {S : Type*} [CommRing S] (f : K →+* S) (vars : Fin n → K) (p : PolyAux n) :
    f (p.eval vars) = p.eval (fun i => f (vars i)) := by
  induction p <;> simp_all


def add : {n : ℕ} → PolyAux n → PolyAux n → PolyAux n
  | _, ofInt' x, ofInt' y => ofInt' (x + y)
  | _, const p, const q => const (add p q)
  | _, const p, constAddXMul q r => constAddXMul (add p q) r
  | _, constAddXMul p q, const r => constAddXMul (add p r) q
  | _, constAddXMul p q, constAddXMul r s => constAddXMul' (add p r) (add q s)

instance {n : ℕ} : Add (PolyAux n) := ⟨PolyAux.add⟩

@[simp]
theorem eval_add' : {n : ℕ} → (p : PolyAux n) → (q : PolyAux n) → (vars : Fin n → K) →
    eval (p.add q) vars = p.eval vars + q.eval vars
  | _, ofInt' x, ofInt' y => by simp
  | _, const p, const q => by simp [eval_add' p q]
  | _, const p, constAddXMul q r => by simp [eval_add' p q, add_comm, add_assoc, add_left_comm, add]
  | _, constAddXMul p q, const r => by simp [eval_add' p r, add_comm, add_assoc, add_left_comm, add]
  | _, constAddXMul p q, constAddXMul r s => by
    simp [eval_add' p r, eval_add' q s, add_comm, add_assoc, add_left_comm, mul_add, add]

@[simp]
theorem eval_add : {n : ℕ} → (p : PolyAux n) → (q : PolyAux n) → (vars : Fin n → K) →
    eval (p + q) vars = p.eval vars + q.eval vars :=
  eval_add'

theorem add_def {n : ℕ} (p q : PolyAux n) : p + q = p.add q := rfl

def mul : {n : ℕ} → PolyAux n → PolyAux n → PolyAux n
  | _, ofInt' x, ofInt' y => ofInt' (x * y)
  | _, const p, const q => const (mul p q)
  | _, const p, constAddXMul q r => constAddXMul' (mul p q) (mul (const p) r)
  | _, constAddXMul p q, const r => constAddXMul' (mul p r) (mul q (const r))
  | n+1, constAddXMul p q, constAddXMul r s =>
    constAddXMul' (mul p r) (add (add (mul (const p) s) (mul q (const r)))
      (constAddXMul' 0 (mul q s)))
  termination_by n p q => (n, sizeOf p + sizeOf q)

instance {n : ℕ} : Mul (PolyAux n) := ⟨PolyAux.mul⟩

@[simp]
theorem eval_mul' : {n : ℕ} → (p : PolyAux n) → (q : PolyAux n) → (vars : Fin n → K) →
    eval (p.mul q) vars = p.eval vars * q.eval vars
  | _, ofInt' x, ofInt' y, _ => by simp [mul]
  | _, const p, const q, _ => by simp [eval_mul' p q, mul]
  | _, const p, constAddXMul q r, _ => by
    simp [eval_mul' p q, eval_mul' (const p) r, mul]; ring
  | _, constAddXMul p q, const r, _ => by
    simp [eval_mul' p r, eval_mul' q (const r), mul]; ring
  | _+1, constAddXMul p q, constAddXMul r s, _ => by
    simp [eval_mul' p r, eval_mul' (const p) s, eval_mul' q (const r), eval_mul' q s, mul]
    ring
  termination_by n p q => (n, sizeOf p + sizeOf q)

@[simp]
theorem eval_mul : {n : ℕ} → (p : PolyAux n) → (q : PolyAux n) → (vars : Fin n → K) →
    eval (p * q) vars = p.eval vars * q.eval vars :=
  eval_mul'

def neg : {n : ℕ} → (p : PolyAux n) → PolyAux n
  | _, ofInt' x => ofInt' (-x)
  | _, const p => const (neg p)
  | _, constAddXMul p q => constAddXMul (neg p) (neg q)

instance {n : ℕ} : Neg (PolyAux n) := ⟨PolyAux.neg⟩

theorem neg_const {n : ℕ} (p : PolyAux n) :
    -const p = const (-p) := rfl

theorem neg_def {n : ℕ} (p : PolyAux n) : -p = p.neg := rfl

@[simp]
theorem constAddXMul_neg {n : ℕ} (p : PolyAux n) (q : PolyAux (n+1)) :
    -constAddXMul p q = constAddXMul (-p) (-q) := rfl

@[simp]
theorem eval_neg' {n : ℕ} (p : PolyAux n) : (vars : Fin n → K) →
    eval (neg p) vars = -p.eval vars := by
  induction p <;> simp_all [eval, add_comm]

@[simp]
theorem eval_neg {n : ℕ} (p : PolyAux n) : (vars : Fin n → K) →
    eval (-p) vars = -p.eval vars :=
  eval_neg' p

instance : Sub (PolyAux n) := ⟨fun p q => p + -q⟩

@[simp]
theorem eval_sub {n : ℕ} (p q : PolyAux n) (vars : Fin n → K) :
    eval (p - q) vars = p.eval vars - q.eval vars :=
  (eval_add p (-q) vars).trans <| by simp [sub_eq_add_neg]

theorem good_ofInt {z : ℤ} : Good (ofInt z : PolyAux n) := by
  induction n <;> simp [ofInt] <;> constructor; assumption

def leadingCoeff : ∀ {n : ℕ}, PolyAux (n+1) → PolyAux n
  | _, const p => p
  | _, constAddXMul _ q => leadingCoeff q

theorem good_leadingCoeff : ∀ {n : ℕ} {p : PolyAux (n+1)} (_h : Good p), Good (leadingCoeff p)
  | _, const _, h => by cases h; simp [leadingCoeff]; assumption
  | _, constAddXMul _ q, h => by
    cases h
    rw [leadingCoeff]
    exact good_leadingCoeff (by assumption)

theorem good_constAddXMul' {n : ℕ} {p : PolyAux n} (q : (PolyAux (n+1)))
    (hp : Good p) (hq : Good q) : Good (constAddXMul' p q) := by
  rw [constAddXMul']
  split_ifs with hq0
  · constructor; assumption
  · constructor <;> assumption

def eraseLead : ∀ {n : ℕ}, PolyAux n → PolyAux n
  | _, ofInt' _ => 0
  | _, const _ => 0
  | _, constAddXMul p q => constAddXMul' p (eraseLead q)

theorem good_eraseLead : ∀ {n : ℕ} {p : PolyAux n} (_h : Good p), Good (eraseLead p)
  | _, ofInt' _, h => by constructor
  | _, const _, h => good_ofInt
  | _, constAddXMul p q, h => by
    cases h
    simp [eraseLead]
    exact good_constAddXMul' _ (by assumption) (good_eraseLead (by assumption))

open Mathlib Mathlib.Vector

def leadingMon : ∀ {n : ℕ}, PolyAux n → Vector ℕ n
  | _, ofInt' _ => Vector.nil
  | _, const p => 0 ::ᵥ leadingMon p
  | _, constAddXMul _ q =>
    match leadingMon q with
    | ⟨n :: l, h⟩ => ⟨(n+1) :: l, h⟩

@[simp]
def degree : ∀ {n : ℕ}, PolyAux n → WithBot ℕ
  | _, ofInt' x => if x = 0 then ⊥ else 0
  | _, const p => if p = 0 then ⊥ else 0
  | _, constAddXMul _ q => degree q + 1

theorem degree_nonneg_iff_ne_zero : ∀ {n : ℕ} (p : PolyAux n) (_hp : p.Good), 0 ≤ p.degree ↔ p ≠ 0
  | _, ofInt' x, _ => by
    simp [degree]
    split_ifs
    · simp_all
      rfl
    · simp
      intro h
      injection h; simp_all
  | _, const p, _ => by
    simp [degree]
    split_ifs
    · simp_all
      rfl
    · simp
      intro h
      injection h
      simp_all
      contradiction
  | _, constAddXMul _ q, h => by
    simp [zero_def, ofInt]
    refine add_nonneg ?_ zero_le_one
    rw [degree_nonneg_iff_ne_zero q]
    cases h
    assumption
    cases h
    assumption

@[simp]
def natDegree {n : ℕ} (p : PolyAux n) : ℕ := p.degree.unbot' 0

def deriv : ∀ {n : ℕ}, PolyAux (n + 1) → PolyAux (n + 1)
  | _, constAddXMul _ q => q + constAddXMul' 0 (deriv q)
  | _, _ => 0

def X : ∀ {n : ℕ}, Fin n → PolyAux n
  | _+1, ⟨0, _⟩ => constAddXMul 0 1
  | _+1, ⟨i+1, h⟩ => const (X ⟨i, Nat.lt_of_succ_lt_succ h⟩)


@[simp]
theorem eval_X : ∀ {n : ℕ}  (i : Fin n) (vars : Fin n → K),
    eval (X i) vars = vars i
  | _+1, ⟨0, _⟩ => by simp
  | _+1, ⟨i+1, h⟩ => by simp [eval_X]

instance {n : ℕ} : NatPow (PolyAux n) := ⟨fun p n => (.*p)^[n] 1⟩

@[simp]
theorem eval_pow {n : ℕ} (p : PolyAux n) (m : ℕ) (vars : Fin n → K) :
    eval (p^m) vars = p.eval vars ^ m := by
  induction m with
  | zero => rw [pow_zero]; exact eval_one vars
  | succ m ih =>
    rw [pow_succ, ← ih, ← eval_mul]
    show ((.*p)^[m+1] 1).eval vars = _
    rw [Function.iterate_succ']
    simp only [Function.comp_apply, eval_mul]
    rfl

-- @[simp]
-- theorem eval_eraseLead : ∀ {n : ℕ} (p : PolyAux (n+1)) (vars : Fin (n+1) → K),
--      p.eraseLead.eval vars = p.eval vars - p.leadingCoeff.eval (fun i => vars i.succ) * vars 0 ^ p.natDegree
--   | _, const _, _ => by simp [natDegree, eraseLead, leadingCoeff]
--   | _, constAddXMul p q, _ => by
--     simp only [eraseLead, leadingCoeff, eval, eval_constAddXMul', natDegree]
--     rw [eval_eraseLead]
--     ring

-- theorem natDegree_pos_of_eraseLead_ne_zero : ∀ {n : ℕ} {p : PolyAux n}, p.eraseLead ≠ 0 → 0 < p.natDegree
--   | _, ofInt' _ => by simp [eraseLead]
--   | _, const _ => by simp [eraseLead]
--   | _, constAddXMul _ _ => by simp [natDegree, eraseLead]

-- theorem natDegree_eraseLead : ∀ {n : ℕ} (p : PolyAux n), natDegree (eraseLead p) ≤ natDegree p - 1
--   | _, ofInt' _ => by simp [natDegree]
--   | _, const _ => by simp [natDegree]
--   | _, constAddXMul p q => by
--     rw [natDegree, eraseLead, constAddXMul']
--     split_ifs with hq0
--     · simp [natDegree]
--     · simp only [natDegree, add_tsub_cancel_right]
--       refine le_trans (Nat.succ_le_succ (natDegree_eraseLead q)) ?_
--       rw [← Nat.succ_sub (Nat.succ_le.2 (natDegree_pos_of_eraseLead_ne_zero hq0))]
--       simp

@[simp]
theorem neg_eq_zero {n : ℕ} {p : PolyAux n} : p.neg = 0 ↔ p = 0 := by
  induction p <;> simp_all [neg, zero_def, ofInt]

@[simp]
theorem degree_neg : ∀ {n : ℕ} (p : PolyAux n), (-p).degree = p.degree
  | _, ofInt' _ => by simp [degree]
  | _, const _ => by simp [degree]
  | _, constAddXMul p q => by
    rw [degree, ← degree_neg q]
    rfl

@[simp]
theorem leadingCoeff_neg : ∀ {n : ℕ} (p : PolyAux (n+1)), (-p).leadingCoeff = -p.leadingCoeff
  | _, const _ => by rw [leadingCoeff, neg_const, leadingCoeff]
  | _, constAddXMul p q => by
    rw [leadingCoeff, ← leadingCoeff_neg, constAddXMul_neg, leadingCoeff]

def mulConstMulXPow : ∀ {n : ℕ} (p : PolyAux n) (m : ℕ) (q : PolyAux (n+1)), PolyAux (n+1)
  | _, p, 0, const q => const (p * q)
  | _, p, 0, constAddXMul q r => constAddXMul (p * q) (mulConstMulXPow p 0 r)
  | _, p, m+1, q => constAddXMul 0 (mulConstMulXPow p m q)

@[simp]
theorem leadingCoeff_mulConstMulXPow : ∀ {n : ℕ} (p : PolyAux n) (m : ℕ) (q : PolyAux (n+1)),
    leadingCoeff (mulConstMulXPow p m q) = p * leadingCoeff q
  | _, p, 0, const q => by simp [mulConstMulXPow, leadingCoeff]
  | _, p, 0, constAddXMul q r => by
    simp only [mulConstMulXPow, leadingCoeff, constAddXMul']

    rw [leadingCoeff_mulConstMulXPow]
  | _, p, m+1, q => by
    simp only [mulConstMulXPow, leadingCoeff]
    rw [leadingCoeff_mulConstMulXPow]

-- @[simp]
-- theorem natDegree_mulConstMulXPow : ∀ {n : ℕ} (p : PolyAux n) (m : ℕ) (q : PolyAux (n+1)),
--      natDegree (mulConstMulXPow p m q) = natDegree q + m
--   | _, p, 0, const q => by simp [natDegree, mulConstMulXPow]
--   | _, p, 0, constAddXMul q r => by
--     rw [natDegree, mulConstMulXPow, natDegree, natDegree_mulConstMulXPow]
--   | _, p, m+1, q => by
--     rw [mulConstMulXPow, natDegree, natDegree_mulConstMulXPow, add_assoc]

theorem eval_mulConstMulXPow : ∀ {n : ℕ} (p : PolyAux n) (m : ℕ) (q : PolyAux (n+1)) (vars : Fin (n+1) → K),
    eval (mulConstMulXPow p m q) vars = eval p (fun i => vars i.succ) * vars 0 ^ m * eval q vars
  | _, p, 0, const q, _=> by simp [mulConstMulXPow]
  | _, p, 0, constAddXMul q r, _ => by
    simp only [mulConstMulXPow, eval, eval_mul]
    rw [eval_mulConstMulXPow]
    ring
  | _, p, m+1, q, _ => by
    simp only [mulConstMulXPow, eval, eval_mul, eval_zero]
    rw [eval_mulConstMulXPow, pow_succ]
    ring

open Good

theorem good_add : ∀ {n : ℕ} {p q : PolyAux n}, Good p → Good q → Good (p.add q)
  | _, ofInt' x, ofInt' y, _, _ => by constructor
  | _, const p, const q, Good.const hp, Good.const hq => by
     constructor; exact good_add hp hq
  | _, const p, constAddXMul q r, Good.const hp, Good.constAddXMul hq hr hr0 => by
    constructor
    apply good_add
    all_goals {assumption}
  | _, constAddXMul p q, const r, Good.constAddXMul hp hq hq0, Good.const hr => by
    constructor
    apply good_add
    all_goals {assumption}
  | _, constAddXMul p q, constAddXMul r s, Good.constAddXMul hp hq hq0,
      Good.constAddXMul hr hs hs0 => by
    simp only [add, constAddXMul']
    split_ifs
    · constructor; apply good_add; all_goals {assumption}
    · constructor
      apply good_add hp hr
      apply good_add hq hs
      all_goals {assumption}

@[simp]
theorem ofInt'_eq_zero {x : ℤ} : ofInt' x = 0 ↔ x = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    cases h
    rfl
  · rintro rfl; rfl

@[simp]
theorem const_eq_zero {p : PolyAux n} : const p = 0 ↔ p = 0 := by
  induction p <;> simp_all [zero_def, ofInt]

@[simp]
theorem constAddXMul_ne_zero {p : PolyAux n} {q : PolyAux (n+1)} :
    constAddXMul p q ≠ 0 := by
  simp [zero_def]
  cases n <;> simp [ofInt]



theorem good_neg {n : ℕ} {p : PolyAux n} (h : Good p) : Good p.neg := by
  induction p <;> cases h <;> constructor <;> simp_all



@[simp]
theorem ofInt_add {x y : ℤ} : (ofInt (x + y) : PolyAux n) = ofInt x + ofInt y := by
  induction n with
  | zero => simp [ofInt, add_def, add]
  | succ n ih => simp [ofInt, add_def, add, ih]

@[simp]
theorem ofInt_neg {x : ℤ} : (ofInt (-x) : PolyAux n) = -ofInt x := by
  induction n with
  | zero => simp [ofInt, neg_def, neg]
  | succ n ih => simp [ofInt, neg_def, neg, ih]

theorem good_mul : ∀ {n : ℕ} {p q : PolyAux n}, Good p → Good q → Good (p.mul q)
  | _, ofInt' x, ofInt' y, _, _ => by simp [mul]; constructor
  | _, const p, const q, Good.const hp, Good.const hq => by
     simp [mul]; constructor; exact good_mul hp hq
  | _, const p, constAddXMul q r, Good.const hp, Good.constAddXMul hq hr hr0 => by
    simp [mul, constAddXMul']
    split_ifs
    · constructor
      exact good_mul hp hq
    · constructor
      exact good_mul hp hq
      exact good_mul (by constructor; exact hp) hr
      all_goals {assumption}
  | _, constAddXMul p q, const r, Good.constAddXMul hp hq hq0, Good.const hr => by
    simp [mul, constAddXMul']
    split_ifs
    · constructor
      exact good_mul hp hr
    · constructor
      exact good_mul hp hr
      exact good_mul hq (by constructor; exact hr)
      all_goals {assumption}
  | _, constAddXMul p q, constAddXMul r s, Good.constAddXMul hp hq hq0,
      Good.constAddXMul hr hs hs0 => by
    simp only [mul, constAddXMul']
    split_ifs
    · constructor; exact good_mul hp hr
    · constructor
      exact good_mul hp hr
      exact good_add (good_add (good_mul (Good.const hp) hs)
        (good_mul hq (Good.const hr))) good_ofInt
      assumption
    · exact Good.const (good_mul hp hr)
    · constructor
      exact good_mul hp hr
      exact good_add (good_add (good_mul (Good.const hp) hs)
        (good_mul hq (Good.const hr))) (Good.constAddXMul good_ofInt (good_mul hq hs)
          (by assumption))
      assumption
  termination_by n p q => (n, sizeOf p + sizeOf q)

theorem good_X : ∀ {n : ℕ} (i : Fin n), Good (X i : PolyAux n)
  | _+1, ⟨0, _⟩ => by
    rw [X]; constructor <;> try { apply good_ofInt }
    rw [zero_def, one_def, Ne, ofInt_injective.eq_iff]
    simp
  | _+1, ⟨i+1, h⟩ => by
    simp only [X]
    constructor
    apply good_X

theorem good_deriv : ∀ {n : ℕ} {p : PolyAux (n+1)} (_h : Good p), Good (deriv p)
  | _, constAddXMul _ q, h => by
    cases h
    simp [deriv]
    exact good_add (by assumption) (good_constAddXMul' _ (good_ofInt) (good_deriv (by assumption)))
  | _, const _, h => by
    cases h
    simp [deriv]
    exact good_ofInt

-- theorem good_mulConstMulXPow  : ∀ {n : ℕ} {p : PolyAux n} {m : ℕ} {q : PolyAux (n+1)},
--     Good p → Good q → Good (mulConstMulXPow p m q)
--   | _, p, 0, const q, hp, hq => by
--     simp [mulConstMulXPow]
--     exact Good.const <| good_mul hp (by cases hq; assumption)
--   | _, p, 0, constAddXMul q r, hp, hq => by
--     simp [mulConstMulXPow]
--     exact Good.constAddXMul (good_mul hp (by cases hq; assumption))
--       (good_mulConstMulXPow hp (by cases hq; assumption))
--       sorry
--   | _, p, m+1, q, hp, hq => by
--     simp [mulConstMulXPow]
--     exact Good.constAddXMul good_ofInt (good_mulConstMulXPow hp hq) _

theorem eq_of_sub_eq_zero : ∀ {n : ℕ} {p q : PolyAux n}, Good p → Good q →
    p.add q.neg = 0 → p = q
  | _, ofInt' x, ofInt' y, _, _ => by simp [add, neg, add_neg_eq_zero]
  | _, const p, const q, Good.const hp, Good.const hq => by
     simp only [add, neg, zero_def, ofInt]
     intro h
     injection h with _ h
     rw [eq_of_sub_eq_zero hp hq h]
  | _, const p, constAddXMul q r, Good.const hp, Good.constAddXMul hq hr hr0 => by
     simp [add, neg]
  | _, constAddXMul p q, const r, Good.constAddXMul hp hq hq0, Good.const hr => by
    simp [add, neg]
  | _, constAddXMul p q, constAddXMul r s, Good.constAddXMul hp hq hq0,
      Good.constAddXMul hr hs hs0 => by
    intro h
    simp only [add, constAddXMul'] at *
    split_ifs at h with h1
    · rw [eq_of_sub_eq_zero hq hs h1]
      rw [zero_def, ofInt] at h
      injection h with _ h
      rw [eq_of_sub_eq_zero hp hr h]
    · cases h

theorem eval_eq_zero : ∀ {n : ℕ} {p : PolyAux n}, Good p →
    p.eval (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)) = 0 →
    p = 0
  | _, ofInt' x, h => by simp
  | n+1, const p, Good.const hp => by
    intro h
    apply_fun MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin (n+1) => Fin.cases
      (0 : MvPolynomial (Fin n) ℤ) (MvPolynomial.X) i) at h
    simp only [apply_eval] at h
    simp only [eval, MvPolynomial.eval₂Hom_X', Fin.cases_succ, map_zero] at h
    rw [eval_eq_zero hp h]
    rfl
  | n+1,  constAddXMul p q, Good.constAddXMul hp hq h0 => by
    intro h
    simp at h
    apply_fun MvPolynomial.eval₂Hom (Int.castRingHom _ : ℤ →+* (Polynomial (MvPolynomial (Fin n) ℤ)))
      (fun i : Fin (n+1) => Fin.cases Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i)) i) at h
    simp only [apply_eval, MvPolynomial.eval₂Hom_X', Fin.cases_succ, map_add, map_mul,
      Fin.cases_zero] at h
    simp only [← apply_eval] at h
    apply_fun Polynomial.divX at h
    simp only [Polynomial.divX_C, Polynomial.divX_add, zero_add] at h
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_zero, Polynomial.divX_zero] at h
    rw [Polynomial.divX_eq_zero_iff] at h
    simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, map_zero, mul_eq_zero,
      Polynomial.X_ne_zero, false_or] at h
    apply_fun Polynomial.eval₂RingHom (MvPolynomial.rename (Fin.succ : Fin n → Fin (n+1))).toRingHom
      (MvPolynomial.X 0) at h
    simp only [apply_eval] at h
    simp at h
    exfalso
    apply h0
    apply eval_eq_zero hq
    convert h using 2
    funext i
    induction i using Fin.cases <;> simp

theorem eval_injective {n : ℕ} {p q : PolyAux n} (hp : Good p) (hq : Good q)
    (h : p.eval (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)) =
    q.eval (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))) : p = q := by
  apply eq_of_sub_eq_zero hp hq
  erw [← sub_eq_zero, ← eval_sub] at h
  exact eval_eq_zero (good_add hp (good_neg hq)) h

end PolyAux

def Poly (n : ℕ) : Type := { p : PolyAux n // p.Good }

instance (n : ℕ) : DecidableEq (Poly n) := by dsimp [Poly]; infer_instance

namespace Poly

section CommRing

open PolyAux

variable {n : ℕ}

instance : IntCast (Poly n) := ⟨fun x => ⟨PolyAux.ofInt x, good_ofInt⟩⟩

instance : NatCast (Poly n) := ⟨fun x => ⟨PolyAux.ofInt x, good_ofInt⟩⟩

instance : Zero (Poly n) := ⟨(0 : ℤ)⟩

instance : One (Poly n) := ⟨(1 : ℤ)⟩

instance : Add (Poly n) := ⟨fun x y => ⟨x.1 + y.1, good_add x.2 y.2⟩⟩

instance : Mul (Poly n) := ⟨fun x y => ⟨x.1 * y.1, good_mul x.2 y.2⟩⟩

instance : Neg (Poly n) := ⟨fun x => ⟨-x.1, good_neg x.2⟩⟩

def X : Fin n → Poly n := fun i => ⟨PolyAux.X i, good_X i⟩

@[simp]
theorem val_add (x y : Poly n) : ((x + y).val : PolyAux n) = x.1 + y.1 := rfl

@[simp]
theorem val_mul (x y : Poly n) : ((x * y).val : PolyAux n) = x.1 * y.1 := rfl

@[simp]
theorem val_neg (x : Poly n) : ((-x).val : PolyAux n) = -x.1 := rfl

@[simp]
theorem val_X (i : Fin n) : ((X i).val : PolyAux n) = PolyAux.X i := rfl

@[simp]
theorem val_zero : ((0 : Poly n).val : PolyAux n) = 0 := rfl

@[simp]
theorem val_one : ((1 : Poly n).val : PolyAux n) = 1 := rfl

@[simp]
theorem val_eq_zero {x : Poly n} : x.1 = 0 ↔ x = 0 := by
  rw [← Subtype.val_injective.eq_iff]; rfl

@[simp]
theorem val_ne_zero (x : Poly n) : x.1 ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, val_eq_zero]

private noncomputable def ringEquivMvPolyAux : Poly n ≃+* MvPolynomial (Fin n) ℤ where
  toEquiv := Equiv.ofBijective (fun p => p.1.eval (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))) <| by
    refine ⟨fun p q h => ?_, fun f => ?_⟩
    · apply Subtype.ext
      apply eq_of_sub_eq_zero p.2 q.2
      erw [← sub_eq_zero, ← eval_sub] at h
      exact eval_eq_zero (p + -q).2 h
    · induction f using MvPolynomial.induction_on with
      | h_C x => exact ⟨⟨x, good_ofInt⟩, by simp⟩
      | h_add f g ihf ihg =>
        use Exists.choose ihf + Exists.choose ihg
        dsimp only
        erw [eval_add]
        conv_rhs => rw [← Exists.choose_spec ihf, ← Exists.choose_spec ihg]
      | h_X f i ih =>
        simp only
        use Exists.choose ih * X i
        dsimp only
        erw [eval_mul, eval_X]
        conv_rhs => rw [← Exists.choose_spec ih]
  map_mul' := by intros; exact eval_mul _ _ _
  map_add' := by intros; exact eval_add _ _ _

instance : CommRing (Poly n) where
  add_assoc a b c := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [add_assoc]
  add_comm a b := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [add_comm]
  add_zero a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [add_zero, ringEquivMvPolyAux]
  zero_add a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [zero_add, ringEquivMvPolyAux]
  left_distrib a b c := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [left_distrib]
  right_distrib a b c := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [right_distrib]
  zero_mul a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [zero_mul, ringEquivMvPolyAux]
  mul_zero a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [mul_zero, ringEquivMvPolyAux]
  mul_assoc a b c := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [mul_assoc]
  one_mul a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [one_mul, ringEquivMvPolyAux]
  mul_one a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [mul_one, ringEquivMvPolyAux]
  mul_comm a b := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [mul_comm]
  neg_add_cancel a := by
    apply ringEquivMvPolyAux.toEquiv.injective
    simp [neg_add_cancel, ringEquivMvPolyAux]
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast_succ a := by
    simp [Nat.succ_eq_add_one, NatCast.natCast]
    rfl
  intCast_negSucc a := by
    apply Subtype.ext
    simp only [IntCast.intCast, Int.negSucc_eq, Int.reduceNeg, ofInt_add,
      ofInt_neg, NatCast.natCast, Nat.cast]
    simp

instance : IsDomain (Poly n) := Equiv.isDomain ringEquivMvPolyAux

instance : UniqueFactorizationMonoid (Poly n) :=
  (MulEquiv.uniqueFactorizationMonoid_iff ringEquivMvPolyAux.toMulEquiv).2 inferInstance


end CommRing

section defs

variable {n : ℕ} {R : Type*} [CommRing R]

def eval (vars : Fin n → R) : Poly n →+* R where
  toFun := fun p => p.1.eval vars
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

theorem apply_eval {S : Type*} [CommRing S] (f : R →+* S) (vars : Fin n → R) (p : Poly n) :
    f (p.eval vars) = p.eval (fun i => f (vars i)) :=
  PolyAux.apply_eval _ _ _

@[simp]
theorem eval_X (i : Fin n) (vars : Fin n → R) : eval vars (X i) = vars i := by
  simp [eval, val_X]

noncomputable def toMvPoly {n : ℕ} : Poly n ≃+* MvPolynomial (Fin n) ℤ where
  toFun := eval MvPolynomial.X
  invFun := MvPolynomial.eval₂Hom (Int.castRingHom _) X
  left_inv := Function.rightInverse_of_injective_of_leftInverse
    (fun p q h => Subtype.ext (PolyAux.eval_injective p.2 q.2 h))
    (fun p => by induction p using MvPolynomial.induction_on <;> simp_all)
  right_inv := fun p => by
    induction p using MvPolynomial.induction_on <;> simp_all
  map_mul' := by simp
  map_add' := by simp

theorem eval_X' (p : Poly n) : p.eval X = p := by
  apply toMvPoly.injective
  erw [apply_eval toMvPoly.toRingHom]
  simp [toMvPoly]

@[ext high]
theorem hom_ext {f g : Poly n →+* R} (h : ∀ i, f (X i) = g (X i)) : f = g := by
  ext p
  rw [← eval_X' p, apply_eval, apply_eval]
  simp only [h]

noncomputable def toPoly : Poly (n+1) ≃+* Polynomial (MvPolynomial (Fin n) ℤ) :=
  RingEquiv.ofHomInv
    (eval (Fin.cons Polynomial.X (fun i : Fin n => Polynomial.C (MvPolynomial.X i))) :
       _ →+* Polynomial (MvPolynomial (Fin n) ℤ))
    (Polynomial.eval₂RingHom
       (MvPolynomial.eval₂Hom (Int.castRingHom _) (fun i => X i.succ)) (X 0))
    (hom_ext (fun i => by induction i using Fin.cases <;> simp))
    (Polynomial.ringHom_ext' (MvPolynomial.ringHom_ext (by simp) (by simp)) (by simp))

def const : Poly n →+* Poly (n+1) where
  toFun := fun p => ⟨PolyAux.const p.1, PolyAux.Good.const p.2⟩
  map_one' := rfl
  map_mul' x y := by
    apply Subtype.ext
    cases x; cases y
    simp [val_mul, val_add, val_one, val_zero]
    simp [HMul.hMul]
    simp [Mul.mul, PolyAux.mul]
  map_add' x y := by
    apply Subtype.ext
    cases x; cases y
    simp [val_mul, val_add, val_one, val_zero]
    simp [HAdd.hAdd]
    simp [Add.add, PolyAux.add]
  map_zero' := rfl

@[simp]
theorem eval_const (vars : Fin (n+1) → R) (p : Poly n) :
    eval vars p.const = eval (fun i => vars i.succ) p := rfl

@[simp]
theorem const_X (i : Fin n) : const (X i) = X i.succ := by
  apply Subtype.ext
  simp [const, X, PolyAux.X]

theorem const_eq_eval : @const n = eval (fun i => X i.succ) := by
  ext
  rw [eval_X, const_X]

def constAddXMul {n : ℕ} (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) : Poly (n+1) :=
  ⟨PolyAux.constAddXMul p.1 q.1, PolyAux.Good.constAddXMul p.2 q.2 (by
    intro h
    cases q
    simp_all
    exact hq0 rfl)⟩

@[simp]
theorem eval_constAddXMul (vars : Fin (n+1) → R) (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) :
    eval vars (constAddXMul p q hq0) = eval vars p.const + vars 0 * eval vars q := rfl

theorem toPoly_const (p : Poly n) : toPoly (const p) = Polynomial.C (toMvPoly p) :=
  show (toPoly.toRingHom.comp const) p = Polynomial.C.comp toMvPoly.toRingHom p from
    RingHom.congr_fun (hom_ext (by simp [toPoly, toMvPoly])) _

@[recursor 2]
def recOnAux : ∀ {n : ℕ} {C : ∀ {n : ℕ}, Poly n → Sort*} (p : PolyAux n) (hp : p.Good)
    (_ofInt : ∀ x : ℤ, C (x : Poly 0))
    (_const : ∀ {n} (p : Poly n), C p → C (const p))
    (_constAddXMul : ∀ (n) (p : Poly n) (q : Poly (n+1)) (hq : q ≠ 0),
      C p → C q → C (constAddXMul p q hq)), C ⟨p, hp⟩
  | _, _, PolyAux.ofInt' x, _, ofInt, _, _ => ofInt x
  | _, _, PolyAux.const p, hp, oI, const, cX =>
    const ⟨p, by cases hp; assumption⟩ (recOnAux _ _ oI const cX)
  | _, _, PolyAux.constAddXMul p q, h, oI, oC, constAddXMul =>
    constAddXMul _ ⟨p, by cases h; assumption⟩ ⟨q, by cases h; assumption⟩ (by
    intro hq
    cases h with
    | constAddXMul _ _ hq0 =>
      apply_fun Subtype.val at hq
      simp_all) (recOnAux p _ oI oC constAddXMul) (recOnAux q _ oI oC constAddXMul)

@[recursor 2]
def recOn {n : ℕ} {C : ∀ {n : ℕ}, Poly n → Sort*} (p : Poly n) (_ofInt : ∀ x : ℤ, C (x : Poly 0))
    (_const : ∀ {n} (p : Poly n), C p → C (const p))
    (_constAddXMul : ∀ (n) (p : Poly n) (q : Poly (n+1)) (hq : q ≠ 0),
      C p → C q → C (constAddXMul p q hq)) : C p :=
  recOnAux p.1 p.2 _ofInt _const _constAddXMul

@[recursor 1]
def recOnSucc  {n : ℕ} {C : ∀ {n : ℕ}, Poly (n+1) → Sort*} (p : Poly (n+1))
    (const : ∀ {n} (p : Poly n), C (const p))
    (constAddXMul : ∀ (n) (p : Poly n) (q : Poly (n+1)) (hq : q ≠ 0),
      C q → C (constAddXMul p q hq)) : C p :=
  @recOn (n + 1) (fun {k} p => ∀ (h : n + 1 = k), C (h ▸ p)) p (fun _ h => False.elim (by simp at h))
    (fun _ _ h => (Nat.succ_injective h).symm ▸ const _)
    (fun _ _ _ _ _ ih h => by
      cases Nat.succ_injective h
      exact constAddXMul _ _ _ _ (ih rfl))
    rfl

def leadingCoeff {n : ℕ} (p : Poly (n+1)) : Poly n :=
  ⟨PolyAux.leadingCoeff p.1, PolyAux.good_leadingCoeff p.2⟩

def eraseLead {n : ℕ} (p : Poly n) : Poly n :=
  ⟨PolyAux.eraseLead p.1, PolyAux.good_eraseLead p.2⟩

def degree {n : ℕ} (p : Poly (n+1)) : WithBot ℕ := p.1.degree

def natDegree {n : ℕ} (p : Poly n) : ℕ := p.1.natDegree

theorem degree_nonneg_iff_ne_zero {n : ℕ} {p : Poly (n+1)} : 0 ≤ p.degree ↔ p ≠ 0 := by
  erw [(PolyAux.degree_nonneg_iff_ne_zero p.1 p.2), val_ne_zero]

theorem degree_toPoly {n : ℕ} (p : Poly (n+1)) : (toPoly p).degree = p.degree :=
  @recOnSucc n (fun p => (toPoly p).degree = p.degree) p
    (by
      intro n p
      by_cases hp : p = 0
      · subst hp; simp [degree]
      · have hp01 : toMvPoly p ≠ 0 := by
          rwa [Ne, RingEquiv.map_eq_zero_iff toMvPoly]
        rw [toPoly_const, Polynomial.degree_C hp01]
        show (0 : WithBot ℕ) = if _ then _ else _
        rw [if_neg]
        rwa [val_eq_zero])
    (by
      intro m p q hq ih
      simp [toPoly, degree] at *
      rw [← ih, add_comm, ← apply_eval]
      rw [Polynomial.degree_add_C, Polynomial.degree_mul, Polynomial.degree_X,
        add_comm]
      rw [Polynomial.degree_mul, Polynomial.degree_X, ih]
      refine add_pos_of_pos_of_nonneg zero_lt_one ?_
      rw [PolyAux.degree_nonneg_iff_ne_zero _ q.2]
      rwa [val_ne_zero])

def deriv {n : ℕ} (p : Poly (n+1)) : Poly (n+1) :=
  ⟨PolyAux.deriv p.1, PolyAux.good_deriv p.2⟩

@[simp]
theorem degree_neg {n : ℕ} (p : Poly (n+1)) : (-p).degree = p.degree := by
  rw [← degree_toPoly, map_neg, Polynomial.degree_neg, degree_toPoly]

theorem degree_add_le {n : ℕ} (p q : Poly (n+1)) : (p + q).degree ≤ max p.degree q.degree := by
  rw [← degree_toPoly, ← degree_toPoly, map_add, ← degree_toPoly]
  apply Polynomial.degree_add_le

theorem degree_sub_le {n : ℕ} (p q : Poly (n+1)) : (p - q).degree ≤ max p.degree q.degree := by
  rw [← degree_toPoly, ← degree_toPoly, map_sub, ← degree_toPoly]
  apply Polynomial.degree_sub_le

theorem degree_mul {n : ℕ} (p q : Poly (n+1)) : (p * q).degree = p.degree + q.degree := by
  rw [← degree_toPoly, ← degree_toPoly, map_mul, ← degree_toPoly]
  apply Polynomial.degree_mul

theorem degree_const_of_ne_zero {n : ℕ} {p : Poly n} (hp0 : p ≠ 0) : (const p : Poly (n+1)).degree = 0 := by
  simp [degree, *]

@[simp]
theorem leadingCoeff_const {n : ℕ} (p : Poly n) : leadingCoeff (const p) = p := by
  apply Subtype.ext
  simp [leadingCoeff, const, PolyAux.leadingCoeff]

@[simp]
theorem leadingCoeff_constAddXMul {n : ℕ} (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) :
    leadingCoeff (constAddXMul p q hq0) = q.leadingCoeff := by
  apply Subtype.ext
  simp [leadingCoeff, constAddXMul, PolyAux.leadingCoeff]

theorem Nat.WithBot.nonneg_iff_ne_bot (n : WithBot ℕ) : 0 ≤ n ↔ n ≠ ⊥ := by
  cases n
  · simp
  · simp [Nat.zero_le]

theorem leadingCoeff_toPoly {n : ℕ} (p : Poly (n+1)) : toMvPoly (leadingCoeff p) = Polynomial.leadingCoeff (toPoly p) :=
  @recOnSucc n (fun p => toMvPoly (leadingCoeff p) = Polynomial.leadingCoeff (toPoly p)) p
    (by
      intro n p
      simp [toPoly, ← apply_eval, toMvPoly])
    (by
      intro m p q hq ih
      simp only [toMvPoly, MvPolynomial.coe_eval₂Hom, RingEquiv.coe_mk, Equiv.coe_fn_mk, toPoly,
        RingEquiv.ofHomInv_apply, leadingCoeff_constAddXMul, eval_constAddXMul, eval_const,
        Fin.cons_succ, Fin.cons_zero] at *
      rw [ih]
      simp only [← apply_eval]
      rw [Polynomial.leadingCoeff_add_of_degree_lt, mul_comm, Polynomial.leadingCoeff_mul_X]
      refine lt_of_le_of_lt (Polynomial.degree_C_le) ?_
      rw [Polynomial.degree_mul, Polynomial.degree_X]
      refine add_pos_of_pos_of_nonneg zero_lt_one ?_
      rw [Nat.WithBot.nonneg_iff_ne_bot, Ne, Polynomial.degree_eq_bot]
      show toPoly _ ≠ _
      rwa [Ne, toPoly.map_eq_zero_iff])

theorem degree_sub_lt {n : ℕ} {p q : Poly (n+1)} (h : p.degree = q.degree) (hq0 : p ≠ 0)
    (h : p.leadingCoeff = q.leadingCoeff) : (p - q).degree < p.degree := by
  rw [← degree_toPoly, ← degree_toPoly, map_sub]
  apply Polynomial.degree_sub_lt
  · rwa [degree_toPoly, degree_toPoly]
  · rwa [Ne, toPoly.map_eq_zero_iff]
  · rw [← leadingCoeff_toPoly, ← leadingCoeff_toPoly, h]

theorem natDegree_toPoly {n : ℕ} (p : Poly (n+1)) : (toPoly p).natDegree = p.natDegree := by
  rw [natDegree, Polynomial.natDegree, degree_toPoly, PolyAux.natDegree]; rfl

theorem degree_eq_natDegree {n : ℕ} {p : Poly (n+1)} (hp0 : p ≠ 0) : p.degree = p.natDegree := by
  rw [← degree_toPoly, ← natDegree_toPoly]
  apply Polynomial.degree_eq_natDegree
  rwa [Ne, toPoly.map_eq_zero_iff]

@[simp]
theorem toPoly_X_zero {n : ℕ} : toPoly (X 0 : Poly (n+1)) = Polynomial.X := by
  simp [toPoly]

theorem degree_const_mul_X_pow {n : ℕ} {p : Poly n} (hp0 : p ≠ 0) (k : ℕ) :
    (const p * X 0 ^ k).degree = (k : WithBot ℕ) := by
  rw [← degree_toPoly, map_mul, map_pow, toPoly_X_zero, toPoly_const]
  rw [Polynomial.degree_C_mul_X_pow]
  rwa [Ne,toMvPoly.map_eq_zero_iff]

theorem const_injective : Function.Injective (@const n) := by
  intros p q h
  cases p; cases q;
  simp [const, Subtype.ext_iff] at h
  injection h with h
  injection h; simp_all

@[simp]
theorem const_eq_zero_iff {n : ℕ} (p : Poly n) : const p = 0 ↔ p = 0 :=
  map_eq_zero_iff _ const_injective

theorem C_toMvPoly (p : Poly n) : Polynomial.C (toMvPoly p) = toPoly (const p) := by
  simp [toMvPoly, toPoly, apply_eval]

@[simp]
theorem degree_zero : degree (0 : Poly (n+1)) = ⊥ := by
  induction n <;> simp_all [degree, PolyAux.ofInt]

end defs

variable {n : ℕ}

theorem modDiv_wf {p q : Poly (n+1)} (lp lq : Poly n) (h : q.degree ≤ p.degree) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    (const q.leadingCoeff * p - const p.leadingCoeff * X 0 ^ (p.natDegree - q.natDegree) * q).degree < p.degree := by
  have hp : leadingCoeff p ≠ 0 := by
    rwa [Ne, ← (@toMvPoly n).injective.eq_iff, leadingCoeff_toPoly, map_zero,
      Polynomial.leadingCoeff_eq_zero, toPoly.map_eq_zero_iff]
  have hq : leadingCoeff q ≠ 0 := by
    rwa [Ne, ← (@toMvPoly n).injective.eq_iff, leadingCoeff_toPoly, map_zero,
      Polynomial.leadingCoeff_eq_zero, toPoly.map_eq_zero_iff]
  have hlt : natDegree q ≤ natDegree p :=
    (Nat.cast_le (α := WithBot ℕ)).1
      (by rw [← degree_eq_natDegree hp0, ← degree_eq_natDegree hq0]; exact h)
  refine lt_of_lt_of_le (degree_sub_lt ?_ ?_ ?_) ?_
  · rw [mul_comm, degree_mul, degree_mul, degree_const_mul_X_pow hp, degree_eq_natDegree hp0,
        degree_eq_natDegree hq0, ← Nat.cast_add, tsub_add_cancel_of_le hlt,
        degree_const_of_ne_zero hq, add_zero]
  · rw [mul_ne_zero_iff, Ne, const_eq_zero_iff]
    tauto
  · rw [← toMvPoly.injective.eq_iff, leadingCoeff_toPoly, leadingCoeff_toPoly,
       map_mul, toPoly_const, map_mul, map_mul,
       map_pow, toPoly_X_zero, mul_right_comm, Polynomial.leadingCoeff_mul_X_pow,
       Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, mul_comm, leadingCoeff_toPoly,
       toPoly_const, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
       leadingCoeff_toPoly]

theorem div_wf {p q : Poly (n+1)} (lp : Poly n) (h : q.degree ≤ p.degree)
    (hq0 : q.degree ≠ 0) :
    (p.eraseLead - (mulConstMulXPow lp (p.degree - q.degree) q).eraseLead).degree < p.degree := by
  refine lt_of_le_of_lt (degree_sub_le _ _) ?_
  simp only [max_lt_iff]
  refine ⟨lt_of_le_of_lt (degree_eraseLead _) ?_, lt_of_le_of_lt (degree_eraseLead _) ?_⟩
  . exact lt_of_lt_of_le (Nat.sub_lt_self zero_lt_one (le_trans (Nat.one_le_iff_ne_zero.2 hq0) h)) le_rfl
  · erw [degree_mulConstMulXPow, Nat.add_sub_cancel' h]
    exact Nat.sub_lt_self zero_lt_one (le_trans (Nat.one_le_iff_ne_zero.2 hq0) h)


/-- returns `n` such that `leadingCoeff q ^ n * p = h * q + r` -/
def pseudoModDiv : ∀ {n : ℕ} (p q : Poly (n+1)), (ℕ × Poly (n+1) ×
    {r : Poly (n+1) // q ≠ 0 → r.degree < q.degree}) :=
  fun p q =>
  let dp := natDegree p
  let dq := natDegree q
  let lp := p.leadingCoeff
  let lq := q.leadingCoeff
  if h : degree q ≤ degree p then
  if hp0 : p = 0 then (0, 0, ⟨0, by
    simp [WithBot.bot_lt_iff_ne_bot]
    rw [← Ne, ← degree_nonneg_iff_ne_zero]
    intro h h1
    rw [h1] at h
    simp at h⟩)
  else if hq0 : q = 0 then ⟨1, 0, ⟨0, by simp_all⟩⟩
  else
    let z := (const lp * X 0 ^ (dp - dq) * q)
    have wf := modDiv_wf lp lq h hp0 hq0
    let (n, h, r) := pseudoModDiv (const lq * p - z) q
    (n+1, h + const (lq ^ n * lp) * X 0 ^(dp - dq), r)
  else (0, 0, ⟨p, fun _ => lt_of_not_le h⟩)
  termination_by n p => (n+1, 1, degree p)


/-- returns `p / q` if it exists, otherwise nonsense -/
def divDvd : ∀ {n : ℕ} (_p _q : Poly n), Poly n
  | 0, ofInt' x, ofInt' y => ofInt (x.tdiv y)
  | _+1, const p, const q => const (divDvd p q)
  | _+1, constAddXMul p₁ p₂, const q => constAddXMul (divDvd p₁ q) (divDvd p₂ (const q))
  | _+1, p, constAddXMul q₁ q₂ =>
    let q := constAddXMul q₁ q₂
    let dp := degree p
    let dq := degree q
    let lp := p.leadingCoeff
    let lq := q.leadingCoeff
    let k := divDvd lp lq
    if h : degree q ≤ degree p then
    if hp0 : p = 0 then 0
    else
      have hq0 : q.degree ≠ 0 := by simp [q, degree]
      let z := (mulConstMulXPow k (dp - dq) q).eraseLead
      have wf := div_wf k h hq0
      let v := divDvd (p.eraseLead - z) q
      v + const k * X 0 ^ (dp - dq)
    else 0
  termination_by n p => (n, degree p)

instance : Div (Poly n) := ⟨divDvd⟩

theorem div_def {n : ℕ} (p q : Poly n) : p / q = divDvd p q := rfl

mutual

def contPrim : ∀ {n : ℕ} (p : Poly (n+1)), Poly n × Poly (n+1)
  | _, const p => (p, 1)
  | _, constAddXMul p q =>
    let (c, q') := contPrim q
    let g := gCd p c
    let a := g / p
    let b := g / c
    (g, const a + X 0 * const b * q')
  termination_by n p => (n+1, 0, sizeOf p)

-- This returns the gcd
def gCd : ∀ {n : ℕ} (_p _q : Poly n), Poly n
  | 0, ofInt' x, ofInt' y => (Int.gcd x y : ℤ)
  | n+1, p, q =>
    if hq0 : q = 0 then p
    else
      let (pc, pp) := contPrim p
      let (_, h, ⟨r, hr⟩) := pseudoModDiv pp q
      have _wf : (if (r : Poly (n+1)) = 0 then 0 else 1 + (r : Poly (n+1)).degree) <
          (if q = 0 then 0 else 1 + q.degree) := by
        split_ifs with hr0
        · simp_all
        · by_cases hq0 : q.degree = 0
          · simp_all
          · simp only [add_lt_add_iff_left]
            exact hr.1 (Nat.pos_iff_ne_zero.2 hq0)
      let g := gCd q r -- v.1 is `1` or `-1` so multiplying is dividing.
      g
  termination_by n _ q => (n, 2, if q = 0 then 0 else 1 + degree q)

end



noncomputable def polyToMvPoly : Polynomial (MvPolynomial (Fin n) ℤ) →+* MvPolynomial (Fin (n+1)) ℤ :=
  Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun i => MvPolynomial.X i.succ)) (MvPolynomial.X 0)

@[simp]
theorem polyToMvPoly_toPoly {n : ℕ} (p : Poly (n+1)) :
    polyToMvPoly (toPoly p) = toMvPoly p := by
  rw [polyToMvPoly, toPoly, apply_eval, toMvPoly]
  simp
  congr
  ext1 i
  induction i using Fin.cases <;> simp

-- @[simp]
-- theorem polyToMvPoly_C {n : ℕ} (p : MvPolynomial (Fin n) ℤ) :
--     polyToMvPoly (Polynomial.C p) = toMvPoly p := by
--   rw [polyToMvPoly, toPoly, apply_eval, toMvPoly]
--   simp
--   congr
--   ext1 i
--   induction i using Fin.cases <;> simp

@[simp]
theorem toMvPoly_X {n : ℕ} (i : Fin n) : toMvPoly (X i) = MvPolynomial.X i := by
  simp [X, toMvPoly]

@[simp]
theorem toMvPoly_const {n : ℕ} (p : Poly n) : toMvPoly (const p) =
    (toMvPoly p).rename Fin.succ := by
  simp only [toMvPoly, eval]
  rw [← AlgHom.coe_toRingHom, apply_eval]
  simp

@[simp]
theorem toMvPoly_constAddXMul {n : ℕ} (p : Poly n) (q : Poly (n+1)) : toMvPoly (constAddXMul p q) =
    (toMvPoly p).rename Fin.succ + MvPolynomial.X 0 * toMvPoly q := by
  simp only [toMvPoly, eval]
  rw [← AlgHom.coe_toRingHom, apply_eval]
  simp


@[simp]
theorem toPoly_X_succ {n : ℕ} (i : Fin n) : toPoly (X i.succ) = Polynomial.C (MvPolynomial.X i) := by
  simp [toPoly]

@[simp]
theorem toPoly_const {n : ℕ} (p : Poly n) : toPoly (const p) = Polynomial.C (toMvPoly p) := by
  rw [toPoly, eval, toMvPoly, apply_eval]
  simp

@[simp]
theorem toPoly_constAddXMul {n : ℕ} (p : Poly n) (q : Poly (n+1)) : toPoly (constAddXMul p q) = Polynomial.C (toMvPoly p) +
    Polynomial.X * toPoly q  := by
  simp only [toPoly, eval, toMvPoly, apply_eval]
  simp

@[simp]
theorem toPoly_add {n : ℕ} (p q : Poly (n+1)) : toPoly (p + q) = toPoly p + toPoly q :=
  eval_add _ _ _

@[simp]
theorem toPoly_mul {n : ℕ} (p q : Poly (n+1)) : toPoly (p * q) = toPoly p * toPoly q :=
  eval_mul _ _ _

@[simp]
theorem toPoly_pow {n : ℕ} (p : Poly (n+1)) (m : ℕ) : toPoly (p ^ m) = toPoly p ^ m := eval_pow _ _ _

@[simp]
theorem toMvPoly_pow {n : ℕ} (p : Poly n) (m : ℕ) : toMvPoly (p ^ m) = toMvPoly p ^ m := eval_pow _ _ _

@[simp]
theorem toPoly_zero {n : ℕ} : toPoly (0 : Poly (n+1)) = 0 := eval_zero _

@[simp]
theorem toPoly_eraseLead : ∀ {n : ℕ} (p : Poly (n+1)),
    p.eraseLead.toPoly = p.toPoly - Polynomial.C p.leadingCoeff.toMvPoly * Polynomial.X ^ p.degree := by
  simp [toPoly, toMvPoly, apply_eval]

@[simp]
theorem toPoly_mulConstMulXPow : ∀ {n : ℕ} (p : Poly n) (m : ℕ) (q : Poly (n+1)),
    (mulConstMulXPow p m q).toPoly = Polynomial.C p.toMvPoly * Polynomial.X ^ m * q.toPoly := by
  simp [toPoly, toMvPoly, apply_eval, eval_mulConstMulXPow]

@[simp]
theorem toMvPoly_one {n : ℕ} : toMvPoly (1 : Poly n) = 1 := eval_one _

@[simp]
theorem toMvPoly_add {n : ℕ} (p q : Poly n) : toMvPoly (p + q) = toMvPoly p + toMvPoly q :=
  eval_add _ _ _

@[simp]
theorem toMvPoly_ofInt' (z : ℤ) : toMvPoly (ofInt' z) = z := rfl

@[simp]
theorem toMvPoly_sub {n : ℕ} (p q : Poly n) : toMvPoly (p - q) = toMvPoly p - toMvPoly q :=
  eval_sub _ _ _

@[simp]
theorem toPoly_sub {n : ℕ} (p q : Poly (n+1)) : toPoly (p - q) = toPoly p - toPoly q :=
  eval_sub _ _ _

@[simp]
theorem toMvPoly_mul {n : ℕ} (p q : Poly n) : toMvPoly (p * q) = toMvPoly p * toMvPoly q :=
  eval_mul _ _ _

open Polynomial

theorem toPoly_pseudoModDiv :  ∀ {n : ℕ} (p q : Poly (n+1)),
    let (n, h, r) := pseudoModDiv p q
    C q.leadingCoeff.toMvPoly ^ n * toPoly p - toPoly r  =
       toPoly h * toPoly q :=
  fun p q =>
  if h : degree q ≤ degree p
  then if hp0 : p = 0 then by
    rw [pseudoModDiv]
    simp [h, hp0, degree]
    split_ifs <;> simp
  else
    if hq0 : q.degree = 0 then by
      rw [pseudoModDiv]
      simp [h, hp0, degree, hq0]
      cases q
      · simp [leadingCoeff, mul_comm]
      · simp [degree] at hq0
    else by
      simp only
      generalize hlp : p.leadingCoeff = lp
      generalize hlq : q.leadingCoeff = lq
      generalize hdp : p.degree = dp
      generalize hz : (mulConstMulXPow lp (dp - q.degree) q).eraseLead = z
      generalize hk : (pseudoModDiv ((mulConstMulXPow lq 0 p).eraseLead - z) q) = k
      have wf := modDiv_wf lp lq h hq0
      have ih := toPoly_pseudoModDiv ((mulConstMulXPow lq 0 p).eraseLead - z) q
      rw [pseudoModDiv]
      simp only [h, ↓reduceDIte, hp0, hq0, toPoly_add, toPoly_mul, toPoly_const, toMvPoly_mul,
        toMvPoly_pow, map_mul, map_pow, toPoly_pow, toPoly_X_zero]
      simp only [add_mul, mul_add, hlp, hlq, hdp, hz, hk] at ih ⊢
      rw [← ih]
      ring_nf
      simp only [← hz, toPoly_sub, toPoly_eraseLead, toPoly_mulConstMulXPow, pow_zero, mul_one,
        leadingCoeff_mulConstMulXPow, toMvPoly_mul, map_mul, degree_mulConstMulXPow, add_zero,
        mul_sub]
      ring_nf
      simp only [mul_assoc, mul_left_comm (Polynomial.X ^ _), mul_comm (Polynomial.X ^q.degree)]
      subst hdp hlp hlq
      rw [← pow_add, Nat.sub_add_cancel h]
      ring
  else by
    rw [pseudoModDiv]
    simp only [h]
    simp
  termination_by n p => (n+1, 1, degree p)

theorem toMvPoly_div : ∀ {n : ℕ} (p q : Poly n), toMvPoly q ∣ toMvPoly p →
    toMvPoly q * (p / q).toMvPoly = p.toMvPoly
  | 0, ofInt' x, ofInt' y, ⟨c, hc⟩ => by
    simp only [toMvPoly_ofInt', div_def, divDvd, ofInt] at *
    apply_fun MvPolynomial.eval (Fin.elim0) at hc
    simp at hc
    subst hc
    rw [mul_comm, ← Int.cast_mul, Int.tdiv_mul_cancel]
    simp
  | n+1, const p, const q, ⟨c, hc⟩ => by
      simp only [toMvPoly_const] at *
      apply_fun (MvPolynomial.eval₂ (MvPolynomial.C) (fun (i : Fin (n+1)) =>
        Fin.cases (n := n) 0 (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ)) i)) at hc
      simp only [MvPolynomial.eval₂_rename, Function.comp_def, Fin.cases_succ,
        map_mul, MvPolynomial.eval₂_mul, div_def, divDvd, toMvPoly_const] at hc ⊢
      simp only [MvPolynomial.eval₂_eta] at hc ⊢
      have := toMvPoly_div p q ⟨_, hc⟩
      rw [← this]
      simp [div_def]
  | n+1, constAddXMul p₁ p₂, const q, ⟨c, hc⟩ => by
      simp [toMvPoly_const] at *
      sorry
  | _+1, p, constAddXMul q₁ q₂, _ => by
    rw [div_def, divDvd]
    split_ifs with hqp hp0
    · simp [hp0, toMvPoly]
    · simp
      have :=


mutual

theorem toPoly_contPrim : ∀ {n : ℕ} (p : Poly (n+1)),
    let cp := contPrim p
    Polynomial.C (toMvPoly cp.1) * toPoly cp.2 = toPoly p ∧ (toPoly cp.2).IsPrimitive
  | _, const p => by
    simp [contPrim, toPoly, toMvPoly, Polynomial.smul_eq_C_mul, apply_eval]
  | i, constAddXMul p q => by
    let _ := UniqueFactorizationMonoid.toNormalizedGCDMonoid
    let _ := @UniqueFactorizationMonoid.normalizationMonoid
    have ih := toPoly_contPrim q
    have ih_gcd := toMvPoly_gCd p q.contPrim.1
    simp only at ih_gcd
    simp only [contPrim, toPoly_constAddXMul] at ih ⊢
    rw [← ih.1]
    refine ⟨?_, ?_⟩
    · rw [← ih_gcd.1, ← ih_gcd.2.1]
      simp only [toMvPoly, toPoly, map_mul, apply_eval, eval, eval_zero,
        Polynomial.smul_eq_C_mul, eval_add, eval_mul, zero_add, eval_ofInt]
      simp [mul_add, add_mul, add_comm, add_left_comm, add_assoc, mul_assoc,
        mul_comm, mul_left_comm]
    · intro k hk
      rcases h : q.contPrim with ⟨qc, qp⟩
      rcases hg : p.gCd qc with ⟨g, a, b⟩
      simp only [h, hg, toPoly_add, toPoly_mul, toPoly_X_zero, C_dvd_iff_dvd_coeff] at ih ih_gcd hk
      have hka : k ∣ a.toMvPoly := by simpa using hk 0
      replace hk := fun i => hk (i+1)
      simp only [toPoly_const, X_mul_C, coeff_add, coeff_C_succ, zero_add,
        ← mul_assoc, mul_right_comm _ (Polynomial.X), coeff_mul_X,
        ← C_dvd_iff_dvd_coeff] at hk
      rw [← dvd_content_iff_C_dvd, content_mul, content_C] at hk
      replace hk := dvd_mul_gcd_of_dvd_mul hk
      let m := gcd k qp.toPoly.content
      have := ih.2 m (dvd_content_iff_C_dvd.1 (gcd_dvd_right _ _))
      replace hk := (IsUnit.dvd_mul_right this).1 hk
      rw [dvd_normalize_iff] at hk
      have := ih_gcd.2.2.1 (k * g.toMvPoly)
      by_cases hg0 : g.toMvPoly = 0
      · simp_all [eq_comm]
        exact isUnit_of_dvd_one hka
      rw [← ih_gcd.1, ← ih_gcd.2.1, mul_comm k, mul_dvd_mul_iff_left hg0,
        mul_dvd_mul_iff_left hg0] at this
      have := this hka hk
      have : g.toMvPoly * k ∣ g.toMvPoly * 1 := by simpa
      rw [mul_dvd_mul_iff_left hg0] at this
      exact isUnit_of_dvd_one this
  termination_by n p => (n+1, 0, sizeOf p)

theorem toMvPoly_gCd : ∀ {n : ℕ} (p q : Poly n),
    let (g, a, b) := gCd p q
    toMvPoly g * toMvPoly a = toMvPoly p ∧
    toMvPoly g * toMvPoly b = toMvPoly q ∧
    (∀ k : MvPolynomial (Fin n) ℤ, k ∣ toMvPoly p → k ∣ toMvPoly q → k ∣ toMvPoly g) ∧
    (toMvPoly p = 0 → a = 1)
  | 0, ofInt' x, ofInt' y => by
    simp only [toMvPoly, gCd, eval_intCast, eval, ← Int.cast_mul,
      Int.mul_tdiv_cancel' (Int.gcd_dvd_left), true_and,
      Int.mul_tdiv_cancel' (Int.gcd_dvd_right), Int.cast_eq_zero]
    admit
  | n+1, p, q =>
    if hq0 : q = 0 then by
      simp [hq0, gCd, toMvPoly]
    else by
      rcases hcp : contPrim p with ⟨pc, pp⟩
      rcases hmd : pseudoModDiv pp q with ⟨k, h, ⟨r, hr⟩⟩
      have _wf : (if (r : Poly (n+1)) = 0 then 0 else 1 + (r : Poly (n+1)).degree) <
          (if q = 0 then 0 else 1 + q.degree) := by
        split_ifs with hr0
        · simp_all
        · by_cases hq0 : q.degree = 0
          · simp_all
          · simp only [add_lt_add_iff_left]
            exact hr.1 (Nat.pos_iff_ne_zero.2 hq0)
      rcases hg : gCd q r with ⟨g, a, b⟩
      have ih := toMvPoly_gCd q r
      simp only at ih
      simp only
      rw [gCd, dif_neg hq0, hcp]
      simp only
      simp only [hmd, ih.1, true_and]
      simp only [toMvPoly_mul, hg, hmd]
      simp only [hg, hmd] at ih ⊢
      rw [hmd, hg]
      simp only
      have ⟨hdpg₁, hdpg₂⟩ := toPoly_pseudoModDiv p g
      have ⟨hdpq₁, hdpq₂⟩ := toPoly_pseudoModDiv pp q
      simp only [hmd] at hdpq₁ hdpq₂
      simp only [← sub_eq_iff_eq_add] at hdpg₁
      apply_fun polyToMvPoly at hdpg₁ hdpq₁
      rw [← mul_assoc, mul_comm g.toMvPoly]
      simp at hdpg₁ hdpq₁
      rw [← hdpg₁]
      rw [← ih.1, ← ih.2.1]  at hdpq₁



  termination_by n _ q => (n, 2, if q = 0 then 0 else 1 + degree q)

end

end Poly

open Poly

-- Invariants to maintain. No constant polys in any list. Eqs has smallest by lex leadingMon degree at head
structure Ands (n : ℕ) : Type where
  (eqs : List (Poly (n+1)))
  (neq : Poly (n+1))
  deriving DecidableEq

namespace Ands

def eval {n : ℕ} (φ : Ands n) (vars : Fin (n+1) → ℂ) : Prop :=
  (∀ p ∈ φ.eqs, p.eval vars = 0) ∧ (φ.neq.eval vars ≠ 0)



--def reduceEqs {n : ℕ} (φ : Ands n) : Ands n × Ands n := sorry

end Ands
