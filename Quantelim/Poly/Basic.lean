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

def natDegree {n : ℕ} (p : PolyAux n) : ℕ := p.degree.unbot' 0

def deriv : ∀ {n : ℕ}, PolyAux (n + 1) → PolyAux (n + 1)
  | _, constAddXMul _ q => q + constAddXMul' 0 (deriv q)
  | _, _ => 0

def X : ∀ {n : ℕ}, Fin n → PolyAux n
  | _+1, ⟨0, _⟩ => constAddXMul 0 1
  | _+1, ⟨i+1, h⟩ => const (X ⟨i, Nat.lt_of_succ_lt_succ h⟩)

def coeff : ∀ {n : ℕ}, PolyAux (n+1) → ℕ → PolyAux n
  | _, const p, 0 => p
  | _, const _, _+1 => 0
  | _, constAddXMul p _, 0 => p
  | _, constAddXMul _ q, i+1 => coeff q i

theorem good_coeff : ∀ {n : ℕ} {p : PolyAux (n+1)} {i : ℕ} (h : Good p), Good (coeff p i)
  | _, const p, 0, h => by cases h; simp [coeff]; assumption
  | _, const _, _+1, h => good_ofInt
  | _, constAddXMul p _, 0, h => by cases h; simp [coeff]; assumption
  | _, constAddXMul _ q, i+1, h => by
    cases h
    simp only [coeff]
    exact good_coeff (by assumption)

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

@[simp]
theorem natDegree_const {n : ℕ} (p : PolyAux n) : natDegree (const p) = 0 := by
  simp [natDegree, degree]; tauto

theorem degree_eq_bot {n : ℕ} (p : PolyAux n) (hp : p.Good) : p.degree = ⊥ ↔ p = 0 := by
  induction p <;> simp_all [degree, zero_def, ofInt]
  cases hp; simp_all [zero_def, ofInt]

-- @[simp]
-- theorem natDegree_constAddXMul {n : ℕ} {p : PolyAux n} {q : PolyAux (n+1)} (hq0 : q ≠ 0) :
--     natDegree (constAddXMul p q) = natDegree q + 1 := by
--   rw [natDegree, natDegree]

-- @[simp]
-- theorem eval_eraseLead : ∀ {n : ℕ} (p : PolyAux (n+1)) (vars : Fin (n+1) → K),
--      p.eraseLead.eval vars = p.eval vars - p.leadingCoeff.eval (fun i => vars i.succ) * vars 0 ^ p.natDegree
--   | _, const _, _ => by simp [eraseLead, leadingCoeff]
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

instance : CharZero (Poly n) := ⟨by
  intro a b
  rw [← map_natCast ringEquivMvPolyAux.symm, ← map_natCast ringEquivMvPolyAux.symm,
     ringEquivMvPolyAux.symm.injective.eq_iff]
  exact fun h => Nat.cast_injective h⟩

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

def toInt : Poly 0 →+* ℤ := eval Fin.elim0

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

noncomputable def toPoly (R : Type*) [CommRing R] (x : Fin n → R) : Poly (n+1) →+* Polynomial R :=
  eval (Fin.cases Polynomial.X (fun i => Polynomial.C (x i)))

def coeff (p : Poly (n+1)) (i : ℕ) : Poly n := ⟨p.1.coeff i, PolyAux.good_coeff p.2⟩

@[simp]
theorem toPoly_coeff : ∀ {n : ℕ} (x : Fin n → R) (p : Poly (n+1)) (i : ℕ),
    (toPoly R x p).coeff i = (p.coeff i).eval x
  | _, _, ⟨PolyAux.const p, _⟩, 0 => by
    simp [coeff, PolyAux.coeff, toPoly, eval, ← PolyAux.apply_eval]
  | _, _, ⟨PolyAux.const p, _⟩, i+1 => by
    simp [coeff, PolyAux.coeff, toPoly, eval, ← PolyAux.apply_eval]
  | _, _, ⟨PolyAux.constAddXMul p q, _⟩, 0 => by
    simp [coeff, PolyAux.coeff, toPoly, eval, ← PolyAux.apply_eval]
  | _, x, ⟨PolyAux.constAddXMul p q, h⟩, i+1 => by
    have ih := toPoly_coeff x ⟨q, by cases h; assumption⟩ i
    simp only [toPoly, eval, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff, PolyAux.eval,
      Fin.cases_succ, ← PolyAux.apply_eval, Fin.cases_zero, Polynomial.coeff_add,
      Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, zero_add, PolyAux.coeff] at ih ⊢
    rw [ih]

theorem eval_X' (p : Poly n) : p.eval X = p := by
  apply toMvPoly.injective
  erw [apply_eval toMvPoly.toRingHom]
  simp [toMvPoly]

@[ext high]
theorem hom_ext {f g : Poly n →+* R} (h : ∀ i, f (X i) = g (X i)) : f = g := by
  ext p
  rw [← eval_X' p, apply_eval, apply_eval]
  simp only [h]

theorem intCast_toInt (p : Poly 0) : (toInt p : Poly 0) = p :=
  show ((Int.castRingHom (Poly 0)).comp toInt) p = RingHom.id _ p by
    apply RingHom.congr_fun
    ext i
    exact Fin.elim0 i

theorem toInt_injective : Function.Injective (toInt : Poly 0 → ℤ) := by
  intro p q h
  rw [← intCast_toInt p, ← intCast_toInt q, h]

noncomputable def toPolyMvPoly : Poly (n+1) ≃+* Polynomial (MvPolynomial (Fin n) ℤ) :=
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

@[simp]
theorem toPoly_const (R : Type*) [CommRing R] (x : Fin n → R) (p : Poly n) :
    toPoly R x (Poly.const p) = Polynomial.C (p.eval x) := by
  simp [toPoly, ← apply_eval]

@[simp]
theorem toPoly_X_zero (R : Type*) [CommRing R] (x : Fin n → R) :
    toPoly R x (X 0) = Polynomial.X := by
  simp [toPoly, ← apply_eval]

@[simp]
theorem toPoly_X_succ (R : Type*) [CommRing R] (x : Fin n → R) (i : Fin n) :
    toPoly R x (X i.succ) = Polynomial.C (x i) := by
  simp [toPoly, ← apply_eval]

def constAddXMul {n : ℕ} (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) : Poly (n+1) :=
  ⟨PolyAux.constAddXMul p.1 q.1, PolyAux.Good.constAddXMul p.2 q.2 (by
    intro h
    cases q
    simp_all
    exact hq0 rfl)⟩

@[simp]
theorem eval_constAddXMul (vars : Fin (n+1) → R) (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) :
    eval vars (constAddXMul p q hq0) = eval vars p.const + vars 0 * eval vars q := rfl

@[simp]
theorem constAddXMul_eq_const_add_X_mul (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) :
    constAddXMul p q hq0 = p.const + X 0 * q := by
  apply toPolyMvPoly.injective
  simp [toPolyMvPoly]

theorem toPolyMvPoly_const (p : Poly n) : toPolyMvPoly (const p) = Polynomial.C (toMvPoly p) :=
  show (toPolyMvPoly.toRingHom.comp const) p = Polynomial.C.comp toMvPoly.toRingHom p from
    RingHom.congr_fun (hom_ext (by simp [toPolyMvPoly, toMvPoly])) _

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

def degree {n : ℕ} (p : Poly n) : WithBot ℕ := p.1.degree

def natDegree {n : ℕ} (p : Poly n) : ℕ := p.1.natDegree

theorem degree_nonneg_iff_ne_zero {n : ℕ} {p : Poly (n+1)} : 0 ≤ p.degree ↔ p ≠ 0 := by
  erw [(PolyAux.degree_nonneg_iff_ne_zero p.1 p.2), val_ne_zero]

theorem degree_toPolyMvPoly {n : ℕ} (p : Poly (n+1)) : (toPolyMvPoly p).degree = p.degree :=
  @recOnSucc n (fun p => (toPolyMvPoly p).degree = p.degree) p
    (by
      intro n p
      by_cases hp : p = 0
      · subst hp; simp [degree]
      · have hp01 : toMvPoly p ≠ 0 := by
          rwa [Ne, RingEquiv.map_eq_zero_iff toMvPoly]
        rw [toPolyMvPoly_const, Polynomial.degree_C hp01]
        show (0 : WithBot ℕ) = if _ then _ else _
        rw [if_neg]
        rwa [val_eq_zero])
    (by
      intro m p q hq ih
      simp [toPolyMvPoly, degree] at *
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
theorem deriv_const (p : Poly n) : (const p).deriv = 0 := by
  apply Subtype.ext
  simp [const, deriv, PolyAux.deriv]

@[simp]
theorem deriv_constAddXMul {n : ℕ} (p : Poly n) (q : Poly (n+1)) (hq0 : q ≠ 0) :
    (constAddXMul p q hq0).deriv = q + X 0 * deriv q := by
  apply toMvPoly.injective
  cases p; cases q;
  simp only [deriv, PolyAux.deriv, constAddXMul, toMvPoly, eval]
  simp

theorem toPoly_deriv (p : Poly (n+1)) : ∀ (x : Fin n → R),
    toPoly R x (deriv p) = (toPoly R x p).derivative :=
  @Poly.recOnSucc _ (fun {m} q => ∀ (x : Fin m → R),
    toPoly R x (deriv q) = (toPoly R x q).derivative) p
      (by simp [toPoly, forall_const, ← apply_eval])
      (by
        intro n p q hq0
        simp only [deriv_constAddXMul]
        simp only [toPoly, map_add, map_mul, eval_X, Fin.cases_zero,
          constAddXMul_eq_const_add_X_mul, eval_const, Fin.cases_succ, ← apply_eval,
          Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
          Polynomial.derivative_X, one_mul, zero_add, add_right_inj]
        intro ih x
        rw [ih])

@[simp]
theorem degree_neg {n : ℕ} (p : Poly (n+1)) : (-p).degree = p.degree := by
  rw [← degree_toPolyMvPoly, map_neg, Polynomial.degree_neg, degree_toPolyMvPoly]

theorem degree_add_le {n : ℕ} (p q : Poly (n+1)) : (p + q).degree ≤ max p.degree q.degree := by
  rw [← degree_toPolyMvPoly, ← degree_toPolyMvPoly, map_add, ← degree_toPolyMvPoly]
  apply Polynomial.degree_add_le

theorem degree_sub_le {n : ℕ} (p q : Poly (n+1)) : (p - q).degree ≤ max p.degree q.degree := by
  rw [← degree_toPolyMvPoly, ← degree_toPolyMvPoly, map_sub, ← degree_toPolyMvPoly]
  apply Polynomial.degree_sub_le

theorem degree_mul {n : ℕ} (p q : Poly (n+1)) : (p * q).degree = p.degree + q.degree := by
  rw [← degree_toPolyMvPoly, ← degree_toPolyMvPoly, map_mul, ← degree_toPolyMvPoly]
  apply Polynomial.degree_mul

theorem degree_const_of_ne_zero {n : ℕ} {p : Poly n} (hp0 : p ≠ 0) : (const p : Poly (n+1)).degree = 0 := by
  simp [degree, *]

@[simp]
theorem natDegree_const {n : ℕ} (p : Poly n) : (const p : Poly (n+1)).natDegree = 0 := by
  simp [natDegree, PolyAux.natDegree, const, PolyAux.natDegree]; tauto

@[simp]
theorem degree_one : (1 : Poly (n+1)).degree = 0 := by
  rw [← Int.cast_one, ← map_intCast (@const n)]
  exact degree_const_of_ne_zero (by simp)

@[simp]
theorem degree_pow {n : ℕ} (p : Poly (n+1)) (k : ℕ) : (p ^ k).degree = k • p.degree := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ih, degree_mul, add_mul]

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


theorem leadingCoeff_toPolyMvPoly {n : ℕ} (p : Poly (n+1)) : toMvPoly (leadingCoeff p) = Polynomial.leadingCoeff (toPolyMvPoly p) :=
  @recOnSucc n (fun p => toMvPoly (leadingCoeff p) = Polynomial.leadingCoeff (toPolyMvPoly p)) p
    (by
      intro n p
      simp [toPolyMvPoly, ← apply_eval, toMvPoly])
    (by
      intro m p q hq ih
      simp only [toMvPoly, MvPolynomial.coe_eval₂Hom, RingEquiv.coe_mk, Equiv.coe_fn_mk, toPolyMvPoly,
        RingEquiv.ofHomInv_apply, leadingCoeff_constAddXMul, eval_constAddXMul, eval_const,
        Fin.cons_succ, Fin.cons_zero] at *
      rw [ih]
      simp only [← apply_eval]
      rw [Polynomial.leadingCoeff_add_of_degree_lt, mul_comm, Polynomial.leadingCoeff_mul_X]
      refine lt_of_le_of_lt (Polynomial.degree_C_le) ?_
      rw [Polynomial.degree_mul, Polynomial.degree_X]
      refine add_pos_of_pos_of_nonneg zero_lt_one ?_
      rw [Nat.WithBot.nonneg_iff_ne_bot, Ne, Polynomial.degree_eq_bot]
      show toPolyMvPoly _ ≠ _
      rwa [Ne, toPolyMvPoly.map_eq_zero_iff])

theorem degree_sub_lt {n : ℕ} {p q : Poly (n+1)} (h : p.degree = q.degree) (hq0 : p ≠ 0)
    (h : p.leadingCoeff = q.leadingCoeff) : (p - q).degree < p.degree := by
  rw [← degree_toPolyMvPoly, ← degree_toPolyMvPoly, map_sub]
  apply Polynomial.degree_sub_lt
  · rwa [degree_toPolyMvPoly, degree_toPolyMvPoly]
  · rwa [Ne, toPolyMvPoly.map_eq_zero_iff]
  · rw [← leadingCoeff_toPolyMvPoly, ← leadingCoeff_toPolyMvPoly, h]

theorem natDegree_toPolyMvPoly {n : ℕ} (p : Poly (n+1)) : (toPolyMvPoly p).natDegree = p.natDegree := by
  rw [natDegree, Polynomial.natDegree, degree_toPolyMvPoly, PolyAux.natDegree]; rfl

theorem degree_eq_natDegree {n : ℕ} {p : Poly (n+1)} (hp0 : p ≠ 0) : p.degree = p.natDegree := by
  rw [← degree_toPolyMvPoly, ← natDegree_toPolyMvPoly]
  apply Polynomial.degree_eq_natDegree
  rwa [Ne, toPolyMvPoly.map_eq_zero_iff]

@[simp]
theorem natDegree_zero : (0 : Poly n).natDegree = 0 := by
  simp [natDegree, PolyAux,natDegree, PolyAux.zero_def]
  cases n <;> simp [PolyAux.ofInt, PolyAux.natDegree, PolyAux.zero_def]

theorem natDegree_eq_ite {n : ℕ} (p : Poly (n+1)) :
    p.natDegree = if p = 0 then 0 else p.degree := by
  split_ifs with hp0
  · subst hp0; simp
  · rw [degree_eq_natDegree hp0]

@[simp]
theorem degree_zero : degree (0 : Poly (n+1)) = ⊥ := by
  induction n <;> simp_all [degree, PolyAux.ofInt]

theorem natDegree_le_natDegree_of_degree_le_degree {p q : Poly (n+1)} :
    p.degree ≤ q.degree → p.natDegree ≤ q.natDegree := by
  rw [← @Nat.cast_le (WithBot ℕ), natDegree_eq_ite, natDegree_eq_ite]
  split_ifs <;> simp_all [degree_eq_natDegree]

theorem natDegree_lt_natDegree_of_degree_lt_degree {p q : Poly (n+1)} (hp0 : p ≠ 0) :
    p.degree < q.degree → p.natDegree < q.natDegree := by
  rw [← @Nat.cast_lt (WithBot ℕ), natDegree_eq_ite, natDegree_eq_ite]
  split_ifs <;> simp_all [degree_eq_natDegree]

--Weirdly specific theorem
theorem natDegree_lt_natDegree_of_degree_lt_degree_of_pos {p q : Poly (n+1)}
    (hq0 : 0 < q.degree) :
    p.degree < q.degree → p.natDegree < q.natDegree := by
  rw [← @Nat.cast_lt (WithBot ℕ), natDegree_eq_ite, natDegree_eq_ite]
  split_ifs <;> simp_all [degree_eq_natDegree]


@[simp]
theorem toPolyMvPoly_X_zero {n : ℕ} : toPolyMvPoly (X 0 : Poly (n+1)) = Polynomial.X := by
  simp [toPolyMvPoly]

@[simp]
theorem degree_X_zero {n : ℕ} : (X 0 : Poly (n+1)).degree = 1 := by
  rw [← degree_toPolyMvPoly, toPolyMvPoly_X_zero, Polynomial.degree_X]

theorem degree_const_mul_X_pow {n : ℕ} {p : Poly n} (hp0 : p ≠ 0) (k : ℕ) :
    (const p * X 0 ^ k).degree = (k : WithBot ℕ) := by
  rw [← degree_toPolyMvPoly, map_mul, map_pow, toPolyMvPoly_X_zero, toPolyMvPoly_const]
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

theorem C_toMvPoly (p : Poly n) : Polynomial.C (toMvPoly p) = toPolyMvPoly (const p) := by
  simp [toMvPoly, toPolyMvPoly, apply_eval]

@[simp]
theorem leadingCoeff_eq_zero {p : Poly (n+1)} : leadingCoeff p = 0 ↔ p = 0 := by
  rw [← (@toMvPoly n).injective.eq_iff, leadingCoeff_toPolyMvPoly, map_zero,
    Polynomial.leadingCoeff_eq_zero, toPolyMvPoly.map_eq_zero_iff]

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : Poly (n+1)) = 0 := by
  simp

@[simp]
theorem leadingCoeff_ne_zero {p : Poly (n+1)} : leadingCoeff p ≠ 0 ↔ p ≠ 0 := by
  rw [Ne, leadingCoeff_eq_zero]

@[simp]
theorem leadingCoeff_one : leadingCoeff (1 : Poly (n+1)) = 1 := by
  rw [← Int.cast_one, ← map_intCast (@const n), leadingCoeff_const, Int.cast_one]


@[simp]
theorem degree_eq_bot {p : Poly (n+1)} : p.degree = ⊥ ↔ p = 0 := by
  rw [← degree_toPolyMvPoly, Polynomial.degree_eq_bot, toPolyMvPoly.map_eq_zero_iff]

@[simp]
theorem toPolyMvPoly_dvd_toPolyMvPoly {n : ℕ} {p q : Poly (n+1)} : toPolyMvPoly p ∣ toPolyMvPoly q ↔ p ∣ q := by
  simp only [dvd_iff_exists_eq_mul_left]
  rw [← Equiv.exists_congr toPolyMvPoly.toEquiv]
  intro a
  rw [← toPolyMvPoly.symm.injective.eq_iff]
  simp

@[simp]
theorem toMvPoly_dvd_toMvPoly {n : ℕ} {p q : Poly n} : toMvPoly p ∣ toMvPoly q ↔ p ∣ q := by
  simp only [dvd_iff_exists_eq_mul_left]
  rw [← Equiv.exists_congr toMvPoly.toEquiv]
  intro a
  rw [← toMvPoly.symm.injective.eq_iff]
  simp

@[simp]
theorem const_dvd_const {n : ℕ} {p q : Poly n} : const p ∣ const q ↔ p ∣ q := by
  refine ⟨?_, map_dvd _⟩
  rw [← toPolyMvPoly_dvd_toPolyMvPoly, toPolyMvPoly_const, toPolyMvPoly_const, Polynomial.C_dvd_iff_dvd_coeff,
    ← toMvPoly_dvd_toMvPoly]
  intro h
  simpa using h 0

@[simp]
theorem intCast_dvd_intCast {n : ℕ} {x y : ℤ} : (x : Poly n) ∣ y ↔ x ∣ y := by
  refine ⟨?_, map_dvd (Int.castRingHom _)⟩
  rw [← toMvPoly_dvd_toMvPoly, map_intCast, map_intCast,
    ← map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin n) ℤ) x,
    ← map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin n) ℤ) y,
    MvPolynomial.C_dvd_iff_dvd_coeff]
  intro h
  have := h 0
  rw [MvPolynomial.coeff_C] at this
  simpa

theorem const_dvd_constAddXMul {n : ℕ} {p q : Poly n} {r : Poly (n+1)} (hq0 : r ≠ 0) :
    const p ∣ constAddXMul q r hq0 ↔ p ∣ q ∧ const p ∣ r := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [← toPolyMvPoly_dvd_toPolyMvPoly, toPolyMvPoly_const, constAddXMul_eq_const_add_X_mul,
      map_add, toPolyMvPoly_const, map_mul, toPolyMvPoly_X_zero, Polynomial.C_dvd_iff_dvd_coeff] at h
    have := h 0
    simp at this
    have := fun i => h (i + 1)
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul,
      zero_add, ← Polynomial.C_dvd_iff_dvd_coeff] at this
    rw [← toPolyMvPoly_const, toPolyMvPoly_dvd_toPolyMvPoly] at this
    tauto
  · intro h
    rw [constAddXMul_eq_const_add_X_mul]
    exact dvd_add (const_dvd_const.2 h.1) (dvd_mul_of_dvd_right h.2 _)

theorem degree_le_zero_iff {n : ℕ} {p : Poly (n+1)} : p.degree ≤ 0 ↔ ∃ p', p = const p' := by
  refine ⟨?_, ?_⟩
  · rw [← degree_toPolyMvPoly, Polynomial.degree_le_zero_iff]
    intro h
    use toMvPoly.symm ((toPolyMvPoly p).coeff 0)
    rw [← toPolyMvPoly.injective.eq_iff]
    conv_lhs => rw [h]
    rw [toPolyMvPoly_const]
    simp
  · rintro ⟨p, rfl⟩
    simp [degree]; split_ifs <;> simp

theorem dvd_const_iff {n : ℕ} {p : Poly (n+1)} {q : Poly n} (hq0 : q ≠ 0) :
    p ∣ const q ↔ ∃ r : Poly n, p = const r ∧ r ∣ q := by
  have hqm0 : toMvPoly q ≠ 0 := by
    rwa [Ne, RingEquiv.map_eq_zero_iff toMvPoly]
  refine ⟨?_, ?_⟩
  · intro h
    have h' := h
    rw [← toPolyMvPoly_dvd_toPolyMvPoly, toPolyMvPoly_const] at h'
    rcases exists_eq_mul_left_of_dvd h' with ⟨r, hr⟩
    have hr':= congr_arg Polynomial.degree hr
    rw [Polynomial.degree_mul, Polynomial.degree_C hqm0] at hr'
    rw [eq_comm, Nat.WithBot.add_eq_zero_iff, degree_toPolyMvPoly] at hr'
    rcases degree_le_zero_iff.1 (le_of_eq hr'.2) with ⟨p', rfl⟩
    use p'
    simp_all
  · rintro ⟨r, rfl, hr⟩
    simp_all

theorem dvd_intCast_iff {x : ℤ} {n : ℕ} {p : Poly n} (hx : x ≠ 0) : p ∣ x ↔ ∃ y : ℤ, p = y ∧ y ∣ x := by
  induction n with
  | zero =>
    rcases p with ⟨⟨z⟩, hp⟩
    show (z : Poly 0) ∣ x ↔ ∃ y : ℤ, (z : Poly 0) = y ∧ y ∣ x
    rw [intCast_dvd_intCast]
    simp
  | succ n ih =>
    have hx0 : (x : Poly n) ≠ 0 := by simp_all
    rw [← map_intCast (@const n), dvd_const_iff hx0]
    refine ⟨?_, ?_⟩
    · rintro ⟨r, rfl, hr⟩
      rcases ih.1 hr with ⟨y, rfl, hy⟩
      use y; simp_all
    · rintro ⟨y, rfl, hy⟩
      use y; simp_all

theorem isUnit_iff {n : ℕ} {p : Poly n} : IsUnit p ↔ p = 1 ∨ p = - 1 := by
  rw [isUnit_iff_dvd_one, ← Int.cast_one, dvd_intCast_iff Int.one_ne_zero]
  simp only [← isUnit_iff_dvd_one, Int.isUnit_iff]
  refine ⟨fun ⟨y, hyp, hy⟩ => hyp ▸ by simpa only [Int.cast_inj, ← Int.cast_neg], ?_⟩
  rintro (rfl | rfl)
  · use 1; simp
  · use -1; simp

theorem leadingCoeff_mul {n : ℕ} (p q : Poly (n+1)) :
    leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  rw [← toMvPoly.injective.eq_iff, leadingCoeff_toPolyMvPoly, map_mul,
    Polynomial.leadingCoeff_mul]
  simp [leadingCoeff_toPolyMvPoly]

theorem leadingCoeff_pow {m : ℕ} (p : Poly (n+1)): leadingCoeff (p ^ m) = leadingCoeff p ^ m := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ, ih, leadingCoeff_mul]

@[simp]
theorem leadingCoeff_X_zero : leadingCoeff (X 0 : Poly (n+1)) = 1 := by
  apply toMvPoly.injective
  rw [leadingCoeff_toPolyMvPoly, toPolyMvPoly_X_zero, Polynomial.leadingCoeff_X, map_one]

theorem leadingCoeff_dvd_of_dvd {n : ℕ} {p q : Poly (n+1)} (h : p ∣ q) :
    leadingCoeff p ∣ leadingCoeff q := by
  rw [dvd_iff_exists_eq_mul_left] at h
  rcases h with ⟨r, rfl⟩
  rw [leadingCoeff_mul]
  simp

def eraseLead {n : ℕ} (p : Poly (n+1)) : Poly (n+1) :=
  p - const p.leadingCoeff * X 0 ^ p.natDegree

theorem eraseLead_add_leadingCoeff_mul : ∀ {n : ℕ} (p : Poly (n+1)),
    p = eraseLead p + const p.leadingCoeff * X 0 ^ p.natDegree := by
  intro n p
  rw [eraseLead, sub_add_cancel]

theorem degree_eraseLead_lt {p : Poly (n+1)} (hp0 : p ≠ 0) :
    (eraseLead p).degree < p.degree := by
  rw [eraseLead]
  refine degree_sub_lt ?_ hp0 ?_
  . rw [degree_mul, degree_const_of_ne_zero (leadingCoeff_ne_zero.2 hp0), zero_add,
      degree_pow, degree_X_zero, degree_eq_natDegree hp0, nsmul_eq_mul, mul_one]
  · simp [leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_X_zero]

theorem degree_toPoly_le {p : Poly (n+1)} {x : Fin n → R} : (toPoly R x p).degree ≤ degree p := by
  rw [← degree_toPolyMvPoly]
  have h : toPoly R x = RingHom.comp (Polynomial.mapRingHom
    (MvPolynomial.eval₂Hom (Int.castRingHom _) x))
      toPolyMvPoly.toRingHom := hom_ext (fun i => by induction i using Fin.cases <;> simp [toPoly, toPolyMvPoly])
  rw [h, RingHom.comp_apply]
  exact Polynomial.degree_map_le _ _

theorem natDegree_toPoly_le {p : Poly (n+1)} {x : Fin n → R} : (toPoly R x p).natDegree ≤ p.natDegree := by
  rw [← natDegree_toPolyMvPoly]
  have h : toPoly R x = RingHom.comp (Polynomial.mapRingHom
    (MvPolynomial.eval₂Hom (Int.castRingHom _) x))
      toPolyMvPoly.toRingHom := hom_ext (fun i => by induction i using Fin.cases <;> simp [toPoly, toPolyMvPoly])
  rw [h, RingHom.comp_apply]
  exact Polynomial.natDegree_map_le _ _

theorem degree_toPoly_of_leadingCoeff_ne_zero {p : Poly (n+1)} {x : Fin n → R}
    (hp : p.leadingCoeff.eval x ≠ 0) : (toPoly R x p).degree = degree p := by
  rw [← degree_toPolyMvPoly]
  have h : toPoly R x = RingHom.comp (Polynomial.mapRingHom
    (MvPolynomial.eval₂Hom (Int.castRingHom _) x))
      toPolyMvPoly.toRingHom := hom_ext (fun i => by induction i using Fin.cases <;> simp [toPoly, toPolyMvPoly])
  rw [h, RingHom.comp_apply]
  apply Polynomial.degree_map_eq_of_leadingCoeff_ne_zero
  convert hp
  erw [← leadingCoeff_toPolyMvPoly]
  simp [toMvPoly, apply_eval]

theorem toPoly_ne_zero_of_leadingCoeff_ne_zero {p : Poly (n+1)} {x : Fin n → R}
    (hp : p.leadingCoeff.eval x ≠ 0) : toPoly R x p ≠ 0 := by
  rw [Ne, ← Polynomial.degree_eq_bot, degree_toPoly_of_leadingCoeff_ne_zero hp,
    degree_eq_bot]
  rintro rfl; simp_all

theorem eval_cons_eq_toPoly_eval (p : Poly (n+1)) (x : Fin n → R) (y : R):
    p.eval (Fin.cons y x) = (toPoly R x p).eval y := by
  rw [toPoly, ← Polynomial.coe_evalRingHom, apply_eval]
  congr
  ext i
  induction i using Fin.cases
  · simp
  · simp

end defs
