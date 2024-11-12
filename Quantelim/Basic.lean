import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Order.PiLex
import Mathlib.Data.Vector.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

variable {K : Type*} [CommRing K]

inductive Term : (vars : ℕ) → Type
  | ofInt' : ℤ  → Term n
  | var {n : ℕ} : Fin n → Term n
  | add : {n : ℕ} → Term n → Term n → Term n
  | mul : {n : ℕ} → Term n → Term n → Term n
  | neg : {n : ℕ} → Term n → Term n
  | sub : {n : ℕ} → Term n → Term n → Term n
  deriving DecidableEq

namespace Term

instance (n : ℕ) : Zero (Term n) :=
  ⟨ofInt' 0⟩

instance (n : ℕ) : One (Term n) :=
  ⟨ofInt' 1⟩

instance (n : ℕ) : Add (Term n) :=
  ⟨Term.add⟩

instance (n : ℕ) : Mul (Term n) :=
  ⟨Term.mul⟩

instance (n : ℕ) : Neg (Term n) :=
  ⟨Term.neg⟩

noncomputable def interpret : {n : ℕ} → Term n → (vars : Fin n → K) → K
  | _, ofInt' q, _ => Int.cast q
  | _, var i, vars => vars i
  | _,  add t₁ t₂, vars => interpret t₁ vars + interpret t₂ vars
  | _, mul t₁ t₂, vars => interpret t₁ vars * interpret t₂ vars
  | _, neg t, vars => -interpret t vars
  | _, sub t₁ t₂, vars => interpret t₁ vars - interpret t₂ vars

end Term

inductive Formula : (freeVars : ℕ) → Type
  | eq : Term n → Term n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n
  | implies : Formula n → Formula n → Formula n
  | iff : Formula n → Formula n → Formula n
  | all : Formula (n+1) → Formula n
  | ex : Formula (n+1) → Formula n

namespace Formula

def interpret : {n : ℕ} → Formula n → (vars : Fin n → K) → Prop
  | _, eq t₁ t₂, vars => t₁.interpret vars = t₂.interpret vars
  | _, not φ, vars => ¬ interpret φ vars
  | _, and φ₁ φ₂, vars => interpret φ₁ vars ∧ interpret φ₂ vars
  | _, or φ₁ φ₂, vars => interpret φ₁ vars ∨ interpret φ₂ vars
  | _, implies φ₁ φ₂, vars => interpret φ₁ vars → interpret φ₂ vars
  | _, iff φ₁ φ₂, vars => interpret φ₁ vars ↔ interpret φ₂ vars
  -- ∀ x4, x3, x2, x1, x0
  | _, all φ₁, vars => ∀ x, interpret φ₁ (Fin.snoc vars x)
  | _, ex φ₁, vars => ∃ x, interpret φ₁ (Fin.snoc vars x)

end Formula

/-- Polynomials in n variables as a polynomial in var 0 over the ring of polynomials in the remaining variables -/
inductive Poly : (n : ℕ) → Type
  | ofInt' : ℤ  → Poly 0
  | const : Poly n → Poly (n+1)
  -- Never use when second part is zero
  | constAddXMul : Poly n → Poly (n + 1) → Poly (n + 1)
  deriving DecidableEq

namespace Poly

@[simp]
noncomputable def eval : {n : ℕ} → Poly n → (vars : Fin n → K) → K
  | _, ofInt' q, _ => q
  | _, const p, vars => p.eval (fun i => vars i.succ)
  | _, constAddXMul p q, vars =>
    p.eval (fun i => vars i.succ) + vars 0 * q.eval vars

def ofInt : ∀ {n : ℕ}, ℤ  → Poly n
  | 0, x => ofInt' x
  | _+1, x => const (ofInt x)

instance {n : ℕ} : IntCast (Poly n) := ⟨ofInt⟩

@[simp]
theorem eval_ofInt : ∀ {n : ℕ} (x : ℤ) (vars : Fin n → K),
    eval (ofInt x) vars = x
  | 0, _, _ => by simp [eval]
  | n+1, x, vars => by
    rw [ofInt, eval, eval_ofInt]

@[simp]
theorem eval_intCast : ∀ {n : ℕ} (x : ℤ) (vars : Fin n → K),
    eval (x : Poly n) vars = x :=
  eval_ofInt

instance {n : ℕ} : Zero (Poly n) := ⟨(0 : ℤ )⟩

@[simp]
theorem eval_zero {n : ℕ} (vars : Fin n → K) :
    eval (0 : Poly n) vars = 0 := by
  erw [eval_intCast 0]; simp

instance {n : ℕ} : One (Poly n) := ⟨(1 : ℤ )⟩

@[simp]
theorem eval_one {n : ℕ} (vars : Fin n → K) :
    eval (1 : Poly n) vars = 1 := by
  erw [eval_intCast 1]; simp

def constAddXMul' {n : ℕ} (p : Poly n) (q : Poly (n + 1)) : Poly (n+1) :=
  if q = 0 then const p else constAddXMul p q

@[simp]
theorem eval_constAddXMul' {n : ℕ} (p : Poly n) (q : Poly (n + 1)) (vars : Fin (n+1) → K) :
    eval (constAddXMul' p q) vars = p.eval (fun i => vars i.succ) + vars 0 * q.eval vars := by
  simp [constAddXMul']
  split_ifs <;>
  simp_all [eval]

theorem apply_eval {S : Type*} [CommRing S] (f : K →+* S) (vars : Fin n → K) (p : Poly n) :
    f (p.eval vars) = p.eval (fun i => f (vars i)) := by
  induction p <;> simp_all

def add : {n : ℕ} → Poly n → Poly n → Poly n
  | _, ofInt' x, ofInt' y => ofInt' (x + y)
  | _, const p, const q => const (add p q)
  | _, const p, constAddXMul q r => constAddXMul (add p q) r
  | _, constAddXMul p q, const r => constAddXMul (add p r) q
  | _, constAddXMul p q, constAddXMul r s => constAddXMul' (add p r) (add q s)

instance {n : ℕ} : Add (Poly n) := ⟨Poly.add⟩

@[simp]
theorem eval_add' : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → K) →
    eval (p.add q) vars = p.eval vars + q.eval vars
  | _, ofInt' x, ofInt' y => by simp
  | _, const p, const q => by simp [eval_add' p q]
  | _, const p, constAddXMul q r => by simp [eval_add' p q, add_comm, add_assoc, add_left_comm, add]
  | _, constAddXMul p q, const r => by simp [eval_add' p r, add_comm, add_assoc, add_left_comm, add]
  | _, constAddXMul p q, constAddXMul r s => by
    simp [eval_add' p r, eval_add' q s, add_comm, add_assoc, add_left_comm, mul_add, add]

@[simp]
theorem eval_add : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → K) →
    eval (p + q) vars = p.eval vars + q.eval vars :=
  eval_add'

def mul : {n : ℕ} → Poly n → Poly n → Poly n
  | _, ofInt' x, ofInt' y => ofInt' (x * y)
  | _, const p, const q => const (mul p q)
  | _, const p, constAddXMul q r => constAddXMul' (mul p q) (mul (const p) r)
  | _, constAddXMul p q, const r => constAddXMul' (mul p r) (mul q (const r))
  | n+1, constAddXMul p q, constAddXMul r s =>
    constAddXMul (mul p r) (add (add (mul (const p) s) (mul q (const r)))
      (constAddXMul 0 (mul q s)))
  termination_by n p q => (n, sizeOf p + sizeOf q)

instance {n : ℕ} : Mul (Poly n) := ⟨Poly.mul⟩

@[simp]
theorem eval_mul' : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → K) →
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
theorem eval_mul : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → K) →
    eval (p * q) vars = p.eval vars * q.eval vars :=
  eval_mul'

def neg : {n : ℕ} → (p : Poly n) → Poly n
  | _, ofInt' x => ofInt' (-x)
  | _, const p => const (neg p)
  | _, constAddXMul p q => constAddXMul (neg p) (neg q)

instance {n : ℕ} : Neg (Poly n) := ⟨Poly.neg⟩

theorem neg_const {n : ℕ} (p : Poly n) :
    -const p = const (-p) := rfl

@[simp]
theorem constAddXMul_neg {n : ℕ} (p : Poly n) (q : Poly (n+1)) :
    -constAddXMul p q = constAddXMul (-p) (-q) := rfl

@[simp]
theorem eval_neg' {n : ℕ} (p : Poly n) : (vars : Fin n → K) →
    eval (neg p) vars = -p.eval vars := by
  induction p <;> simp_all [eval, add_comm]

@[simp]
theorem eval_neg {n : ℕ} (p : Poly n) : (vars : Fin n → K) →
    eval (-p) vars = -p.eval vars :=
  eval_neg' p

instance : Sub (Poly n) := ⟨fun p q => p + -q⟩

@[simp]
theorem eval_sub {n : ℕ} (p q : Poly n) (vars : Fin n → K) :
    eval (p - q) vars = p.eval vars - q.eval vars :=
  (eval_add p (-q) vars).trans <| by simp [sub_eq_add_neg]

def leadingCoeff : ∀ {n : ℕ}, Poly (n+1) → Poly n
  | _, const p => p
  | _, constAddXMul _ q => leadingCoeff q

def eraseLead : ∀ {n : ℕ}, Poly n → Poly n
  | _, ofInt' _ => 0
  | _, const _ => 0
  | _, constAddXMul p q => constAddXMul' p (eraseLead q)

open Mathlib Mathlib.Vector

def leadingMon : ∀ {n : ℕ}, Poly n → Vector ℕ n
  | _, ofInt' _ => Vector.nil
  | _, const p => 0 ::ᵥ leadingMon p
  | _, constAddXMul _ q =>
    match leadingMon q with
    | ⟨n :: l, h⟩ => ⟨(n+1) :: l, h⟩

@[simp]
def degree : ∀ {n : ℕ}, Poly n → ℕ
  | _, ofInt' _ => 0
  | _, const _ => 0
  | _, constAddXMul _ q => degree q + 1

def deriv : ∀ {n : ℕ}, Poly (n + 1) → Poly (n + 1)
  | _, constAddXMul _ q => q + constAddXMul' 0 (deriv q)
  | _, _ => 0

def X : ∀ {n : ℕ}, Fin n → Poly n
  | _+1, ⟨0, _⟩ => constAddXMul 0 1
  | _+1, ⟨i+1, h⟩ => const (X ⟨i, Nat.lt_of_succ_lt_succ h⟩)

@[simp]
theorem eval_X : ∀ {n : ℕ}  (i : Fin n) (vars : Fin n → K),
    eval (X i) vars = vars i
  | _+1, ⟨0, _⟩ => by simp
  | _+1, ⟨i+1, h⟩ => by simp [eval_X]

instance {n : ℕ} : NatPow (Poly n) := ⟨fun p n => (.*p)^[n] 1⟩

@[simp]
theorem eval_pow {n : ℕ} (p : Poly n) (m : ℕ) (vars : Fin n → K) :
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
theorem eval_eraseLead : ∀ {n : ℕ} (p : Poly (n+1)) (vars : Fin (n+1) → K),
     p.eraseLead.eval vars = p.eval vars - p.leadingCoeff.eval (fun i => vars i.succ) * vars 0 ^ p.degree
  | _, const _, _ => by simp [degree, eraseLead, leadingCoeff]
  | _, constAddXMul p q, _ => by
    simp only [eraseLead, leadingCoeff, eval, eval_constAddXMul', degree]
    rw [eval_eraseLead]
    ring

theorem degree_pos_of_eraseLead_ne_zero : ∀ {n : ℕ} {p : Poly n}, p.eraseLead ≠ 0 → 0 < p.degree
  | _, ofInt' _ => by simp [eraseLead]
  | _, const _ => by simp [eraseLead]
  | _, constAddXMul _ _ => by simp [degree, eraseLead]

theorem degree_eraseLead : ∀ {n : ℕ} (p : Poly n), degree (eraseLead p) ≤ degree p - 1
  | _, ofInt' _ => by simp [degree]
  | _, const _ => by simp [degree]
  | _, constAddXMul p q => by
    rw [degree, eraseLead, constAddXMul']
    split_ifs with hq0
    · simp [degree]
    · simp only [degree, add_tsub_cancel_right]
      refine le_trans (Nat.succ_le_succ (degree_eraseLead q)) ?_
      rw [← Nat.succ_sub (Nat.succ_le.2 (degree_pos_of_eraseLead_ne_zero hq0))]
      simp

@[simp]
theorem degree_neg : ∀ {n : ℕ} (p : Poly n), (-p).degree = p.degree
  | _, ofInt' _ => by simp [degree]
  | _, const _ => by simp [degree]
  | _, constAddXMul p q => by
    rw [degree, ← degree_neg q]
    rfl

@[simp]
theorem leadingCoeff_neg : ∀ {n : ℕ} (p : Poly (n+1)), (-p).leadingCoeff = -p.leadingCoeff
  | _, const _ => by rw [leadingCoeff, neg_const, leadingCoeff]
  | _, constAddXMul p q => by
    rw [leadingCoeff, ← leadingCoeff_neg, constAddXMul_neg, leadingCoeff]

theorem degree_add_le : ∀ {n : ℕ} (p q : Poly (n+1)), degree (p + q) ≤ max (degree p) (degree q)
  | _, const p, const q => by simp [HAdd.hAdd, degree]
  | _, constAddXMul p q, const r => by simp [HAdd.hAdd, degree]
  | _, const p, constAddXMul r s => by simp [HAdd.hAdd, degree]
  | _, constAddXMul p q, constAddXMul r s => by
    simp only [HAdd.hAdd, degree]
    simp only [Add.add]
    rw [add, constAddXMul']
    split_ifs
    · simp [degree]
    · rw [degree]
      simpa using degree_add_le q s

theorem degree_sub_le {n : ℕ} (p q : Poly (n+1)) : degree (p - q) ≤ max (degree p) (degree q) :=
  le_trans (degree_add_le _ _) (by simp)

def mulConstMulXPow : ∀ {n : ℕ} (p : Poly n) (m : ℕ) (q : Poly (n+1)), Poly (n+1)
  | _, p, 0, const q => const (p * q)
  | _, p, 0, constAddXMul q r => constAddXMul (p * q) (mulConstMulXPow p 0 r)
  | _, p, m+1, q => constAddXMul 0 (mulConstMulXPow p m q)

@[simp]
theorem leadingCoeff_mulConstMulXPow : ∀ {n : ℕ} (p : Poly n) (m : ℕ) (q : Poly (n+1)),
    leadingCoeff (mulConstMulXPow p m q) = p * leadingCoeff q
  | _, p, 0, const q => by simp [mulConstMulXPow, leadingCoeff]
  | _, p, 0, constAddXMul q r => by
    simp only [mulConstMulXPow, leadingCoeff]
    rw [leadingCoeff_mulConstMulXPow]
  | _, p, m+1, q => by
    simp only [mulConstMulXPow, leadingCoeff]
    rw [leadingCoeff_mulConstMulXPow]

@[simp]
theorem degree_mulConstMulXPow : ∀ {n : ℕ} (p : Poly n) (m : ℕ) (q : Poly (n+1)),
     degree (mulConstMulXPow p m q) = degree q + m
  | _, p, 0, const q => by simp [degree, mulConstMulXPow]
  | _, p, 0, constAddXMul q r => by
    rw [degree, mulConstMulXPow, degree, degree_mulConstMulXPow]
  | _, p, m+1, q => by
    rw [mulConstMulXPow, degree, degree_mulConstMulXPow, add_assoc]

theorem eval_mulConstMulXPow : ∀ {n : ℕ} (p : Poly n) (m : ℕ) (q : Poly (n+1)) (vars : Fin (n+1) → K),
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

open Poly

theorem modDiv_wf {p q : Poly (n+1)} (lp lq : Poly n) (h : q.degree ≤ p.degree)
    (hq0 : q.degree ≠ 0) :
    ((lq.mulConstMulXPow 0 p).eraseLead -
    (mulConstMulXPow lp (p.degree - q.degree) q).eraseLead).degree < p.degree :=by
  refine lt_of_le_of_lt (degree_sub_le _ _) ?_
  simp only [max_lt_iff]
  refine ⟨lt_of_le_of_lt (degree_eraseLead _) ?_, lt_of_le_of_lt (degree_eraseLead _) ?_⟩
  . rw [degree_mulConstMulXPow, add_zero]
    exact lt_of_lt_of_le (Nat.sub_lt_self zero_lt_one (le_trans (Nat.one_le_iff_ne_zero.2 hq0) h)) le_rfl
  · erw [degree_mulConstMulXPow, Nat.add_sub_cancel' h]
    exact Nat.sub_lt_self zero_lt_one (le_trans (Nat.one_le_iff_ne_zero.2 hq0) h)

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
    {r : Poly (n+1) // (0 < q.degree → r.degree < q.degree) ∧ (q.degree = 0 → r = 0)}) :=
  fun p q =>
  let dp := degree p
  let dq := degree q
  let lp := p.leadingCoeff
  let lq := q.leadingCoeff
  if h : degree q ≤ degree p then
  if hp0 : p = 0 then (0, 0, ⟨0, by simp [degree]⟩)
  else
    if hq0 : q.degree = 0 then (1, p, ⟨0, by simp [degree]⟩)
    else
      let z := (mulConstMulXPow lp (dp - dq) q).eraseLead
      have wf := modDiv_wf lp lq h hq0
      let (n, h, r) := pseudoModDiv ((mulConstMulXPow lq 0 p).eraseLead - z) q
      (n+1, h + const (lq ^ n * lp) * X 0 ^(dp - dq), r)
  else (0, 0, ⟨p, ⟨fun _ => lt_of_not_ge h, fun hq0 => by simp [dp, dq, hq0] at h⟩⟩)
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

@[coe]
noncomputable def toMvPoly {n : ℕ} (p : Poly n) : MvPolynomial (Fin n) ℤ := eval p MvPolynomial.X

@[coe]
noncomputable def toPoly {n : ℕ} (p : Poly (n+1)) : Polynomial (MvPolynomial (Fin n) ℤ) :=
  p.eval (Fin.cons Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i)))

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
theorem toPoly_X_zero {n : ℕ} : toPoly (X 0 : Poly (n+1)) = Polynomial.X := by
  simp [toPoly]

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
  | _+1, p, q@(constAddXMul q₁ q₂), _ => by
    rw [div_def, divDvd]
    split_ifs with hqp hp0 hq0
    · simp [hp0, toMvPoly]
    · cases q with
      | const q =>
        simp only [toMvPoly_const, ← map_mul, leadingCoeff]
        have := toMvPoly_div p.leadingCoeff q
        erw [this]


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
