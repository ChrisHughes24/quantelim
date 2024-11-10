import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Order.PiLex
import Mathlib.Data.Vector.Basic

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

def degree : ∀ {n : ℕ}, Poly n → ℕ
  | _, ofInt' _ => 0
  | _, const _ => 0
  | _, constAddXMul _ q => degree q + 1

def deriv : ∀ {n : ℕ}, Poly (n + 1) → Poly (n + 1)
  | _, constAddXMul _ q => q + constAddXMul' 0 (deriv q)
  | _, _ => 0

def X : Poly (n + 1) := constAddXMul 0 1

@[simp]
theorem eval_X {n : ℕ} (vars : Fin (n+1) → K) :
    eval (X : Poly (n+1)) vars = vars 0 := by
  simp [X, eval]

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

-- theorem eraseLead_eq_zero_iff : ∀ {n : ℕ} (p : Poly n), p.eraseLead = 0 ↔ degree p = 0
--   | _, ofInt' _ => by simp [degree, eraseLead]
--   | _, const _ => by simp [degree, eraseLead]
--   | _, constAddXMul p q => by
--     rw [degree, eraseLead, constAddXMul']
--     split_ifs with hq0
--     ·

theorem degree_pos_of_eraseLead_ne_zero : ∀ {n : ℕ} {p : Poly n}, p.eraseLead ≠ 0 → 0 < p.degree
  | _, ofInt' _ => by simp [eraseLead]
  | _, const _ => by simp [eraseLead]
  | _, constAddXMul _ _ => by simp [degree]

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

noncomputable def toMvPoly (p : Poly n) : MvPolynomial (Fin n) ℤ := eval p MvPolynomial.X

noncomputable def toPoly (p : Poly (n+1)) : Polynomial (MvPolynomial (Fin n) ℤ) :=
  eval p (Fin.cons Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i)))


end Poly

-- mutual

-- def gcd : ∀ {n : ℕ} (p q : Poly n),
--     Poly n × --the gcd
--     Poly n × --p / gcd
--     Poly n -- q / gcd
--   | 0, ofInt' x, ofInt' y => ⟨(Int.gcd x y : ℤ),
--     (x / Int.gcd x y : ℤ), (y / Int.gcd x y : ℤ)⟩
--   | n+1, _, _ => sorry


-- /-- returns `(h, d)` such that `q.leadingCoeff ^ (degree p - degree q + 1) * p = h * q + r`,
--   assuming `degree p ≤ degree q` -/
-- -- def pseudoModDiv (p q : Poly (n+1)) : (Poly (n+1) × Poly (n+1)) :=
-- --   let dp := degree p
-- --   let dq := degree q
-- --   if dp ≤ dq
-- --   then
-- --     let z := const (leadingCoeff p) * X ^ (dp - dq)
-- --     let dm := pseudoModDiv (const q.leadingCoeff * p - q * z) q
-- --     ⟨z + dm.1, dm.2⟩
-- --   else ⟨0, p⟩

-- --end


-- -- letI := Classical.decEq R
-- --     if h : degree q ≤ degree p ∧ p ≠ 0 then
-- --       let z := C (leadingCoeff p) * X ^ (natDegree p - natDegree q)
-- --       have _wf := div_wf_lemma h hq
-- --       let dm := divModByMonicAux (p - q * z) hq
-- --       ⟨z + dm.1, dm.2⟩
-- --     else ⟨0, p⟩
-- --   termination_by p => p


open Poly

-- Invariants to maintain. No constant polys in any list. Eqs has smallest by lex leadingMon degree at head
structure Ands (n : ℕ) : Type where
  (eqs : List (Poly (n+1)))
  (neq : Poly (n+1))
  deriving DecidableEq

namespace Ands

def eval {n : ℕ} (φ : Ands n) (vars : Fin (n+1) → ℂ) : Prop :=
  (∀ p ∈ φ.eqs, p.eval vars = 0) ∧ (φ.neq.eval vars ≠ 0)



def reduceEqs {n : ℕ} (φ : Ands n) : Ands n × Ands n := sorry

end Ands
