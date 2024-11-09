import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Order.PiLex
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Complex.Basic

namespace Polynomial

open Polynomial

variable {K : Type*} [Field K]

theorem Splits.dvd_of_roots_le_roots {p q : K[X]} (hp : p.Splits (RingHom.id _)) (hp0 : p ≠ 0)
    (hq : p.roots ≤ q.roots) : p ∣ q := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [eq_prod_roots_of_splits_id hp, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
    exact dvd_trans (Multiset.prod_dvd_prod_of_le
           (Multiset.map_le_map hq)) (prod_multiset_X_sub_C_dvd _)

theorem Splits.dvd_iff_roots_le_roots {p q : K[X]}
    (hp : p.Splits (RingHom.id _)) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    p ∣ q ↔ p.roots ≤ q.roots := by
  refine ⟨?_, Splits.dvd_of_roots_le_roots hp hp0⟩
  · rintro ⟨r, rfl⟩
    rw [roots_mul hq0]; exact le_add_right le_rfl

theorem key {f g : Polynomial ℂ} (hf0 : f ≠ 0) :
    (∀ x, f.eval x = 0 → g.eval x = 0) ↔ f ∣ f.derivative * g := by
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [eval_C, derivative_C, zero_mul, dvd_zero, iff_true]
    intro x hx
    refine False.elim (hf0 (Polynomial.ext ?_))
    intro n
    cases n
    · rw [hx]; simp
    · rw [eq_C_of_derivative_eq_zero hdf0]; simp
  have hdg :  f.derivative * g ≠ 0 := mul_ne_zero hdf0 hg0
  rw [Splits.dvd_iff_roots_le_roots (IsAlgClosed.splits f) hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_congr' fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    have : (f.rootMultiplicity a : ℂ) ∈ nonZeroDivisors ℂ := by
      rw [mem_nonZeroDivisors_iff_ne_zero, Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero]
      exact h0
    rw [derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors haf this]
    refine ⟨?_, ?_⟩
    · intro h
      calc rootMultiplicity a f
          = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
        _ ≤ rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
          ((rootMultiplicity_pos hg0).2 (h haf)))
    · intro h haf
      by_contra hg
      rw [rootMultiplicity_eq_zero hg, add_zero, Nat.le_sub_iff_add_le (Nat.succ_le_iff.1 h0)] at h
      exact not_le_of_gt (Nat.lt_succ_self _) h
  · simp [haf, rootMultiplicity_eq_zero haf]

end Polynomial

inductive Term : (vars : ℕ) → Type
  | ofRat' : ℚ → Term n
  | var {n : ℕ} : Fin n → Term n
  | add : {n : ℕ} → Term n → Term n → Term n
  | mul : {n : ℕ} → Term n → Term n → Term n
  | neg : {n : ℕ} → Term n → Term n
  | sub : {n : ℕ} → Term n → Term n → Term n
  deriving DecidableEq

namespace Term

instance (n : ℕ) : Zero (Term n) :=
  ⟨ofRat' 0⟩

instance (n : ℕ) : One (Term n) :=
  ⟨ofRat' 1⟩

instance (n : ℕ) : Add (Term n) :=
  ⟨Term.add⟩

instance (n : ℕ) : Mul (Term n) :=
  ⟨Term.mul⟩

instance (n : ℕ) : Neg (Term n) :=
  ⟨Term.neg⟩

noncomputable def interpret : {n : ℕ} → Term n → (vars : Fin n → ℂ) → ℂ
  | _, ofRat' q, _ => q
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

def interpret : {n : ℕ} → Formula n → (vars : Fin n → ℂ) → Prop
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
  | ofRat' : ℚ → Poly 0
  | const : Poly n → Poly (n+1)
  -- Never use when second part is zero
  | constAddXMul : Poly n → Poly (n + 1) → Poly (n + 1)
  deriving DecidableEq

namespace Poly

@[simp]
noncomputable def eval : {n : ℕ} → Poly n → (vars : Fin n → ℂ) → ℂ
  | _, ofRat' q, _ => q
  | _, const p, vars => p.eval (fun i => vars i.succ)
  | _, constAddXMul p q, vars =>
    p.eval (fun i => vars i.succ) + vars 0 * q.eval vars

def ofRat : ∀ {n : ℕ}, ℚ → Poly n
  | 0, x => ofRat' x
  | _+1, x => const (ofRat x)

instance {n : ℕ} : RatCast (Poly n) := ⟨ofRat⟩

@[simp]
theorem eval_ratCast : ∀ {n : ℕ} (x : ℚ) (vars : Fin n → ℂ),
    eval (x : Poly n) vars = x
  | 0, _, _ => by simp [eval]
  | n+1, x, vars => by
    simp only [eval]
    rw [← @eval_ratCast n]
    rfl

instance {n : ℕ} : Zero (Poly n) := ⟨(0 : ℚ)⟩

@[simp]
theorem eval_zero {n : ℕ} (vars : Fin n → ℂ) :
    eval (0 : Poly n) vars = 0 := by
  erw [eval_ratCast 0]; simp

def constAddXMul' {n : ℕ} (p : Poly n) (q : Poly (n + 1)) : Poly (n+1) :=
  if q = 0 then const p else constAddXMul p q

@[simp]
theorem eval_constAddXMul' {n : ℕ} (p : Poly n) (q : Poly (n + 1)) (vars : Fin (n+1) → ℂ) :
    eval (constAddXMul' p q) vars = p.eval (fun i => vars i.succ) + vars 0 * q.eval vars := by
  simp [constAddXMul']
  split_ifs <;>
  simp_all [eval]

@[simp]
def add : {n : ℕ} → Poly n → Poly n → Poly n
  | _, ofRat' x, ofRat' y => ofRat' (x + y)
  | _, const p, const q => const (add p q)
  | _, const p, constAddXMul q r => constAddXMul (add p q) r
  | _, constAddXMul p q, const r => constAddXMul (add p r) q
  | _, constAddXMul p q, constAddXMul r s => constAddXMul' (add p r) (add q s)

instance {n : ℕ} : Add (Poly n) := ⟨Poly.add⟩

@[simp]
theorem eval_add' : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → ℂ) →
    eval (p.add q) vars = p.eval vars + q.eval vars
  | _, ofRat' x, ofRat' y => by simp
  | _, const p, const q => by simp [eval_add' p q]
  | _, const p, constAddXMul q r => by simp [eval_add' p q, add_comm, add_assoc, add_left_comm]
  | _, constAddXMul p q, const r => by simp [eval_add' p r, add_comm, add_assoc, add_left_comm]
  | _, constAddXMul p q, constAddXMul r s => by
    simp [eval_add' p r, eval_add' q s, add_comm, add_assoc, add_left_comm, mul_add]

@[simp]
theorem eval_add : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → ℂ) →
    eval (p + q) vars = p.eval vars + q.eval vars :=
  eval_add'

@[simp]
def mul : {n : ℕ} → Poly n → Poly n → Poly n
  | _, ofRat' x, ofRat' y => ofRat' (x * y)
  | _, const p, const q => const (mul p q)
  | _, const p, constAddXMul q r => constAddXMul' (mul p q) (mul (const p) r)
  | _, constAddXMul p q, const r => constAddXMul' (mul p r) (mul q (const r))
  | n+1, constAddXMul p q, constAddXMul r s =>
    constAddXMul (mul p r) (add (add (mul (const p) s) (mul q (const r)))
      (constAddXMul 0 (mul q s)))
  termination_by n p q => (n, sizeOf p + sizeOf q)

instance {n : ℕ} : Mul (Poly n) := ⟨Poly.mul⟩

@[simp]
theorem eval_mul' : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → ℂ) →
    eval (p.mul q) vars = p.eval vars * q.eval vars
  | _, ofRat' x, ofRat' y, _ => by simp
  | _, const p, const q, _ => by simp [eval_mul' p q]
  | _, const p, constAddXMul q r, _ => by
    simp [eval_mul' p q, eval_mul' (const p) r]; ring
  | _, constAddXMul p q, const r, _ => by
    simp [eval_mul' p r, eval_mul' q (const r)]; ring
  | _+1, constAddXMul p q, constAddXMul r s, _ => by
    simp [eval_mul' p r, eval_mul' (const p) s, eval_mul' q (const r), eval_mul' q s]
    ring
  termination_by n p q => (n, sizeOf p + sizeOf q)

@[simp]
theorem eval_mul : {n : ℕ} → (p : Poly n) → (q : Poly n) → (vars : Fin n → ℂ) →
    eval (p * q) vars = p.eval vars * q.eval vars :=
  eval_mul'

@[simp]
def neg : {n : ℕ} → (p : Poly n) → Poly n
  | _, ofRat' x => ofRat' (-x)
  | _, const p => const (neg p)
  | _, constAddXMul p q => constAddXMul (neg p) (neg q)

instance {n : ℕ} : Neg (Poly n) := ⟨Poly.neg⟩

@[simp]
theorem eval_neg' {n : ℕ} (p : Poly n) : (vars : Fin n → ℂ) →
    eval (neg p) vars = -p.eval vars := by
  induction p <;> simp_all [eval, add_comm]

@[simp]
theorem eval_neg {n : ℕ} (p : Poly n) : (vars : Fin n → ℂ) →
    eval (-p) vars = -p.eval vars :=
  eval_neg' p

instance : Sub (Poly n) := ⟨fun p q => p + -q⟩

@[simp]
theorem eval_sub {n : ℕ} (p q : Poly n) (vars : Fin n → ℂ) :
    eval (p - q) vars = p.eval vars - q.eval vars :=
  (eval_add p (-q) vars).trans <| by simp [sub_eq_add_neg]

def leadingCoeff : ∀ {n : ℕ}, Poly (n+1) → Poly n
  | _, const p => p
  | _, constAddXMul _ q => leadingCoeff q

open Mathlib Mathlib.Vector

def leadingMon : ∀ {n : ℕ}, Poly n → Vector ℕ n
  | _, ofRat' _ => Vector.nil
  | _, const p => 0 ::ᵥ leadingMon p
  | _, constAddXMul _ q =>
    match leadingMon q with
    | ⟨n :: l, h⟩ => ⟨(n+1) :: l, h⟩

def degree : ∀ {n : ℕ}, Poly n → ℕ
  | _, ofRat' _ => 0
  | _, const _ => 0
  | _, constAddXMul _ q => degree q + 1

def deriv : ∀ {n : ℕ}, Poly (n + 1) → Poly (n + 1)
  | _, constAddXMul _ q => q + constAddXMul' 0 (deriv q)
  | _, _ => 0

-- def gcd : ∀ {n : ℕ}, (p q : Poly n) →
--     Poly n × --the gcd
--     Poly n × --p / gcd
--     Poly n -- q / gcd
--   | _, ofRat' x, q => ⟨ofRat 1, ofRat' x, q⟩
--   | _, p, ofRat' x => ⟨ofRat 1, p, ofRat' x⟩
--   | _, const p, const q =>
--     let (g, a, b) := gcd p q
--     (const g, const a, const b)
--   | _, const p, constAddXMul r s =>
--     let (g, a, b) := gcd p r

def pseudoModDiv (nonzeroVars : Fin n)
    (p q : Poly n) : Option (Poly n × Poly n) :=
  let lp := leadingMon p
  let lq := leadingMon q


end Poly

open Poly

-- Invariants to maintain. No constant polys in any list. Eqs has smallest by lex leadingMon degree at head
structure Ands (n : ℕ) : Type where
  /-- A var is nonzero iff its index is < than `nonzeroVars` -/
  (nonzeroVars : Fin (n+1))
  (eqs : List (Poly (n+1)))
  (neq : Poly (n+1))
  deriving DecidableEq

namespace Ands

def eval {n : ℕ} (φ : Ands n) (vars : Fin (n+1) → ℂ) : Prop :=
  (∀ p ∈ φ.eqs, p.eval vars = 0) ∧ (φ.neq.eval vars ≠ 0)



def reduceEqs {n : ℕ} (φ : Ands n) : Ands n × Ands n := sorry

end Ands
