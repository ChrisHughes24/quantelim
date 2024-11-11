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

theorem degree_mulConstMulXPow :  ∀ {n : ℕ} (p : Poly n) (m : ℕ) (q : Poly (n+1)),
     degree (mulConstMulXPow p m q) = degree q + m
  | _, p, 0, const q => by simp [degree, mulConstMulXPow]
  | _, p, 0, constAddXMul q r => by
    rw [degree, mulConstMulXPow, degree, degree_mulConstMulXPow]
  | _, p, m+1, q => by
    rw [mulConstMulXPow, degree, degree_mulConstMulXPow, add_assoc]

open Poly

theorem gcd_mod_wf {p q : Poly (n+1)} (lpd lqd : Poly n) (h : q.degree ≤ p.degree)
    (hq0 : q.degree ≠ 0) :
    ((lqd.mulConstMulXPow 0 p).eraseLead -
    (mulConstMulXPow lpd (p.degree - q.degree) q).eraseLead).degree < p.degree :=by
  refine lt_of_le_of_lt (degree_sub_le _ _) ?_
  simp only [max_lt_iff]
  refine ⟨lt_of_le_of_lt (degree_eraseLead _) ?_, lt_of_le_of_lt (degree_eraseLead _) ?_⟩
  . rw [degree_mulConstMulXPow, add_zero]
    exact lt_of_lt_of_le (Nat.sub_lt_self zero_lt_one (le_trans (Nat.one_le_iff_ne_zero.2 hq0) h)) le_rfl
  · erw [degree_mulConstMulXPow, Nat.add_sub_cancel' h]
    exact Nat.sub_lt_self zero_lt_one (le_trans (Nat.one_le_iff_ne_zero.2 hq0) h)

mutual

def contPrim : ∀ {n : ℕ} (p : Poly (n+1)), Poly n × Poly (n+1)
  | 0, const (ofInt' x) => (ofInt' x, 1)
  | _+1, const p =>
    let (pc, pp) := contPrim p
    (const pc, const pp)
  | _, constAddXMul p q =>
    let (c, q') := contPrim q
    let (g, a, b) := gCd p c
    (g, const a + const b * q')
  termination_by n p => (n+1, 0, sizeOf p)

-- This returns the gcd
def gCd : ∀ {n : ℕ} (p q : Poly n),
    Poly n × --the gcd
    Poly n × --p / gcd
    Poly n -- q / gcd
  | 0, ofInt' x, ofInt' y => ⟨(Int.gcd x y : ℤ),
    (x / Int.gcd x y : ℤ), (y / Int.gcd x y : ℤ)⟩
  | n+1, p, q =>
    if hq0 : q = 0 then (p, 1, 0)
    else
      let (pc, pp) := contPrim p
      let (k, h, ⟨r, hr⟩) := pseudoModDiv pp q
      have _wf : (if (r : Poly (n+1)) = 0 then 0 else 1 + (r : Poly (n+1)).degree) <
          (if q = 0 then 0 else 1 + q.degree) := by
        split_ifs with hr0
        · simp_all
        · by_cases hq0 : q.degree = 0
          · simp_all
          · simp only [add_lt_add_iff_left]
            exact hr.1 (Nat.pos_iff_ne_zero.2 hq0)
      let (g, a, b) := gCd q r
      -- Probably not correct, `g * (h * a + b) = k * pp`, so need to divide by k. It is divisible by `k`.
      let v := (pseudoModDiv (h * a + b) (const k)) -- v.1 is `1` or `-1` so multiplying is dividing.
      (g, v.2.1 * const v.1, a)
  termination_by n _ q => (n, 2, if q = 0 then 0 else 1 + degree q)

/-- returns `(k, h, r)` such that `k * p = h * q + r`, `k` and `h` are relatively prime
If `q ∣ p` then `k = 1 or -1` and `r = 0` -/
def pseudoModDiv : ∀ {n : ℕ} (p q : Poly (n+1)), (Poly n × Poly (n+1) ×
    {r : Poly (n+1) // (0 < q.degree → r.degree < q.degree) ∧ (q.degree = 0 → r = 0)}) :=
  fun p q =>
  let dp := degree p
  let dq := degree q
  let lp := p.leadingCoeff
  let lq := q.leadingCoeff
  let (g, lpd, lqd) := gCd lp lq
  if h : degree q ≤ degree p then
  if hp0 : p = 0 then (1, 0, ⟨0, by simp [degree]⟩ )
  else
    if hq0 : q.degree = 0 then (lqd, const lpd, ⟨0, by simp [degree]⟩)
    else
      let z := (mulConstMulXPow lpd (dp - dq) q).eraseLead
      have wf := gcd_mod_wf lpd lqd h hq0
      let (k, h, r) := pseudoModDiv ((mulConstMulXPow lqd 0 p).eraseLead - z) q
      (k * lqd, h + const (k * lpd) * X 0 ^(dp - dq), r)
  else (1, 0, ⟨p, ⟨fun _ => lt_of_not_ge h, fun hq0 => by simp [dp, dq, hq0] at h⟩⟩)
  termination_by n p => (n+1, 1, degree p)

end

theorem hom_ext {R : Type*} [CommRing R] {f g : Poly n → R}
    (hf₁ : ∀ ):

noncomputable def toMvPoly {n : ℕ} (p : Poly n) : MvPolynomial (Fin n) ℤ := eval p MvPolynomial.X

noncomputable def toPoly {n : ℕ} (p : Poly (n+1)) : Polynomial (MvPolynomial (Fin n) ℤ) :=
  (toMvPoly p).eval₂ (Int.castRingHom _)
  (Fin.cons Polynomial.X (fun i => Polynomial.C (MvPolynomial.X i)))

theorem eval₂_toMvPoly {R : Type} [CommRing R] {n : ℕ} (p : Poly n) (vars : Fin n → R) (f) :
    (toMvPoly p).eval₂ (f) vars = p.eval vars := by
  induction p with
  | ofInt' x =>
    rw [toMvPoly, ← MvPolynomial.coe_eval₂Hom, eval, map_intCast, eval]
  | const p ih =>
    rw [eval, ← ih]
    simp [toMvPoly]


@[simp]
theorem toMvPoly_X {n : ℕ} : toMvPoly (X : Poly (n+1)) = MvPolynomial.X 0 := by
  simp [X, toMvPoly]

@[simp]
theorem toMvPoly_const {n : ℕ} (p : Poly n) : toMvPoly (const p) =
    (toMvPoly p).rename Fin.succ := by
  induction p with
  | ofInt' => simp [toMvPoly]
  | const p ih =>
      rw [toMvPoly, eval]

@[simp]
theorem toPoly_X {n : ℕ} : toPoly (X : Poly (n+1)) = Polynomial.X := by
  simp [toPoly]

@[simp]
theorem toPoly_const {n : ℕ} (p : Poly n) : toPoly (const p) = Polynomial.C (toMvPoly p) := by
    simp [toPoly]
    induction p <;> simp_all [eval]

mutual

theorem toPoly_contPrim : ∀ {n : ℕ} (p : Poly (n+1)),
    let cp := contPrim p
    toMvPoly cp.1 • toPoly cp.2 = toPoly p ∧ (toPoly cp.2).IsPrimitive
  | 0, const (ofInt' x) => by
    simp [contPrim, toPoly, toMvPoly, Polynomial.smul_eq_C_mul]
  | _+1, const p => by
    simp [contPrim]
    have := toPoly_contPrim p
    dsimp at this
  | _, constAddXMul p q =>
    let (c, q') := contPrim q
    let (g, a, b) := gCd p c
    (g, const a + const b * q')


  termination_by n p => (n+1, 0, sizeOf p)

theorem toMvPoly_gCd : ∀ {n : ℕ} (p q : Poly n),
    let (g, a, b) := gCd p q
    toMvPoly g * toMvPoly a = toMvPoly p ∧
    toMvPoly g * toMvPoly b = toMvPoly q ∧
    ∀ k : MvPolynomial (Fin n) ℤ, k ∣ toMvPoly p → k ∣ toMvPoly q → k ∣ toMvPoly g := sorry
  termination_by n _ q => (n, 2, if q = 0 then 0 else 1 + degree q)

theorem toPoly_pseudoModDiv :  ∀ {n : ℕ} (p q : Poly (n+1)),
    let (k, h, r) := pseudoModDiv p q
    toMvPoly k • toPoly p = toPoly h * toPoly q + toPoly r
    ∧ toPoly q ∣ toPoly p → k = 1 ∨ k = -1 := sorry
  termination_by n p => (n+1, 1, degree p)

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
