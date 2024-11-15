import QuantElim.Poly.Basic

variable {n : ℕ}

inductive QuantFreeFormula (n : ℕ) : Type
  | tru : QuantFreeFormula n
  | fals : QuantFreeFormula n
  | ite : Poly n → QuantFreeFormula n → QuantFreeFormula n → QuantFreeFormula n

namespace QuantFreeFormula

def rel (p q : Poly n) : Prop :=
  0 < p.degree ∧ p.degree ≤ q.degree

instance : DecidableRel (@rel n) := fun _ _ => by dsimp [rel]; infer_instance

@[simp]
def eval : QuantFreeFormula n → Set (Fin n → ℂ)
  | tru => Set.univ
  | fals => ∅
  | ite p φ ψ => ({x | p.eval x = 0} ∩ φ.eval) ∪ ({x | p.eval x ≠ 0} ∩ ψ.eval)

def not : QuantFreeFormula n → QuantFreeFormula n
  | tru => fals
  | fals => tru
  | ite p φ ψ => ite p  (not φ) (not ψ)

@[simp]
theorem eval_not : ∀ φ : QuantFreeFormula n, eval (not φ) = (eval φ)ᶜ
  | tru => by simp [not, eval]
  | fals => by simp [not, eval]
  | ite p φ ψ => by
    ext x
    by_cases h : p.eval x = 0
    · simp [eval_not, h]
    · simp [eval_not, h]

def or : ∀ (_φ₁ _φ₂ : QuantFreeFormula n), QuantFreeFormula n
  | tru, _ => tru
  | _, tru => tru
  | fals, φ => φ
  | φ, fals => φ
  | ite p φ ψ, ite q χ ω =>
    if rel p q
    then ite p (ite q (φ.or χ) (φ.or ω)) (ite q (ψ.or χ) (ψ.or ω))
    else ite q (ite p (φ.or χ) (ψ.or χ)) (ite p (φ.or ω) (ψ.or ω))

@[simp]
theorem eval_or : ∀ φ₁ φ₂ : QuantFreeFormula n, eval (or φ₁ φ₂) = eval φ₁ ∪ eval φ₂
  | tru, _ => by simp [or, eval]
  | fals, fals => by simp [or, eval]
  | fals, tru => by simp [or, eval]
  | ite _ _ _, tru => by simp [or, eval]
  | fals, ite _ _ _ => by simp [or, eval]
  | ite _ _ _, fals => by simp [or, eval]
  | ite p φ ψ, ite q χ ω => by
    rw [or]
    ext x
    by_cases h1 : rel p q <;> by_cases h2 : p.eval x = 0 <;> by_cases h3 : q.eval x = 0
      <;> simp_all [eval, eval_or]

def and : ∀ (_φ₁ _φ₂ : QuantFreeFormula n), QuantFreeFormula n
  | fals, _ => fals
  | _, fals => fals
  | tru, φ => φ
  | φ, tru => φ
  | ite p φ ψ, ite q χ ω =>
    if rel p q
    then ite p (ite q (φ.and χ) (φ.and ω)) (ite q (ψ.and χ) (ψ.and ω))
    else ite q (ite p (φ.and χ) (ψ.and χ)) (ite p (φ.and ω) (ψ.and ω))

@[simp]
theorem eval_and : ∀ φ₁ φ₂ : QuantFreeFormula n, eval (and φ₁ φ₂) = eval φ₁ ∩ eval φ₂
  | fals, _ => by simp [and, eval]
  | tru, tru => by simp [and, eval]
  | tru, fals => by simp [and, eval]
  | ite _ _ _, tru => by simp [and, eval]
  | tru, ite _ _ _ => by simp [and, eval]
  | ite _ _ _, fals => by simp [and, eval]
  | ite p φ ψ, ite q χ ω => by
    rw [and]
    ext x
    by_cases h1 : rel p q <;> by_cases h2 : p.eval x = 0 <;> by_cases h3 : q.eval x = 0
      <;> simp_all [eval, eval_and]

def iOrs {α : Type*} (l : List α) (f : α → QuantFreeFormula n) : QuantFreeFormula n :=
  l.foldr (fun a φ => (f a).or φ) fals

@[simp]
theorem eval_ors  {α : Type*} (l : List α) (f : α → QuantFreeFormula n) :
    (iOrs l f).eval = ⋃ (a ∈ l), (f a).eval := by
  induction l with
  | nil => simp [iOrs, eval]
  | cons a l ih =>
    simp [iOrs, eval, ih, Set.ext_iff] at *
    simp [ih]

def iAnds {α : Type*} (l : List α) (f : α → QuantFreeFormula n) : QuantFreeFormula n :=
  l.foldr (fun a φ => (f a).and φ) tru

@[simp]
theorem eval_iAnds {α : Type*} (l : List α) (f : α → QuantFreeFormula n) :
    (iAnds l f).eval = ⋂ (a ∈ l), (f a).eval := by
  induction l with
  | nil => simp [iAnds, eval]
  | cons a l ih =>
    simp [iAnds, eval, ih, Set.ext_iff] at *
    simp [ih]

def neZero (p : Poly n) : QuantFreeFormula n := ite p fals tru

@[simp]
theorem eval_neZero (p : Poly n) : eval (neZero p) = {x | p.eval x ≠ 0} := by
  ext x
  simp [eval, neZero]

def eqZero (p : Poly n) : QuantFreeFormula n := ite p tru fals

@[simp]
theorem eval_eqZero (p : Poly n) : eval (eqZero p) = {x | p.eval x = 0} := by
  ext x
  simp [eval, eqZero]

open Poly

instance decidableEvalZero (x : Fin 0 → ℂ) : ∀ (φ : QuantFreeFormula 0), Decidable (x ∈ φ.eval)
  | tru => isTrue trivial
  | fals => isFalse not_false
  | ite p φ ψ =>
      have := decidableEvalZero x φ
      have := decidableEvalZero x ψ
      decidable_of_iff ((if toInt p = 0 then x ∈ φ.eval else x ∈ ψ.eval) = true)
        (by
          rcases p with ⟨⟨_⟩, _⟩
          split_ifs <;> simp [Poly.eval, toInt, *] <;> tauto)

end QuantFreeFormula
