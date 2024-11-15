import QuantElim.Poly.Basic

variable {n : ℕ}

inductive QuantFreeFormula (n : ℕ) : Type
  | true : QuantFreeFormula n
  | false : QuantFreeFormula n
  | neZero : Poly n → QuantFreeFormula n
  | eqZero : Poly n → QuantFreeFormula n
  | and : QuantFreeFormula n → QuantFreeFormula n → QuantFreeFormula n
  | or : QuantFreeFormula n → QuantFreeFormula n → QuantFreeFormula n

namespace QuantFreeFormula

@[simp]
def eval : QuantFreeFormula n → Set (Fin n → ℂ)
  | true => Set.univ
  | false => ∅
  | neZero p => { x | p.eval x ≠ 0 }
  | eqZero p => { x | p.eval x = 0 }
  | and φ ψ => eval φ ∩ eval ψ
  | or φ ψ => eval φ ∪ eval ψ

def not : QuantFreeFormula n → QuantFreeFormula n
  | true => false
  | false => true
  | neZero p => eqZero p
  | eqZero p => neZero p
  | and φ ψ => or (not φ) (not ψ)
  | or φ ψ => and (not φ) (not ψ)

@[simp]
theorem eval_not : ∀ φ : QuantFreeFormula n, eval (not φ) = (eval φ)ᶜ
  | true => by simp [not, eval]
  | false => by simp [not, eval]
  | neZero p => by simp [Set.ext_iff, not, eval, eval_not]
  | eqZero p => by simp [Set.ext_iff, not, eval, eval_not]
  | and p q => by simp [Set.ext_iff, not, eval, eval_not]; tauto
  | or p q => by simp [Set.ext_iff, not, eval, eval_not]

def iOrs {α : Type*} (l : List α) (f : α → QuantFreeFormula n) : QuantFreeFormula n :=
  l.foldr (fun a φ => (f a).or φ) false

@[simp]
theorem eval_ors  {α : Type*} (l : List α) (f : α → QuantFreeFormula n) :
    (iOrs l f).eval = ⋃ (a ∈ l), (f a).eval := by
  induction l with
  | nil => simp [iOrs, eval]
  | cons a l ih =>
    simp [iOrs, eval, ih, Set.ext_iff] at *
    simp [ih]

def ands {α : Type*} (l : List α) (f : α → QuantFreeFormula n) : QuantFreeFormula n :=
  l.foldr (fun a φ => (f a).and φ) true

@[simp]
theorem eval_ands {α : Type*} (l : List α) (f : α → QuantFreeFormula n) :
    (ands l f).eval = ⋂ (a ∈ l), (f a).eval := by
  induction l with
  | nil => simp [ands, eval]
  | cons a l ih =>
    simp [ands, eval, ih, Set.ext_iff] at *
    simp [ih]

open Poly

instance decidableEvalZero (x : Fin 0 → ℂ) : ∀ (φ : QuantFreeFormula 0), Decidable (x ∈ φ.eval)
  | true => isTrue trivial
  | false => isFalse not_false
  | neZero p => decidable_of_iff (toInt p ≠ 0)
      (by rcases p with ⟨⟨_⟩, _⟩; simp[Poly.eval, toInt])
  | eqZero p => decidable_of_iff (toInt p = 0)
      (by rcases p with ⟨⟨_⟩, _⟩; simp[Poly.eval, toInt])
  | and φ ψ => by
    have := decidableEvalZero x φ
    have := decidableEvalZero x ψ
    simp [eval]; infer_instance
  | or φ ψ =>  by
    have := decidableEvalZero x φ
    have := decidableEvalZero x ψ
    simp [eval]; infer_instance

end QuantFreeFormula
