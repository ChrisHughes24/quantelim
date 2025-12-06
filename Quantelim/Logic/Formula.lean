import QuantElim.Logic.Term
import Mathlib.Data.Fin.Tuple.Basic

variable {K : Type*} [Ring K]

inductive Formula : (freeVars : ℕ) → Type
  | eq {n : ℕ} : Term n → Term n → Formula n
  | not {n : ℕ} : Formula n → Formula n
  | and {n : ℕ} : Formula n → Formula n → Formula n
  | or {n : ℕ} : Formula n → Formula n → Formula n
  | implies {n : ℕ} : Formula n → Formula n → Formula n
  | iff {n : ℕ} : Formula n → Formula n → Formula n
  | all {n : ℕ} : Formula (n+1) → Formula n
  | ex {n : ℕ} : Formula (n+1) → Formula n
  | tru {n : ℕ} : Formula n
  | fals {n : ℕ} : Formula n

namespace Formula

def eval : {n : ℕ} → Formula n → (vars : Fin n → K) → Prop
  | _, eq t₁ t₂, vars => t₁.eval vars = t₂.eval vars
  | _, not φ, vars => ¬ eval φ vars
  | _, and φ₁ φ₂, vars => eval φ₁ vars ∧ eval φ₂ vars
  | _, or φ₁ φ₂, vars => eval φ₁ vars ∨ eval φ₂ vars
  | _, implies φ₁ φ₂, vars => eval φ₁ vars → eval φ₂ vars
  | _, iff φ₁ φ₂, vars => eval φ₁ vars ↔ eval φ₂ vars
  -- ∀ x0, x1, x2, x3, x4
  | _, all φ₁, vars => ∀ x, eval φ₁ (Fin.cons x vars)
  | _, ex φ₁, vars => ∃ x, eval φ₁ (Fin.cons x vars)
  | _, tru, _ => True
  | _, fals, _ => False

end Formula
