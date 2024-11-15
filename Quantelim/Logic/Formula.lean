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
