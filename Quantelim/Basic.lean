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
