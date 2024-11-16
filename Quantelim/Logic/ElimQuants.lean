import QuantElim.QuantFreeFormula.ElimQuant
import QuantElim.Logic.Formula

variable {n : ℕ}

def Term.toPoly : {n : ℕ} → Term n → Poly n
  | _, Term.ofInt q => q
  | _, Term.var i => Poly.X i
  | _, Term.add t₁ t₂ => (Term.toPoly t₁) + (Term.toPoly t₂)
  | _, Term.mul t₁ t₂ => (Term.toPoly t₁) * (Term.toPoly t₂)
  | _, Term.neg t => - (Term.toPoly t)
  | _, Term.sub t₁ t₂ => (Term.toPoly t₁) - (Term.toPoly t₂)

@[simp]
theorem Term.eval_toPoly {R : Type*} [CommRing R] (x : Fin n → R) (t : Term n) :
    (Term.toPoly t).eval x = t.eval (fun i => x i) := by
  induction t <;> simp [Term.toPoly, Term.eval, *]

namespace Formula

open QuantFreeFormula

def elimQuants : {n : ℕ} → Formula n → QuantFreeFormula n
  | _, tru => QuantFreeFormula.tru
  | _, fals => QuantFreeFormula.fals
  | _, eq t₁ t₂ => eqZero (Term.toPoly t₁ - Term.toPoly t₂)
  | _, not φ => (elimQuants φ).not
  | _, and φ₁ φ₂ => (elimQuants φ₁).and (elimQuants φ₂)
  | _, or φ₁ φ₂ => (elimQuants φ₁).or (elimQuants φ₂)
  | _, implies φ₁ φ₂ => (elimQuants φ₁).not.or (elimQuants φ₂)
  | _, iff φ₁ φ₂ => ((elimQuants φ₁).and (elimQuants φ₂)).or ((elimQuants φ₁).not.and (elimQuants φ₂).not)
  | _, all φ => (elimQuant (elimQuants φ).not).not
  | _, ex φ => elimQuant (elimQuants φ)

theorem eval_elimQuants (φ : Formula n) :
   (elimQuants φ).eval = {x | φ.eval x } := by
  ext x
  induction φ <;> simp [elimQuants, eval, *, sub_eq_zero, eval_elimQuant,
    iff_iff_and_or_not_and_not] at *; tauto

instance (x : Fin 0 → ℂ) (φ : Formula 0) : Decidable (φ.eval x) := by
  have := Set.ext_iff.1 (eval_elimQuants φ) x
  simp at this
  rw [← this]
  infer_instance

open Term

#eval
  let φ : Formula 0 := all $ all $
    (eq (var 0 * var 0) (var 1 * var 1)).implies (or (eq (var 0) (var 1)) (eq (var 0) (neg (var 1))))
  decide (φ.eval (Fin.elim0 : Fin 0 → ℂ))

end Formula
