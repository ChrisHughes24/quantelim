import QuantElim.QuantFreeFormula.Ands

namespace QuantFreeFormula

def elimQuantInContext {n : ℕ} : ∀ (Γ : Ands (n+1))
    (φ : QuantFreeFormula (n+1)),
    { ψ : QuantFreeFormula n //  ∀ x : Fin n → ℂ,
      x ∈ ψ.eval ↔ ∃ y : ℂ, (Fin.cons y x) ∈ Γ.eval ∩ φ.eval }
  | Γ, QuantFreeFormula.tru => ⟨Γ.elimQuant, by intro x; simp [Γ.elimQuant.2]⟩
  | Γ, QuantFreeFormula.fals => ⟨QuantFreeFormula.fals, by intro x; simp⟩
  | Γ, ite p φ ψ =>
    let ⟨φ', hφ⟩ := elimQuantInContext (Γ.insertEq p) φ
    let ⟨ψ', hψ⟩ := elimQuantInContext (Γ.insertNeq p) ψ
    ⟨φ'.or ψ', by simp [hφ, hψ, exists_or, and_or_left, and_assoc]⟩

def elimQuant {n : ℕ} (φ : QuantFreeFormula (n+1)) : QuantFreeFormula n :=
  (elimQuantInContext (Ands.true _) φ).1

def eval_elimQuant {n : ℕ} (φ : QuantFreeFormula (n+1)) :
    eval (elimQuant φ) = { x | ∃ y : ℂ, (Fin.cons y x) ∈ φ.eval } := by
  ext x
  rw [elimQuant, (elimQuantInContext (Ands.true _) φ).2]
  simp

end QuantFreeFormula
