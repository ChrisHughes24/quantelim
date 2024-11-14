import QuantElim.Poly.Div

namespace Poly

variable {n : ℕ} {R : Type*} [CommRing R] [dom : IsDomain R]

theorem eval_eq_zero_iff_of_associated {p q : Poly n} (h : Associated p q) {x : Fin n → R} :
    p.eval x = 0 ↔ q.eval x = 0 := by
  rcases h with ⟨u, rfl⟩
  simp
  cases isUnit_iff.1 u.isUnit <;> simp [*]

theorem eval_eq_zero_of_dvd {p q : Poly n} {x : Fin n → R} (h : p ∣ q) : p.eval x = 0 → q.eval x = 0 := by
  rcases h with ⟨r, rfl⟩
  simp; tauto

@[simp]
theorem eval_lcm_eq_zero {p q : Poly n} {x : Fin n → R} : eval x (lcm p q) = 0 ↔ eval x p = 0 ∨ eval x q = 0 := by
  rw [← mul_eq_zero, ← map_mul, ← eval_eq_zero_iff_of_associated (gcd_mul_lcm p q), map_mul, mul_eq_zero]
  simp only [iff_or_self]
  intro h
  exact eval_eq_zero_of_dvd (dvd_trans (gcd_dvd_left p q) (dvd_lcm_left p q)) h

theorem eval_pMod_eq_zero {q : Poly (n+1)} {x : Fin (n+1) → R}
    (hl : q.leadingCoeff.eval (fun i => x i.succ) ≠ 0)
    (hq : eval x q = 0) (p : Poly (n+1)) :
    (pMod p q).eval x = 0 ↔ p.eval x = 0 := by
  rw [pMod_eq_sub p q, map_sub, map_mul, map_mul, hq, mul_zero, sub_zero,
    mul_eq_zero, map_pow, eval_const]
  simp only [pow_eq_zero_iff', hl, ne_eq, false_and, false_or]

omit dom in
theorem eval_eraseLead_eq_zero {p : Poly (n+1)} {x : Fin (n+1) → R}
    (hl : p.leadingCoeff.eval (fun i => x i.succ) = 0) :
    p.eval x = 0 ↔ p.eraseLead.eval x = 0 := by
  simp [eraseLead, hl]

end Poly
