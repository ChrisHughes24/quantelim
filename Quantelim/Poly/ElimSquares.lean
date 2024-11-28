/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import QuantElim.Poly.Div
import QuantElim.forMathlib

namespace Poly

/-- Eliminates repeated factors, and also integer factors -/
def elimSquares : ∀ {n : ℕ}, Poly n → Poly n
  | 0, x => if toInt x = 0 then 0 else 1
  | n+1, p => by
    let c := cont p
    let pp := p / const c
    let d := gcd pp pp.deriv
    exact const (elimSquares c) * (pp / d)

theorem eval_elimSquares {R : Type*} [CommRing R] [IsDomain R] [CharZero R] : ∀ {n : ℕ}
    {x : Fin n → R} {p : Poly n}, (elimSquares p).eval x = 0 ↔ p.eval x = 0
  | 0, x, p => by
    rw [elimSquares]
    conv_rhs => rw [← intCast_toInt p, map_intCast]
    split_ifs with h0
    · simp only [map_zero, true_iff, h0, Int.cast_zero]
    · simpa
  | n+1, x, p => by
    rw [elimSquares]
    generalize hc : cont p = c
    rcases c with ⟨c, hc1⟩
    simp
    rcases exists_eq_mul_right_of_dvd hc1.1 with ⟨pp, hpp⟩
    subst hpp; clear hc hc1
    rw [eval_elimSquares, ← mul_eq_zero, ← eval_const, ← map_mul]
    rw [Poly.mul_div_cancel]
    let d := gcd pp pp.deriv
    have : x = Fin.cons (x 0) (fun i => x i.succ) := by
      ext i; induction i using Fin.cases <;> simp
    rw [this, eval_cons_eq_toPoly_eval, eval_cons_eq_toPoly_eval]
    let d := toPoly R (fun i : Fin n => x i.succ) d
    rw [iff_comm]
    by_cases hp0 : toPoly R (fun i : Fin n => x i.succ) p = 0
    · simp [hp0]
      have :=
    apply Polynomial.square_free_key
    · simp

example
end Poly
