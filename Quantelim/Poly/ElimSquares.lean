import QuantElim.Poly.Div

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
  | _+1, x, p => by
    let c := cont p
    let pp := p / const c
    let d := gcd pp pp.deriv
    have : p.eval x = 0 → (gcd pp pp.deriv).eval x = 0 := sorry
    sorry


end Poly
