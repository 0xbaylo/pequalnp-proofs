import PEqualNP.Defs

-- CONTROL (ops-1, 2026-11-24): a deliberately wrong proof, a term of the wrong type. Never to be merged.
theorem PEqualNP.Outside.L_lib_123 : ∃ p q : ℕ, 1 ≤ p ∧ p < q ∧ PEqualNP.Library.FP3 p q := Nat.zero
