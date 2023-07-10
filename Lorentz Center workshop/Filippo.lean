import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

section fae

namespace Nat

open NNReal Real

/- # Let's start! -/

theorem Euclid_Thm ( n : ℕ ) : ∃ p, n ≤ p ∧ Prime p := by
let p := minFac (n ! + 1)
have f1 : n ! + 1 ≠ 1 := ne_of_gt <| succ_lt_succ <| factorial_pos _
have pp : Prime p := minFac_prime f1
have np : n ≤ p :=
  le_of_not_ge fun h =>
    have h₁ : p ∣ n ! := dvd_factorial (minFac_pos _) h
    have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
    pp.not_dvd_one h₂
exact ⟨p, np, pp⟩

#check Prime
#check Prime 2
#check Prime 4

#eval Prime 2
#eval Prime 4

example (p : ℕ) : Decidable (Prime p) := by
  exact decidablePrime p

example : Prime 37 := by
  norm_num

#check 1 + 1 = 2
#check ℕ
#check Prop
#check ℝ
#check ℕ → ℝ
#check π

#check exp
#check (exp)
#check @exp

#check exp = sin
#check (exp = sin)

#check ℕ
#check Prop
#check ℕ → Prop
#check ℕ → Type
#check ℕ → Type 4

#check Type → Prop
#check Type → Type
#check Type → Type 1
#check Type 1 → Type

#check Euclid_Thm
#check (Euclid_Thm)

#print axioms Euclid_Thm

def test : 1 + 1 = 2 := Eq.refl 2
#print axioms test

def sequence_of_Prop : ℕ → Prop :=  λ n => n ≥ 0
#check sequence_of_Prop
#check @sequence_of_Prop
