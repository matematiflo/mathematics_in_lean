import Mathlib.GroupTheory.Commutator
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/- Rewrite and apply -/

example {G : Type} [Group G] (g h : G) : ⁅g, h⁆⁻¹ = ⁅h,g⁆ := by
  repeat rw [commutatorElement_def]
  repeat rw [mul_inv_rev]
  repeat rw [inv_inv]
  repeat rw [mul_assoc]
  done

open Real

example : Continuous (fun x ↦ (sin x)^2 ) := by continuity

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
  done
