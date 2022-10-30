import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.Have
import Mathlib.Tactic.Contrapose

/-- Criterion for an integer not to divide another. -/
lemma int.not_dvd_of_exists_lt_and_lt (a : ℤ) {b : ℤ} (hb : 0 < b)
  (h : ∃ q, b * q < a ∧ a < b * (q + 1)) :
    ¬b ∣ a := by
  intro ⟨q₀, H⟩
  rw [H] at h
  obtain ⟨q, hq₁, hq₂⟩ := h
  have h₁ : q + 1 ≤ q₀
  . contrapose! hq₁ with H
    apply Int.mul_le_mul_of_nonneg_left
    . exact Int.le_of_lt_add_one H
    . exact le_of_lt hb
  have h₂ : q₀ + 1 ≤ q + 1
  . contrapose! hq₂ with H
    apply Int.mul_le_mul_of_nonneg_left
    . apply Int.le_of_lt_add_one H
    . exact le_of_lt hb
  exact Int.lt_irrefl q₀ $ le_trans h₂ h₁
  
