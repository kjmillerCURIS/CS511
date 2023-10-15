import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


--Macbeth 5.1.7.11
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intro hE --assume E x, P x, prove E x, Q x
    obtain ⟨x, hEx⟩ := hE
    use x
    have hPQx : P x ↔ Q x := h x
    obtain ⟨hPQx, hother⟩ := hPQx
    apply hPQx hEx 
  · intro hE --assume E x, Q x, prove E x, P x
    obtain ⟨x, hEx⟩ := hE
    use x
    have hQPx : P x ↔ Q x := h x
    obtain ⟨hother, hQPx⟩ := hQPx
    apply hQPx hEx


--Macbeth 5.1.7.12
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intro hE --left direction
    obtain ⟨x, y, hExy⟩ := hE
    use y, x
    apply hExy
  · intro hE --right direction
    obtain ⟨y, x, hEyx⟩ := hE
    use x, y
    apply hEyx


--Macbeth 5.1.7.13
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intro hA --left direction
    have hgoal : ∀ y x, P x y := by
      intro y x
      apply hA x y
    apply hgoal
  · intro hA --right direction
    have hgoal : ∀ x y, P x y := by
      intro x y
      apply hA y x
    apply hgoal


--Macbeth 5.1.7.14
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intro h --left direction
    obtain ⟨hE, hQ⟩ := h
    obtain ⟨x, hEx⟩ := hE
    use x
    constructor
    · apply hEx
    · apply hQ  
  · intro h --right direction
    obtain ⟨x, hExQ⟩ := h
    obtain ⟨hPx, hQ⟩ := hExQ
    constructor
    · use x
      apply hPx
    · apply hQ   


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3


--Macbeth 5.2.7.1
example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h1 : Tribalanced 1
  · use 1 --we assume that 1 is Tribalanced, so we only have to show that 2 isn't
    constructor
    · apply h1 --the "easy" part, where we already assumed the goal
    · by_cases h2 : Tribalanced (1 + 1) --need to show that 2 is not Tribalanced
      · have h21 := h2 1 --show that this one leads to a contradiction
        simp at h21 --makes it 1 + (1 + 1) < 3
        have h21 : 3 < 3 := by
          calc
            3 = 1 + (1 + 1) := by ring
            _ < 3 := by addarith[h21] --rel didn't work but addarith did, go figure...
        contradiction
      · apply h2
  · use (0 : ℝ)  --we assume that 1 isn't Tribalanced, so we only have to show that 0 is
    constructor
    · have hgoal : ∀ n : ℕ, (1 + (0 : ℝ) / n) ^ n < 3 := by --show that 0 is Tribalanced
        intro n
        obtain hn0 | hnpos := le_or_gt n 0
        · calc --zero case - use fact that zero-power is always 1
            (1 + (0 : ℝ) / n) ^ n = 1 := by ring
            _ < 1 + 2 := by extra
            _ = 3 := by numbers
        · calc --positive case - do normal algebra
            (1 + (0 : ℝ) / n) ^ n = 1 := by ring
            _ < 1 + 2 := by extra
            _ = 3 := by numbers
      apply hgoal
    · by_cases h01 : Tribalanced (0 + 1) --the "easy" part, except we have to remind lean that 0 + 1 = 1. Let's use a contradiction
      · simp at h01 --this turns 0 + 1 into 1, so we can get our contradiction
        contradiction
      · apply h01 --in this case we already assumed the thing we want to prove


def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)


theorem superpowered_one : Superpowered 1 := by
  intro n
  --conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  conv => ring_nf -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two


--Macbeth 5.2.7.3
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  · apply superpowered_one --this proves that Superpowered 1 is True
  · intro h -- h is Superpowered (1 + 1), which will hopefully lead to a contradiction
    have h5 := h 5
    obtain ⟨hother, hfactorimp⟩ := h5
    have hfactorimp641 := hfactorimp 641
    have hfactor641 : 641 ∣ (1 + 1) ^ (1 + 1) ^ 5 + 1 := by
      use 6700417
      calc
        (1 + 1) ^ (1 + 1) ^ 5 + 1 = 4294967297 := by numbers
        _ = 641 * 6700417 := by numbers
    have hmeow : 641 = 1 ∨ 641 = (1 + 1) ^ (1 + 1) ^ 5 + 1 := by apply hfactorimp641 hfactor641
    contradiction