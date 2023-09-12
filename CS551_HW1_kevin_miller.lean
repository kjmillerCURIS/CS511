import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


axiom notnotE {p : Prop} (h : ¬ ¬ p) : p


--PROBLEM 3:


--part (a.) Slide 21
theorem Slide21 {p q r : Prop} (h : p ∧ q → r) : p → (q → r) := by
  intro hp
  intro hq
  have hpandq : p ∧ q := by apply And.intro hp hq
  apply h hpandq
  --that last line gave us r
  --and now the leprechauns magically close the box that started with "intro hq", so we get q -> r
  --and then they magically close the box that started with "intro hp", and so we get the conclusion!
  --thanks invisible leprechauns!


--part (b.) Slide 23
theorem Slide23 {p q r : Prop} (h : p → (q → r)) : (p → q) → (p → r) := by
  intro hpq
  intro hp
  have hq : q := by apply hpq hp
  have hqr : q → r := by apply h hp
  apply hqr hq
  --that last line gave us r
  --and now the leprechauns magically close the box that started with "intro hp", and so we get p -> r
  --and then they magically close the box that started with "intro hpq", and so we get the conclusion!
  --thanks invisible leprechauns!


--part (c.) Slide 24
theorem Slide24 {p q r : Prop} (h1 : p ∧ ¬q → r) (h2 : ¬r) (h3 : p) : q := by
  
  --time to use ⊥i
  have hnotnotq : ¬¬q := by
  {
    intro hnotq
    have hpandnotq : p ∧ ¬q := by apply And.intro h3 hnotq
    have hr : r := by apply h1 hpandnotq
    contradiction
  }

  --double-negative
  apply notnotE hnotnotq


--PROBLEM 4:


--part (a.) Macbeth 1.3.1
theorem Macbeth131 {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * 3 + 5 := by rw [h1, h2]
    _ = 11 := by ring


--part (b.) Macbeth 1.3.2
theorem Macbeth132 {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring


--part (c.) Macbeth 1.3.3
theorem Macbeth133 {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = (a - 5 * b) + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = -6 + 5 * (b + 2) := by ring
    _ = -6 + 5 * 3 := by rw [h2]
    _ = 9 := by ring