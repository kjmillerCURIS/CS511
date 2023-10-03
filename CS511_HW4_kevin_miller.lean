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
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


--Macbeth 3.1.4
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
    obtain ⟨x, hx⟩ := hn
    --7 * 2 * x + 7 - 4 = 2 * (7 * x + 1) + 1
    use 7 * x + 1
    calc
      7 * n - 4 = 7 * (2 * x + 1) - 4 := by rw[hx]
      _ = 2 * (7 * x + 1) + 1 := by ring


--Macbeth 3.1.6
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  --2 * 2 * i * j + 2 * i + 2 * j + 1 + 2 * y = 2 * (2 * i * j + i + j + y) + 1
  use 2 * i * j + i + j + y
  calc
    x * y + 2 * y = (2 * i + 1) * (2 * j + 1) + 2 * y := by rw[hi, hj]
    _ = 2 * (2 * i * j + i + j + y) + 1 := by ring


--Macbeth 3.1.8
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨x, hx⟩ := hn
  --thingy = 2 * 2 * x^2 + 2 * 2 * x - 5 = 2 * (2 * x^2 + 2 * x - 3) + 1
  use 2 * x^2 + 2 * x - 3
  calc
    n ^ 2 + 2 * n - 5 = (x + x) ^ 2 + 2 * (x + x) - 5 := by rw[hx]
    _ = 2 * (2 * x ^ 2 + 2 * x - 3) + 1 := by ring


--Macbeth 3.1.10.14
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  obtain a_minus_b_even | a_minus_b_odd := Int.even_or_odd (a - b)
  · left --if a - b is even then it's even, duhhhh
    obtain ⟨x, hx⟩ := a_minus_b_even
    use x
    calc
      a - b = 2 * x := by rw[hx]
      _ = x + x := by ring
  · obtain a_plus_c_even | a_plus_c_odd := Int.even_or_odd (a + c)
    · right
      left --if a + c is even, then it's even, duhhhh
      obtain ⟨x, hx⟩ := a_plus_c_even
      use x
      calc
        a + c = 2 * x := by rw[hx]
        _ = x + x := by ring
    · right
      right --now for the actual work - can we prove that b - c is even if the other things are odd?
      obtain ⟨i, hi⟩ := a_minus_b_odd
      obtain ⟨j, hj⟩ := a_plus_c_odd
      use (-i - j - 1 + a)
      calc
        b - c = -(a - b) - (a + c) + 2 * a := by ring
        _ = -(2 * i + 1) - (2 * j + 1) + 2 * a := by rw[hi, hj]
        _ = (-i - j - 1 + a) + (-i - j - 1 + a) := by ring


--Macbeth 4.1.3
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have hmid : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain hgeqa | hleqb := hmid
  · calc
      a = 2 * a - a := by ring
      _ ≤ 2 * ((a + b) / 2) - a := by rel[hgeqa]
      _ = b := by ring
  · calc
      a = 2 * ((a + b) / 2) - b := by ring
      _ ≤ 2 * b - b := by rel[hleqb]
      _ = b := by ring


--Macbeth 4.1.6
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -3
  intro x
  intro y
  intro h
  have hsq : (x + y)^2 ≤ (3)^2 := by
    calc
      (x + y)^2 ≤ (x + y)^2 + (x - y)^2 := by extra
      _ = 2 * (x^2 + y^2) := by ring
      _ ≤ 2 * 4 := by rel[h]
      _ ≤ 2 * 4 + 1 := by extra
      _ = 9 := by numbers
      _ = (3)^2 := by numbers
  have hpos : (0 : ℝ) ≤ (3 : ℝ) := by addarith
  have halmost : -3 ≤ x + y ∧ x + y ≤ 3 := by apply abs_le_of_sq_le_sq' hsq hpos
  obtain ⟨hgoal, hother⟩ := halmost
  addarith[hgoal] --makes it x + y >= -3
  

--Macbeth 4.1.10.2
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h5 : 1 ≤ 5 → 5 ≤ 5 → 5 ∣ n := hn 5
  simp at h5 --this lets us treat it as "5 | n"
  have h3 : 1 ≤ 3 → 3 ≤ 5 → 3 ∣ n := hn 3
  simp at h3 --this lets us treat it as "3 | n"
  obtain ⟨a, ha⟩ := h5
  obtain ⟨b, hb⟩ := h3
  use 2 * b - 3 * a
  calc
    n = 10 * n - 9 * n := by ring
    _ = 10 * (3 * b) - 9 * n := by rw[hb]
    _ = 10 * (3 * b) - 9 * (5 * a) := by rw[ha]
    _ = 30 * b - 45 * a := by ring
    _ = 15 * (2 * b - 3 * a) := by ring


--Macbeth 4.1.10.4
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  use 8
  intro x
  intro hxgeq8
  have halmost : x ^ 3 - 7 * x ^ 2 + 3 * x - 12 ≥ 0 := by
    calc
      x ^ 3 - 7 * x ^ 2 + 3 * x - 12 = (x - 7) * x ^ 2 + 3 * x - 12 := by ring
      _ ≥ (8 - 7) * x ^ 2 + 3 * 8 - 12 := by rel[hxgeq8]
      _ = x * x + 12 := by ring
      _ ≥ 8 * x + 12 := by rel[hxgeq8]
      _ ≥ 8 * 8 + 12 := by rel[hxgeq8]
      _ = 76 := by numbers
      _ ≥ 0 := by extra
  calc
    x ^ 3 + 3 * x = (x ^ 3 - 7 * x ^ 2 + 3 * x - 12) + (7 * x ^ 2 + 12) := by ring
    _ ≥ 0 + (7 * x ^ 2 + 12) := by rel[halmost]
    _ = 7 * x ^ 2 + 12 := by ring


--Macbeth 4.2.5
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro hleft --assume polynomial, derive roots
    have hfactored : (x + 3) * (x - 2) = 0 := by --common factoring that will be used for two different cancellations
      calc
        (x + 3) * (x - 2) = x ^ 2 + x - 6 := by ring
        _ = 0 := by rw[hleft]
        _ = 0 := by ring
    have H := le_or_gt x 0
    obtain hneg | hpos := H
    · left --if x <= 0 then x = -3
      have hfactored : (x + 3) * (x - 2) = 0 * (x - 2) := by --make it good for cancelling (x - 2)
        calc
          (x + 3) * (x - 2) = 0 := by rw[hfactored]
          _ = 0 * (x - 2) := by ring
      have hcancel : x - 2 < 0 := by
        calc
          x - 2 ≤ 0 - 2 := by rel[hneg]
          _ < 0 := by numbers
      have hcancel : x - 2 ≠ 0 := by
        apply ne_of_lt
        apply hcancel
      cancel (x - 2) at hfactored
      addarith [hfactored]
    · right --if x > 0 then x = 2
      have hfactored : (x - 2) * (x + 3) = 0 * (x + 3) := by --make it good for cancelling (x + 3)
        calc
          (x - 2) * (x + 3) = (x + 3) * (x - 2) := by ring
          _ = 0 := by rw[hfactored]
          _ = 0 * (x + 3) := by ring
      have hcancel : x + 3 > 0 := by
        calc
          x + 3 > 0 + 3 := by rel[hpos]
          _ > 0 := by numbers
      have hcancel : x + 3 ≠ 0 := by
        apply ne_of_gt
        apply hcancel
      cancel (x + 3) at hfactored
      addarith [hfactored]
  · intro hright --assume roots, derive polynomial
    obtain ha | hb := hright
    · calc --x = -3
        x ^ 2 + x - 6 = (-3) ^ 2 + (-3) - 6 := by rw[ha]
        _ = 0 := by numbers
    · calc --x = 2
        x ^ 2 + x - 6 = (2) ^ 2 + (2) - 6 := by rw[hb]
        _ = 0 := by numbers

    
--Macbeth 4.2.6
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  · intro hleft --assume polynomial, derive roots
    have hsq : (2 * a - 5) ^ 2 ≤ 1 ^ 2 := by
      calc
        (2 * a - 5) ^ 2 = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5 := by rel[hleft]
        _ = 1 ^ 2 := by ring
    have hpos : (0 : ℤ) ≤ (1 : ℤ) := by addarith
    have hbound : -1 ≤ 2 * a - 5 ∧ 2 * a - 5 ≤ 1 := by apply abs_le_of_sq_le_sq' hsq hpos
    --we now need to show that 2 <= a <= 3
    --then we can use interval_cases to magically do what we want to do!
    obtain ⟨hlower, hupper⟩ := hbound
    have hlower : 4 ≤ 2 * a := by addarith[hlower]
    have hlower : 2 * 2 ≤ 2 * a := by
      calc
        2 * 2 = 4 := by numbers
        _ ≤ 2 * a := by rel[hlower]
    cancel 2 at hlower --this proves 2 <= a
    have hupper : 2 * a ≤ 6 := by addarith[hupper]
    have hupper : 2 * a ≤ 2 * 3 := by
      calc
        2 * a ≤ 6 := by rel[hupper]
        _ = 2 * 3 := by numbers
    cancel 2 at hupper --this proves a <= 3
    --we're now ready for some leprechaun magic!
    interval_cases a
    · left
      numbers
    · right
      numbers
  · intro hright --assume roots, derive polynomial
    obtain ha | hb := hright
    · calc --a = 2
        a ^ 2 - 5 * a + 5 = 2 ^ 2 - 5 * 2 + 5 := by rw[ha]
        _ ≤ -1 := by extra
    · calc --a = 3
        a ^ 2 - 5 * a + 5 = 3 ^ 2 - 5 * 3 + 5 := by rw[hb]
        _ ≤ -1 := by extra