import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


--Macbeth Example 2.5.2
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have target_for_gt_case : 0 < x * (-t) := by --target_for_gt_case will get modified as it goes through the steps
      calc
        0 < -x * t := by addarith [hxt]
        _ = x * (-t) := by ring
    cancel x at target_for_gt_case --"0 < x * (-t)" becomes "0 < -t" because the second "hx" gives us "x > 0"
    have target_for_gt_case : t < 0 := by addarith [target_for_gt_case]
    apply ne_of_lt --this gets us "t ≠ 0"
    apply target_for_gt_case --I guess this wakes up the leprechauns so they actaully apply the previous line?


--Macbeth Example 2.5.6
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1 --this is for m
  use a --this is for n
  calc
    (a + 1)^2 - a^2 = 2 * a + 1 := by ring


--Macbeth Example 2.5.7
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2 --this is for x
  constructor
  · calc --first goal p < x
      p = (p + p) / 2 := by ring
      _ < (p + q) / 2 := by addarith [h]
  · calc --second goal x < q
      (p + q) / 2 < (q + q) / 2 := by addarith [h]
      _ = q := by ring
  

--Macbeth Example 2.5.9.5
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have x_is_neg_or_pos := le_or_gt x 0
  obtain x_is_neg | x_is_pos := x_is_neg_or_pos
  · use -x + 1 --if x <= 0, then use -x + 1 for y
    have neg_x_is_pos : -x ≥ 0 := by addarith [x_is_neg]
    calc
      (-x + 1)^2 = x^2 + -2 * x + 1 := by ring
      _ ≥ -2 * x + 1 := by extra --x^2 is always positive
      _ = 2 * (-x) + 1 := by ring
      _ ≥ 2 * 0 + 1 := by rel [neg_x_is_pos]
      _ > 0 := by extra --2 * 0 + 1 = 1 > 0
      _ ≥ x := by rel [x_is_neg]
  · use x + 1 --if x > 0, then use x + 1 for y
    calc
      (x + 1)^2 = x^2 + 2 * x + 1 := by ring
      _ ≥ 2 * x + 1 := by extra
      _ = x + x + 1 := by ring
      _ > 0 + x + 1 := by rel [x_is_pos]
      _ = x + 1 := by ring
      _ > x := by extra


--Macbeth Example 2.5.9.6
--we can transform this into Example 2.5.2
--That example was of the form "y * s < 0 |- s ≠ 0"
--With some rearrangement, this problem becomes "(a - 1) * (t - 1) < 0 |- (t - 1) ≠ 0"
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
    obtain ⟨x, hxt⟩ := h
    have hxt_rearranged : (x - 1) * (t - 1) < 0 := by
      calc
        (x - 1) * (t - 1) = x * t + 1 - (x + t) := by ring
        _ < (x + t) - (x + t) := by rel [hxt]
        _ = 0 := by ring
    --now we're ready to repeat the reasoning of 2.5.2
    have H := le_or_gt (x - 1) 0
    obtain x_part_is_leq | x_part_is_gt := H
    · have target_for_leq_case : 0 < -(x-1) * (t-1) := by addarith [hxt_rearranged] --target_for_leq_case will get modified as it goes through the steps
      have canceler_for_leq_case : 0 ≤ -(x-1) := by addarith [x_part_is_leq] --this won't be referenced, but I guess it's needed for the cancel step
      cancel -(x-1) at target_for_leq_case --now we have "0 < t - 1"
      have target_for_leq_case : 1 < t := by addarith [target_for_leq_case]
      apply ne_of_gt --this supposedly makes it t ≠ 1
      apply target_for_leq_case --and for some reason I need this line to actually do what the previous line was supposed to do
    · have target_for_gt_case : 0 < (x - 1) * (-(t - 1)) := by --target_for_gt_case will get modified as it goes through the steps
        calc
          0 < -(x - 1) * (t - 1) := by addarith [hxt_rearranged]
          _ = (x - 1) * (-(t - 1)) := by ring
      cancel (x - 1) at target_for_gt_case --now we're at "0 < -(t - 1)"
      have target_for_gt_case : t < 1 := by addarith [target_for_gt_case]
      apply ne_of_lt
      apply target_for_gt_case


--Macbeth Example 2.5.9.7
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, h2xm⟩ := h
  have H := le_or_gt x 2
  obtain x_leq_2 | x_gt_2 := H
  · have m_lt_5 : m < 5 := by
      calc
        m = 2 * x := by rw [h2xm]
        _ ≤ 2 * 2 := by rel [x_leq_2]
        _ = 4 + 0 := by numbers
        _ < 4 + 1 := by extra
        _ = 5 := by numbers
    apply ne_of_lt
    apply m_lt_5
  · have x_geq_3 : x ≥ 3 := by extra --yay! extra knows how integers work!
    have m_gt_5 : m > 5 := by
      calc
        m = 2 * x := by rw [h2xm]
        _ ≥ 2 * 3 := by rel [x_geq_3]
        _ = 5 + 1 := by numbers
        _ > 5 := by extra
    apply ne_of_gt
    apply m_gt_5