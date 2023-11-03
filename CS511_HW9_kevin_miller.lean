import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


--Macbeth 6.2.7.4
def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · rw[B]
    numbers
  · rw[B]
    rw[IH]
    ring


--Macbeth 6.2.7.5
def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH --yes, the exact same code works for 4a and 4b!
  · rw[S]
    numbers
  · rw[S]
    rw[IH]
    ring


--extension of previous result
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  rw[problem4b] --2 - 1 / 2 ^ n ≤ 2
  simp --yep that does it


--Macbeth 6.2.7.8
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k IH
  · rw[factorial]
    rw[factorial]
    numbers
  · rw[factorial] --(k + 1 + 1) * (k + 1)! ≤ (k + 1 + 1) ^ (k + 1)
    have hkittycat : k + 1 ≤ k + 1 + 1 := by extra
    calc
      (k + 1 + 1) * (k + 1)! ≤ (k + 1 + 1) * (k + 1) ^ k := by rel[IH]
      _ ≤ (k + 1 + 1) * (k + 1 + 1) ^ k := by rel[hkittycat]
      _ = (k + 1 + 1) ^ (k + 1) := by ring


--Macbeth 6.3.6.4
def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  · rw[q]
    numbers
  · rw[q]
    numbers
  · rw[q, IH1, IH2]
    ring


--Macbeth 6.3.6.7
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · rw[r,r,r,r,r,r,r,r,r]
    numbers
  · rw[r,r,r,r,r,r,r,r,r,r]
    numbers
  · rw[r]
    calc
      2 * r (k + 1) + r k ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel[IH1, IH2]
      _ = 2 ^ (k + 1 + 1) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 1 + 1) := by extra


--Macbeth 6.4.3.1
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain heven | hodd := Nat.even_or_odd n
  · obtain ⟨k, hk⟩ := heven --heven case
    have hkpos : 0 < k := by addarith[hn, hk]
    have IH : ∃ a x, Odd x ∧ k = 2 ^ a * x := problem5c k hkpos
    obtain ⟨aa, xx, ⟨hmeow, hpurr⟩⟩ := IH
    use aa + 1, xx
    constructor
    · apply hmeow
    · rw[hk]
      ring
      rw[hpurr]
      ring
  · use 0, n --hodd case
    constructor
    · apply hodd
    · ring
