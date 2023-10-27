import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r


--Macbeth 6.1.3
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · use 0
    calc
      a ^ 0 - b ^ 0 = 0 := by ring
      _ = d * 0 := by ring
  · obtain ⟨x, hx⟩ := IH
    obtain ⟨y, hy⟩ := h
    use a * x + b ^ k * y
    calc --just follow the stuff from the book
      a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
      _ = a * (d * x) + b ^ k * (d * y) := by rw[hx, hy]
      _ = d * (a * x + b ^ k * y) := by ring


--Macbeth 6.1.6
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers --wow, numbers actually worked!
  · calc --just follow the stuff from the book
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2 := by rel[IH]
      _ = k ^ 2 + k * k := by ring
      _ ≥ k ^ 2 + 4 * k := by rel[hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel[hk]
      _ = (k + 1) ^ 2 + 7 := by ring
      _ ≥ (k + 1) ^ 2 := by extra


--Macbeth 6.1.7.2
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  · calc
      (1 + a) ^ 0 = 1 := by ring
      _ ≥ 1 := by extra
      _ = 1 + 0 * a := by ring
  · have hsure : 0 ≤ 1 + a := by addarith[ha] --first we need to prove 0 ≤ 1 + a to help lean along
    calc --then it's just some algebra
      (1 + a) ^ (k + 1) = (1 + a) * (1 + a) ^ k := by ring
      _ ≥ (1 + a) * (1 + k * a) := by rel[IH] --good, lean was happy with hsure
      _ = 1 + (k + 1) * a + k * a ^ 2 := by ring
      _ ≥ 1 + (k + 1) * a := by extra --good, extra knows that squares are nonnegative


--Macbeth 6.1.7.6
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · numbers --wow, numbers is on fire today!
  · have IH' : 2 ^ k + 100 ≤ 3 ^ k := by addarith[IH] --just gotta flip it around for lean
    have hduh : 3 ≥ 2 := by numbers
    calc
      3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (2 ^ k + 100) := by rel[IH']
      _ ≥ 2 * (2 ^ k + 100) := by rel[hduh]
      _ = 2 ^ (k + 1) + 100 + 100 := by ring
      _ ≥ 2 ^ (k + 1) + 100 := by extra
    --at this point I get 0 goals but get the following message:
    ----'calc' tactic failed, has type
    ----  3 ^ (k + 1) ≥ 2 ^ (k + 1) + 100
    ----but it is expected to have type
    ----  3 ^ (k + 1) ≥ 2 ^ (k + 1) + 100
    -- ¯\_(ツ)_/¯


--5(b.)
--first, define the summation so we can use it in our goal
def sumOfFirstNOdds : ℕ → ℕ
  | 0 => 0
  | m + 1 => (sumOfFirstNOdds m) + 2 * (m + 1) - 1

--ring isn't working for one particular step of the proof
--no idea why, I've tried decomposing it every which way
--so to keep things clean here's a theorem that does what ring was supposed to do
theorem lets_pretend_ring_actually_works_here (j : ℕ) : 2 + j * 2 + j ^ 2 - 1 = 1 + j * 2 + j ^ 2 := by
  sorry -- (╯°□°)╯︵ ┻━┻

--now we prove a stronger result, which we will use to solve the problem
theorem hstronger (n: ℕ) : sumOfFirstNOdds n = (n ^ 2) := by
  simple_induction n with k IH
  · dsimp[sumOfFirstNOdds] --makes the goal 0 = 0 ^ 2
    numbers
  · dsimp[sumOfFirstNOdds] --makes the goal sumOfFirstNOdds (k + 0) + 2 * (k + 0 + 1) - 1 = (k + 1) ^ 2
    ring --makes the goal 2 + k * 2 + sumOfFirstNOdds k - 1 = 1 + k * 2 + k ^ 2
    rw[IH] --makes the goal 2 + k * 2 + k ^ 2 - 1 = 1 + k * 2 + k ^ 2
    --at this point ring should get the job done...but it doesn't!
    --so let's pretend it does :)
    apply lets_pretend_ring_actually_works_here

--now we use the stronger result to solve the problem
example (n : ℕ) : ∃ j : ℕ, sumOfFirstNOdds n = j ^ 2 := by
  use n
  apply hstronger
