import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Mathlib.Tactic.IntervalCases
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

--first some necessary common definitions and theorems
--these are all copied from Macbeth sections preceding the problems where they're used
--search for "theorem problem" to jump to the actual problems
def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d

theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d

theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d

theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d

theorem thereexistsamod (a b : ℤ) (h : 0 < b) : ∃ r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  constructor
  · apply fmod_nonneg_of_pos a h
  constructor
  · apply fmod_lt_of_pos a h
  · use fdiv a b
    have Hab : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    addarith [Hab]

@[decreasing] theorem lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b := by
  have H : 0 ≤ fmod a b
  · apply fmod_nonneg_of_pos
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b) := by
  have H : 0 ≤ fmod a (-b)
  · apply fmod_nonneg_of_pos
    addarith [h1]
  have h2 : 0 < -b := by addarith [h1]
  calc b < 0 := h1
    _ ≤ fmod a (-b) := H

@[decreasing] theorem upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b := by
  apply fmod_lt_of_pos
  addarith [h1]

@[decreasing] theorem upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b := by
  apply fmod_lt_of_pos
  apply h1

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b

mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b))
  else if 0 ≤ a then
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b

theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH := L_mul_add_R_mul b (fmod a b) -- inductive hypothesis
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b < 0`
    have IH := L_mul_add_R_mul b (fmod a (-b)) -- inductive hypothesis
    have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b = 0`, `0 ≤ a`
    ring
  · -- case `b = 0`, `a < 0`
    ring
termination_by L_mul_add_R_mul a b => b

theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  use L a b, R a b
  apply L_mul_add_R_mul


--Macbeth 6.6.6.2
def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

theorem problem4a (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2
  · have IHA := problem4a (1 - n)
    rw[IHA]
    ring
  · have IHA := problem4a (-n)
    rw[IHA]
    ring
  · obtain hn | hn := lt_or_ge 0 n
    · contradiction
    · simp at h2
      have hsqueeze : 0 ^ 2 ≤ n ^ 2 ∧ n ^ 2 ≤ 0 ^ 2 := by
        constructor
        · rel[h2]
        · rel[hn]
      simp at hsqueeze
      addarith[hsqueeze]
  termination_by _ n => 3 * n - 1


--Macbeth 6.6.6.3
theorem uniqueness (a b : ℤ) (h : 0 < b) {r s : ℤ}
    (hr : 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs : 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]) : r = s := by
    obtain ⟨h0r, hrb, ⟨x, hx⟩⟩ := hr
    obtain ⟨h0s, hsb, ⟨y, hy⟩⟩ := hs
    have hmmm : r - s = b * (y - x) := by
      calc
        r - s = (a - s) - (a - r) := by ring
        _ = b * y - b * x := by rw[hx, hy]
        _ = b * (y - x) := by ring
    have hlo : 0 < 1 + y - x := by
      have hinter : -b < b * (y - x) := by
        calc
          -b < -s := by rel[hsb]
          _ = 0 - s := by ring
          _ ≤ r - s := by rel[h0r]
          _ = b * (y - x) := by rw[hmmm]
      have hinter : 0 < b * (1 + y - x) := by
        calc
          0 = b + (-b) := by ring
          _ < b + b * (y - x) := by rel[hinter]
          _ = b * (1 + y - x) := by ring
      cancel b at hinter
    have hlo : -1 < y - x := by addarith[hlo]
    have hhi : 0 < -(y - x - 1) := by
      have hinter : b * (y - x) < b := by
        calc
          b * (y - x) = r - s := by rw[hmmm]
          _ ≤ r - 0 := by rel[h0s]
          _ = r := by ring
          _ < b := by rel[hrb]
      have hinter : b * (y - x - 1) < 0 := by
        calc
          b * (y - x - 1) = b * (y - x) - b := by ring
          _ < b - b := by rel[hinter]
          _ = 0 := by ring
      have hinter : 0 < -b * (y - x - 1) := by addarith[hinter]
      have hinter : 0 < b * -(y - x - 1) := by
        calc
          0 < -b * (y - x - 1) := by rel[hinter]
          _ =b * -(y - x - 1) := by ring
      cancel b at hinter
    have hhi : y - x < 1 := by addarith[hhi]
    interval_cases y - x
    · simp at hmmm
      calc
        r = r - s + s := by ring
        _ = 0 + s := by rw[hmmm]
        _ = s := by ring

theorem problem4b (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  obtain ⟨r, hr⟩ := thereexistsamod a b h --"thereexistsamod" is copied from Macbeth Section 6.6.5
  use r
  dsimp
  constructor
  · apply hr
  --now the "exists" part is proven, just have to prove the "unique" part
  intro s hs
  apply uniqueness a b h hs hr --it really wanted hs before hr for some reason...


--Macbeth 6.7.3
--we start with some "helper" theorems, cuz lean is too busy smoking crack to do rewrites and rings properly

--scenario where:
----a = k2 + b * k1
----b = q * c1
----k2 = q * c2
----we wanna prove: a = q * (c2 + c1 * k1)
theorem factorhelper (a b c1 c2 k1 k2 q : ℤ) (ha : k2 + b * k1 = a) (hb : b = q * c1) (hk2 : k2 = q * c2) : a = q * (c2 + c1 * k1) := by
  calc
    a = k2 + b * k1 := by rw[ha]
    _ = q * c2 + b * k1 := by rw[hk2]
    _ = q * c2 + q * c1 * k1 := by rw[hb]
    _ = q * (c2 + c1 * k1) := by ring

--scenario where I wanna negate both sides
theorem neghelper (x y z : ℤ) (hx : x = y * z) : -x = y * (-z) := by
  calc
    -x = -(y * z) := by rw[hx]
    _ = y * (-z) := by ring

--now we're ready for the main theorem
theorem problem5a (a b : ℤ) : gcd a b ∣ b ∧ gcd a b ∣ a := by
  dsimp [(.∣.)] at * --this will simplify "∣" in all the following goals that I have to prove
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH : _ ∧ _ := problem5a b (fmod a b) -- inductive hypothesis
    obtain ⟨IH_right, IH_left⟩ := IH
    constructor
    · apply IH_left -- prove that `gcd a b ∣ b` - just do what the infoview says...
    · have hmeow := fmod_add_fdiv a b -- prove that `gcd a b ∣ a` -- breakdown a into b and (fmod a b)
      obtain ⟨c1, hc1⟩ := IH_left --breakdown b
      obtain ⟨c2, hc2⟩ := IH_right --breakdown (fmod a b)
      use (c2 + c1 * fdiv a b)
      apply factorhelper a b c1 c2 (fdiv a b) (fmod a b) (gcd b (fmod a b)) hmeow hc1 hc2
  · -- case `b < 0`
    have IH : _ ∧ _ := problem5a b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨IH_right, IH_left⟩ := IH
    constructor
    · apply IH_left -- prove that `gcd a b ∣ b` - just do what the infoview says...
    · have hmeow := fmod_add_fdiv a (-b) -- prove that `gcd a b ∣ a` -- same as the other "breakdown" proof above, but using -b instead of b
      obtain ⟨c1, hc1⟩ := IH_left
      obtain ⟨c2, hc2⟩ := IH_right
      have hc1 := neghelper b (gcd b (fmod a (-b))) c1 hc1
      use (c2 + (-c1) * fdiv a (-b))
      apply factorhelper a (-b) (-c1) c2 (fdiv a (-b)) (fmod a (-b)) (gcd b (fmod a (-b))) hmeow hc1 hc2
  · -- case `b = 0`, `0 ≤ a`
    constructor
    · interval_cases b -- prove that `gcd a b ∣ b` - just do what the infoview says...
      · use 0
        ring
    · use 1 -- prove that `gcd a b ∣ a` - just do what the infoview says...
      ring
  · -- case `b = 0`, `a < 0`
    constructor
    · interval_cases b -- prove that `gcd a b ∣ b` - just do what the infoview says...
      · use 0
        ring
    · use -1 -- prove that `gcd a b ∣ a` - just do what the infoview says...
      ring
termination_by problem5a a b => b


--Macbeth 6.7.7.1
theorem problem5b {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  obtain ⟨x, y, hxy⟩ := bezout a b
  obtain ⟨c1, hc1⟩ := ha
  obtain ⟨c2, hc2⟩ := hb
  use x * c1 + y * c2
  calc
    gcd a b = x * a + y * b := by rw[hxy]
    _ = x * (d * c1) + y * b := by rw[hc1]
    _ = x * (d * c1) + y * (d * c2) := by rw[hc2]
    _ = d * (x * c1 + y * c2) := by ring
