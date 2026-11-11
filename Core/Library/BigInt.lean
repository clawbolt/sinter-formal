/-!
# 大整数——`std.bigint`

`std.bigint` 用 Sinter 写：大整数是符号加上从低位到高位的一串“位”，每一位是 `0 ≤ d < 10^9` 的 I64。
基数取 10^9：一位乘一位再加两个进位最多 `(10^9-1)^2 + 2(10^9-1) < 10^18 < 2^63`，I64 不会溢出；
转成十进制时每一位正好补足 9 个数字。这里给出和 `std/bigint.sn` 一一对应的算法，证明它们算的是对的：

- `val l`：各位表示的自然数 `l₀ + B·l₁ + B²·l₂ + …`；`Digits l`：每一位都小于 `B`；
- `addL a b c`：逐位相加带进位，`val (addL a b c) = val a + val b + c`（`val_addL`）；
- `subL a b br`：逐位相减带借位，`val b + br ≤ val a` 时 `val (subL a b br) + val b + br = val a`（`val_subL`）；
- `mul1 a d c`：乘一位，`val (mul1 a d c) = val a * d + c`；
  `mulL a b`：从 `b` 的最高位开始，`acc = mul1 a bⱼ + acc 左移一位`，`val (mulL a b) = val a * val b`（`val_mulL`）；
- `cmpL n a b`：从高位往低位比，第一个不同的位决定大小，结果是 `-1`、`0`、`1`（`cmpL_spec`）；
- `divS a d`：从高位往低位除以一个小数 `0 < d ≤ B`，`val q * d + r = val a` 且 `r < d`（`val_divS`）；
- `trim l`：去掉高位的 0，值不变（`val_trim`）。

每个操作都保持“每一位小于 `B`”（`digits_*`），所以结果可以接着参加运算（减法和比较要用到这个前提）。

**带符号**：`Z` 是符号和各位，`toInt` 是它表示的整数。`addZ`（同号相加；异号时比较大小，大的减小的，
取大的那个的符号）、`negZ`、`subZ`、`mulZ` 都对：`toInt (addZ x y) = toInt x + toInt y` 等。
结果都经过 `norm`：去掉高位的 0，值是 0 时符号取正，所以 0 只有一种写法。
-/

namespace Core.Library.BigInt

/-- 基数 10^9（写成字面量，`omega` 才能把乘它、除以它、对它取余当成线性运算）。 -/
local notation "𝔹" => (1000000000 : Nat)

/-- 从低位到高位的各位表示的数。 -/
def val : List Nat → Nat
  | [] => 0
  | d :: ds => d + 𝔹 * val ds

/-- 每一位都小于基数。 -/
abbrev Digits (l : List Nat) : Prop := ∀ d ∈ l, d < 𝔹

theorem digits_head {d : Nat} {ds : List Nat} (h : Digits (d :: ds)) : d < 𝔹 := h d (by simp)

theorem digits_tail {d : Nat} {ds : List Nat} (h : Digits (d :: ds)) : Digits ds :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem digits_cons {d : Nat} {ds : List Nat} (h1 : d < 𝔹) (h2 : Digits ds) : Digits (d :: ds) := by
  intro x hx
  rcases List.mem_cons.1 hx with e | hx
  · rw [e]; exact h1
  · exact h2 x hx

/-! ## 加法 -/

/-- 把进位 `c` 加进各位 `ds`。 -/
def carry : List Nat → Nat → List Nat
  | [], c => if c = 0 then [] else [c]
  | d :: ds, c => (d + c) % 𝔹 :: carry ds ((d + c) / 𝔹)

theorem val_carry : ∀ (ds : List Nat) (c : Nat), val (carry ds c) = val ds + c
  | [], c => by
    by_cases h : c = 0
    · simp [carry, val, h]
    · simp [carry, val, h]
  | d :: ds, c => by
    simp only [carry, val, val_carry ds]
    omega

theorem digits_carry : ∀ (ds : List Nat) (c : Nat), Digits ds → c < 𝔹 → Digits (carry ds c)
  | [], c, _, hc => by
    by_cases h : c = 0
    · simp [carry, h, Digits]
    · simpa [carry, h, Digits] using hc
  | d :: ds, c, hd, hc => by
    have h1 := digits_head hd
    simp only [carry]
    exact digits_cons (Nat.mod_lt _ (by omega)) (digits_carry ds _ (digits_tail hd) (by omega))

/-- 逐位相加，`c` 是进位。一边的位用完以后，只把进位加进另一边剩下的位。 -/
def addL : List Nat → List Nat → Nat → List Nat
  | [], bs, c => carry bs c
  | a :: as, [], c => carry (a :: as) c
  | a :: as, b :: bs, c => (a + b + c) % 𝔹 :: addL as bs ((a + b + c) / 𝔹)

theorem val_addL : ∀ (as bs : List Nat) (c : Nat), val (addL as bs c) = val as + val bs + c
  | [], bs, c => by simp [addL, val_carry, val]
  | a :: as, [], c => by simp [addL, val_carry, val]
  | a :: as, b :: bs, c => by
    simp only [addL, val, val_addL as bs]
    omega

theorem digits_addL : ∀ (as bs : List Nat) (c : Nat), Digits as → Digits bs → c < 𝔹 →
    Digits (addL as bs c)
  | [], bs, c, _, hb, hc => by simp only [addL]; exact digits_carry bs c hb hc
  | a :: as, [], c, ha, _, hc => by simp only [addL]; exact digits_carry _ c ha hc
  | a :: as, b :: bs, c, ha, hb, hc => by
    have h1 := digits_head ha
    have h2 := digits_head hb
    simp only [addL]
    exact digits_cons (Nat.mod_lt _ (by omega))
      (digits_addL as bs _ (digits_tail ha) (digits_tail hb) (by omega))

/-! ## 减法 -/

/-- 从各位 `ds` 里减去借位 `br`。 -/
def borrow : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, br => if br ≤ d then (d - br) :: borrow ds 0 else (d + 𝔹 - br) :: borrow ds 1

theorem val_borrow : ∀ (ds : List Nat) (br : Nat), br ≤ 1 → Digits ds → br ≤ val ds →
    val (borrow ds br) + br = val ds
  | [], br, _, _, h => by
    simp only [borrow, val] at h ⊢
    omega
  | d :: ds, br, hb, hd, h => by
    have h1 := digits_head hd
    simp only [val] at h
    by_cases e : br ≤ d
    · have := val_borrow ds 0 (by omega) (digits_tail hd) (by omega)
      simp [borrow, e, val]
      omega
    · have := val_borrow ds 1 (by omega) (digits_tail hd) (by omega)
      simp [borrow, e, val]
      omega

theorem digits_borrow : ∀ (ds : List Nat) (br : Nat), br ≤ 1 → Digits ds → Digits (borrow ds br)
  | [], _, _, _ => by simp [borrow, Digits]
  | d :: ds, br, hb, hd => by
    have h1 := digits_head hd
    by_cases e : br ≤ d
    · simp only [borrow, ite_eq_left e]
      exact digits_cons (by omega) (digits_borrow ds 0 (by omega) (digits_tail hd))
    · simp only [borrow, ite_eq_right e]
      exact digits_cons (by omega) (digits_borrow ds 1 (by omega) (digits_tail hd))

/-- 逐位相减，`br` 是借位（0 或 1）。要求被减数不小于减数。 -/
def subL : List Nat → List Nat → Nat → List Nat
  | as, [], br => borrow as br
  | [], _ :: _, _ => []
  | a :: as, b :: bs, br =>
    if b + br ≤ a then (a - b - br) :: subL as bs 0 else (a + 𝔹 - b - br) :: subL as bs 1

theorem val_subL : ∀ (as bs : List Nat) (br : Nat), br ≤ 1 → Digits as → Digits bs →
    val bs + br ≤ val as → val (subL as bs br) + val bs + br = val as
  | as, [], br, hb, ha, _, h => by
    simp only [subL, val] at h ⊢
    have := val_borrow as br hb ha (by omega)
    omega
  | [], b :: bs, br, _, _, _, h => by
    simp only [subL, val] at h ⊢
    omega
  | a :: as, b :: bs, br, hb, ha, hbs, h => by
    have h1 := digits_head ha
    have h2 := digits_head hbs
    simp only [val] at h
    by_cases e : b + br ≤ a
    · have := val_subL as bs 0 (by omega) (digits_tail ha) (digits_tail hbs) (by omega)
      simp [subL, e, val]
      omega
    · have := val_subL as bs 1 (by omega) (digits_tail ha) (digits_tail hbs) (by omega)
      simp [subL, e, val]
      omega

theorem digits_subL : ∀ (as bs : List Nat) (br : Nat), br ≤ 1 → Digits as → Digits bs →
    Digits (subL as bs br)
  | as, [], br, hb, ha, _ => by simp only [subL]; exact digits_borrow as br hb ha
  | [], _ :: _, _, _, _, _ => by simp [subL, Digits]
  | a :: as, b :: bs, br, hb, ha, hbs => by
    have h1 := digits_head ha
    have h2 := digits_head hbs
    by_cases e : b + br ≤ a
    · simp only [subL, ite_eq_left e]
      exact digits_cons (by omega) (digits_subL as bs 0 (by omega) (digits_tail ha) (digits_tail hbs))
    · simp only [subL, ite_eq_right e]
      exact digits_cons (by omega) (digits_subL as bs 1 (by omega) (digits_tail ha) (digits_tail hbs))

/-! ## 乘法 -/

/-- 乘一位 `d`，再加上 `c`。 -/
def mul1 : List Nat → Nat → Nat → List Nat
  | [], _, c => if c = 0 then [] else [c]
  | x :: xs, d, c => (x * d + c) % 𝔹 :: mul1 xs d ((x * d + c) / 𝔹)

theorem val_mul1 : ∀ (xs : List Nat) (d c : Nat), val (mul1 xs d c) = val xs * d + c
  | [], d, c => by
    by_cases h : c = 0
    · simp [mul1, val, h]
    · simp [mul1, val, h]
  | x :: xs, d, c => by
    simp only [mul1, val, val_mul1 xs]
    have e : (x + 𝔹 * val xs) * d = x * d + 𝔹 * (val xs * d) := by
      rw [Nat.add_mul, Nat.mul_assoc]
    rw [e]
    generalize x * d = p
    generalize val xs * d = q
    omega

theorem digits_mul1 : ∀ (xs : List Nat) (d c : Nat), Digits xs → d < 𝔹 → c < 𝔹 → Digits (mul1 xs d c)
  | [], _, c, _, _, hc => by
    by_cases h : c = 0
    · simp [mul1, h, Digits]
    · simpa [mul1, h, Digits] using hc
  | x :: xs, d, c, hx, hd, hc => by
    have h1 := digits_head hx
    have hm : x * d ≤ 999999999 * 999999999 := Nat.mul_le_mul (by omega) (by omega)
    simp only [mul1]
    refine digits_cons (Nat.mod_lt _ (by omega)) (digits_mul1 xs d _ (digits_tail hx) hd ?_)
    generalize x * d = p at hm ⊢
    omega

/-- 从 `b` 的最高位开始：`acc = mul1 a bⱼ + acc 左移一位`（左移一位就是在最低位前面补一个 0）。 -/
def mulL (as : List Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => addL (mul1 as d 0) (0 :: mulL as ds) 0

theorem val_mulL (as : List Nat) : ∀ bs, val (mulL as bs) = val as * val bs
  | [] => by simp [mulL, val]
  | d :: ds => by
    simp only [mulL, val_addL, val_mul1, val, val_mulL as ds]
    have e : val as * (d + 𝔹 * val ds) = val as * d + 𝔹 * (val as * val ds) := by
      rw [Nat.mul_add, Nat.mul_left_comm]
    rw [e]
    generalize val as * d = p
    generalize val as * val ds = q
    omega

theorem digits_mulL (as : List Nat) (ha : Digits as) : ∀ bs, Digits bs → Digits (mulL as bs)
  | [], _ => by simp [mulL, Digits]
  | d :: ds, hb => by
    simp only [mulL]
    exact digits_addL _ _ 0 (digits_mul1 as d 0 ha (digits_head hb) (by omega))
      (digits_cons (by omega) (digits_mulL as ha ds (digits_tail hb))) (by omega)

/-! ## 比较 -/

def cmpNat (x y : Nat) : Int := if x < y then -1 else if x = y then 0 else 1

def hd0 : List Nat → Nat
  | [] => 0
  | d :: _ => d

def tl0 : List Nat → List Nat
  | [] => []
  | _ :: ds => ds

theorem val_split : ∀ l, val l = hd0 l + 𝔹 * val (tl0 l)
  | [] => by simp [val, hd0, tl0]
  | d :: ds => by simp [val, hd0, tl0]

theorem len_tl0 : ∀ l : List Nat, (tl0 l).length = l.length - 1
  | [] => rfl
  | _ :: _ => by simp [tl0]

theorem digits_hd0 : ∀ (l : List Nat), Digits l → hd0 l < 𝔹
  | [], _ => by simp [hd0]
  | _ :: _, h => digits_head h

theorem digits_tl0 : ∀ (l : List Nat), Digits l → Digits (tl0 l)
  | [], _ => by simp [tl0, Digits]
  | _ :: _, h => digits_tail h

/-- 比较前 `n` 位（不足的位当成 0）：先比更高的位，相等时再比最低位。也就是从高位往低位找第一个不同的位。 -/
def cmpL : Nat → List Nat → List Nat → Int
  | 0, _, _ => 0
  | n + 1, as, bs =>
    if cmpL n (tl0 as) (tl0 bs) = 0 then cmpNat (hd0 as) (hd0 bs) else cmpL n (tl0 as) (tl0 bs)

theorem cmpL_spec : ∀ (n : Nat) (as bs : List Nat), as.length ≤ n → bs.length ≤ n → Digits as → Digits bs →
    cmpL n as bs = cmpNat (val as) (val bs)
  | 0, as, bs, ha, hb, _, _ => by
    cases as <;> cases bs <;> simp_all [cmpL, cmpNat, val]
  | n + 1, as, bs, ha, hb, hda, hdb => by
    have ih := cmpL_spec n (tl0 as) (tl0 bs) (by rw [len_tl0]; omega) (by rw [len_tl0]; omega)
      (digits_tl0 _ hda) (digits_tl0 _ hdb)
    have h1 := digits_hd0 _ hda
    have h2 := digits_hd0 _ hdb
    simp only [cmpL]
    rw [ih, val_split as, val_split bs]
    rcases Nat.lt_trichotomy (val (tl0 as)) (val (tl0 bs)) with h | h | h
    · have a3 : hd0 as + 𝔹 * val (tl0 as) < hd0 bs + 𝔹 * val (tl0 bs) := by omega
      simp [cmpNat, h, a3]
    · rw [h]
      simp [cmpNat]
    · have a1 : ¬ val (tl0 as) < val (tl0 bs) := by omega
      have a2 : val (tl0 as) ≠ val (tl0 bs) := by omega
      have a3 : ¬ hd0 as + 𝔹 * val (tl0 as) < hd0 bs + 𝔹 * val (tl0 bs) := by omega
      have a4 : hd0 as + 𝔹 * val (tl0 as) ≠ hd0 bs + 𝔹 * val (tl0 bs) := by omega
      simp [cmpNat, a1, a2, a3, a4]

theorem cmpNat_neg {x y : Nat} (h : cmpNat x y = -1) : x < y := by
  unfold cmpNat at h
  by_cases h1 : x < y
  · exact h1
  · by_cases h2 : x = y
    · simp [h2] at h
    · simp [h1, h2] at h

theorem cmpNat_ge {x y : Nat} (h : ¬ cmpNat x y = -1) : y ≤ x := by
  unfold cmpNat at h
  by_cases h1 : x < y
  · simp [h1] at h
  · omega

/-! ## 除以一个小数 -/

/-- 从高位往低位除以 `d`：先除更高的位得到余数 `r`，再除 `r·B + 这一位`。结果是商的各位和余数。 -/
def divS : List Nat → Nat → List Nat × Nat
  | [], _ => ([], 0)
  | x :: xs, d => ((x + 𝔹 * (divS xs d).2) / d :: (divS xs d).1, (x + 𝔹 * (divS xs d).2) % d)

theorem val_divS (d : Nat) (hd : 0 < d) : ∀ xs : List Nat,
    val (divS xs d).1 * d + (divS xs d).2 = val xs ∧ (divS xs d).2 < d
  | [] => by simp [divS, val, hd]
  | x :: xs => by
    obtain ⟨h1, h2⟩ := val_divS d hd xs
    generalize hq : (divS xs d).1 = q at h1
    generalize hr : (divS xs d).2 = r at h1 h2
    simp only [divS, hq, hr, val]
    refine ⟨?_, Nat.mod_lt _ hd⟩
    have e1 := Nat.div_add_mod (x + 𝔹 * r) d
    have e2 : ((x + 𝔹 * r) / d + 𝔹 * val q) * d = d * ((x + 𝔹 * r) / d) + 𝔹 * (val q * d) := by
      rw [Nat.add_mul, Nat.mul_comm ((x + 𝔹 * r) / d) d, Nat.mul_assoc]
    rw [e2, ← h1]
    generalize (x + 𝔹 * r) / d = Q at e1 ⊢
    generalize (x + 𝔹 * r) % d = R at e1 ⊢
    generalize d * Q = p at e1 ⊢
    generalize val q * d = s
    omega

theorem digits_divS (d : Nat) (hd : 0 < d) : ∀ xs : List Nat, Digits xs → Digits (divS xs d).1
  | [], _ => by simp [divS, Digits]
  | x :: xs, hx => by
    have h1 := digits_head hx
    have h2 := (val_divS d hd xs).2
    simp only [divS]
    refine digits_cons ?_ (digits_divS d hd xs (digits_tail hx))
    rw [Nat.div_lt_iff_lt_mul hd]
    generalize (divS xs d).2 = r at h2 ⊢
    have : 𝔹 * r + 𝔹 ≤ 𝔹 * d := by omega
    omega

/-! ## 去掉高位的 0 -/

def trim : List Nat → List Nat
  | [] => []
  | d :: ds => if trim ds = [] ∧ d = 0 then [] else d :: trim ds

theorem val_trim : ∀ l, val (trim l) = val l
  | [] => rfl
  | d :: ds => by
    have ih := val_trim ds
    by_cases h : trim ds = [] ∧ d = 0
    · simp only [trim]
      rw [ite_eq_left h]
      obtain ⟨h1, h2⟩ := h
      rw [h1] at ih
      simp only [val] at ih ⊢
      omega
    · simp only [trim]
      rw [ite_eq_right h]
      simp only [val]
      rw [ih]

theorem digits_trim : ∀ l, Digits l → Digits (trim l)
  | [], _ => by simp [trim, Digits]
  | d :: ds, h => by
    by_cases e : trim ds = [] ∧ d = 0
    · simp only [trim]
      rw [ite_eq_left e]
      simp [Digits]
    · simp only [trim]
      rw [ite_eq_right e]
      exact digits_cons (digits_head h) (digits_trim ds (digits_tail h))

/-! ## 带符号的大整数 -/

structure Z where
  neg : Bool
  mag : List Nat

def toInt (z : Z) : Int := if z.neg then -(val z.mag : Int) else (val z.mag : Int)

/-- 去掉高位的 0；值是 0 时符号取正。 -/
def norm (s : Bool) (m : List Nat) : Z := ⟨if trim m = [] then false else s, trim m⟩

theorem toInt_norm (s : Bool) (m : List Nat) : toInt (norm s m) = toInt ⟨s, m⟩ := by
  have hv := val_trim m
  unfold norm toInt
  by_cases h : trim m = []
  · have : val m = 0 := by rw [← hv, h]; rfl
    simp [h, this, val]
  · simp [h, hv]

theorem digits_norm (s : Bool) (m : List Nat) (h : Digits m) : Digits (norm s m).mag := digits_trim m h

def negZ (x : Z) : Z := norm (!x.neg) x.mag

/-- 同号：各位相加，符号不变。异号：比较大小，大的减小的，符号取大的那个的。 -/
def addZ (x y : Z) : Z :=
  if x.neg = y.neg then norm x.neg (addL x.mag y.mag 0)
  else if cmpL (max x.mag.length y.mag.length) x.mag y.mag = -1 then norm y.neg (subL y.mag x.mag 0)
  else norm x.neg (subL x.mag y.mag 0)

def subZ (x y : Z) : Z := addZ x (negZ y)

def mulZ (x y : Z) : Z := norm (x.neg != y.neg) (mulL x.mag y.mag)

theorem toInt_negZ (x : Z) : toInt (negZ x) = - toInt x := by
  obtain ⟨s, a⟩ := x
  unfold negZ
  rw [toInt_norm]
  cases s <;> simp [toInt]

theorem toInt_addZ (x y : Z) (hx : Digits x.mag) (hy : Digits y.mag) :
    toInt (addZ x y) = toInt x + toInt y := by
  obtain ⟨s, a⟩ := x
  obtain ⟨t, b⟩ := y
  change Digits a at hx
  change Digits b at hy
  show toInt (if s = t then norm s (addL a b 0)
      else if cmpL (max a.length b.length) a b = -1 then norm t (subL b a 0)
      else norm s (subL a b 0)) = toInt ⟨s, a⟩ + toInt ⟨t, b⟩
  by_cases e : s = t
  · rw [ite_eq_left e, toInt_norm]
    have hv := val_addL a b 0
    cases s <;> cases t <;> simp [toInt, hv] at e ⊢ <;> omega
  · rw [ite_eq_right e]
    have hc := cmpL_spec (max a.length b.length) a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) hx hy
    by_cases lt : cmpL (max a.length b.length) a b = -1
    · rw [ite_eq_left lt, toInt_norm]
      rw [hc] at lt
      have hab := cmpNat_neg lt
      have hv := val_subL b a 0 (by omega) hy hx (by omega)
      cases s <;> cases t <;> simp [toInt] at e ⊢ <;> omega
    · rw [ite_eq_right lt, toInt_norm]
      rw [hc] at lt
      have hab := cmpNat_ge lt
      have hv := val_subL a b 0 (by omega) hx hy (by omega)
      cases s <;> cases t <;> simp [toInt] at e ⊢ <;> omega

theorem toInt_subZ (x y : Z) (hx : Digits x.mag) (hy : Digits y.mag) :
    toInt (subZ x y) = toInt x - toInt y := by
  unfold subZ
  rw [toInt_addZ x (negZ y) hx (digits_norm _ _ hy), toInt_negZ]
  omega

theorem toInt_mulZ (x y : Z) : toInt (mulZ x y) = toInt x * toInt y := by
  obtain ⟨s, a⟩ := x
  obtain ⟨t, b⟩ := y
  unfold mulZ
  rw [toInt_norm]
  cases s <;> cases t <;> simp [toInt, val_mulL, Int.natCast_mul, Int.neg_mul, Int.mul_neg]

/-- 每个运算的结果仍然每一位小于基数，可以接着算。 -/
theorem digits_addZ (x y : Z) (hx : Digits x.mag) (hy : Digits y.mag) : Digits (addZ x y).mag := by
  unfold addZ
  split
  · exact digits_norm _ _ (digits_addL _ _ 0 hx hy (by omega))
  · split
    · exact digits_norm _ _ (digits_subL _ _ 0 (by omega) hy hx)
    · exact digits_norm _ _ (digits_subL _ _ 0 (by omega) hx hy)

theorem digits_mulZ (x y : Z) (hx : Digits x.mag) (hy : Digits y.mag) : Digits (mulZ x y).mag :=
  digits_norm _ _ (digits_mulL _ hx _ hy)

/-! ## 例子 -/

-- 999999999 + 1 = 1 000000000（进位产生新的一位）
example : addL [999999999] [1] 0 = [0, 1] := by decide
-- 1 000000000 - 1 = 999999999（借位以后高位变成 0，trim 去掉）
example : trim (subL [0, 1] [1] 0) = [999999999] := by decide
-- (10^9 + 2) * 3 = 3 000000006
example : mulL [2, 1] [3] = [6, 3] := by decide

#eval toInt (mulZ ⟨true, [123456789, 12]⟩ ⟨false, [987654321, 98]⟩)
#eval toInt (addZ ⟨true, [5]⟩ ⟨false, [3]⟩)
#eval divS [7, 1] 3

end Core.Library.BigInt
