/-!
# S1：标准库 `std.math` 的规格和定律

标准库（C35）用 Sinter 写，所有权和区域的安全由 M1–M17 和翻译验证保证；这里管的是另一件事：**函数做的是不是它说的事**。
做法是先在 Lean 里写参考实现（规格），证明它满足的定律；`std/*.sn` 的实现照着规格逐行写，测试（test/c35.t）对拍。

- 整数是 `Int`；Sinter 的 I64 运算溢出时 panic（emit_c 的 `sn_add` 等），所以这里的定理只在不溢出时说话。
- `Ord` 的 `cmp` 返回 -1 / 0 / 1。一个 `cmp` 合格，要满足 `OrdLaws`：只取这三个值、反过来比是相反数、
  等于 0 恰好是相等（和 `Eq` 一致）、-1 可以传递。`min_of`、`max_of` 只依赖这几条。
- I64 和 Str 的 `cmp` 都满足 `OrdLaws`（`cmpI_laws`、`cmpL_laws`）；Str 按字节，模型是 `List Nat`。
-/

namespace Core.S1

/-- `Ord` 的定律。 -/
structure OrdLaws {α : Type} (cmp : α → α → Int) : Prop where
  range : ∀ a b, cmp a b = -1 ∨ cmp a b = 0 ∨ cmp a b = 1
  swap : ∀ a b, cmp b a = - cmp a b
  zero : ∀ a b, cmp a b = 0 ↔ a = b
  trans : ∀ a b c, cmp a b = -1 → cmp b c = -1 → cmp a c = -1

/-! ## I64 -/

/-- `impl Ord for I64`。 -/
def cmpI (a b : Int) : Int := if a < b then -1 else if a > b then 1 else 0

theorem cmpI_neg (a b : Int) : cmpI a b = -1 ↔ a < b := by
  unfold cmpI
  by_cases h1 : a < b <;> by_cases h2 : a > b <;> simp [h1, h2] <;> omega

theorem cmpI_laws : OrdLaws cmpI where
  range a b := by
    unfold cmpI
    by_cases h1 : a < b <;> by_cases h2 : a > b <;> simp [h1, h2]
  swap a b := by
    unfold cmpI
    by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega
  zero a b := by
    unfold cmpI
    by_cases h1 : a < b <;> by_cases h2 : b < a <;> simp [h1, h2] <;> omega
  trans a b c h1 h2 := by
    have g1 := (cmpI_neg a b).1 h1
    have g2 := (cmpI_neg b c).1 h2
    exact (cmpI_neg a c).2 (by omega)

/-! ## Str：按字节的字典序 -/

/-- `impl Ord for Str`：先逐个比字节，前面都相同时短的小。和 math.sn 的循环一致。 -/
def cmpL : List Nat → List Nat → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys => if x < y then -1 else if x > y then 1 else cmpL xs ys

theorem cmpL_range : ∀ (a b : List Nat), cmpL a b = -1 ∨ cmpL a b = 0 ∨ cmpL a b = 1
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | x :: xs, y :: ys => by
    have ih := cmpL_range xs ys
    by_cases h1 : x < y <;> by_cases h2 : y < x <;> simp [cmpL, h1, h2, ih]

theorem cmpL_swap : ∀ (a b : List Nat), cmpL b a = - cmpL a b
  | [], [] => by simp [cmpL]
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | x :: xs, y :: ys => by
    have ih := cmpL_swap xs ys
    by_cases h1 : x < y <;> by_cases h2 : y < x <;> simp [cmpL, h1, h2, ih] <;> omega

theorem cmpL_self : ∀ (a : List Nat), cmpL a a = 0
  | [] => by simp [cmpL]
  | x :: xs => by simp [cmpL, cmpL_self xs]

theorem cmpL_zero : ∀ (a b : List Nat), cmpL a b = 0 → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => by simp [cmpL]
  | _ :: _, [] => by simp [cmpL]
  | x :: xs, y :: ys => by
    intro h
    by_cases h1 : x < y
    · simp [cmpL, h1] at h
    by_cases h2 : y < x
    · simp [cmpL, h1, h2] at h
    have hxy : x = y := by omega
    simp [cmpL, h1, h2] at h
    rw [hxy, cmpL_zero xs ys h]

/-- 两个非空串比出 -1：首字节小，或者首字节相同、后面比出 -1。 -/
theorem cmpL_cons_neg (x y : Nat) (xs ys : List Nat) :
    cmpL (x :: xs) (y :: ys) = -1 ↔ x < y ∨ (x = y ∧ cmpL xs ys = -1) := by
  simp only [cmpL]
  by_cases h1 : x < y
  · simp [h1]
  · by_cases h2 : x > y
    · simp [h1, h2] <;> omega
    · have e : x = y := by omega
      subst e
      simp

theorem cmpL_trans : ∀ (a b c : List Nat), cmpL a b = -1 → cmpL b c = -1 → cmpL a c = -1
  | [], [], _ => by simp [cmpL]
  | [], _ :: _, [] => by simp [cmpL]
  | [], _ :: _, _ :: _ => by simp [cmpL]
  | _ :: _, [], _ => by simp [cmpL]
  | _ :: _, _ :: _, [] => by simp [cmpL]
  | x :: xs, y :: ys, z :: zs => by
    intro h1 h2
    rw [cmpL_cons_neg] at h1 h2 ⊢
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨by omega, cmpL_trans xs ys zs h1 h2⟩

theorem cmpL_laws : OrdLaws cmpL where
  range := cmpL_range
  swap := cmpL_swap
  zero a b := ⟨cmpL_zero a b, fun h => h ▸ cmpL_self a⟩
  trans := cmpL_trans

/-! ## min_of、max_of：只依赖定律 -/

/-- `min_of(a, b)`：`cmp(a, b) <= 0` 时取 a。 -/
def minOf {α : Type} (cmp : α → α → Int) (a b : α) : α := if cmp a b ≤ 0 then a else b

def maxOf {α : Type} (cmp : α → α → Int) (a b : α) : α := if cmp a b ≥ 0 then a else b

/-- min_of 的结果不大于两个实参，并且是其中之一。 -/
theorem minOf_spec {α : Type} {cmp : α → α → Int} (L : OrdLaws cmp) (a b : α) :
    cmp (minOf cmp a b) a ≤ 0 ∧ cmp (minOf cmp a b) b ≤ 0 ∧ (minOf cmp a b = a ∨ minOf cmp a b = b) := by
  have ha := (L.zero a a).2 rfl
  have hb := (L.zero b b).2 rfl
  have hs := L.swap a b
  unfold minOf
  by_cases h : cmp a b ≤ 0 <;> simp [h, ha, hb] <;> omega

theorem maxOf_spec {α : Type} {cmp : α → α → Int} (L : OrdLaws cmp) (a b : α) :
    cmp (maxOf cmp a b) a ≥ 0 ∧ cmp (maxOf cmp a b) b ≥ 0 ∧ (maxOf cmp a b = a ∨ maxOf cmp a b = b) := by
  have ha := (L.zero a a).2 rfl
  have hb := (L.zero b b).2 rfl
  have hs := L.swap a b
  unfold maxOf
  by_cases h : cmp a b ≥ 0 <;> simp [h, ha, hb] <;> omega

/-! ## 整数函数 -/

def minI (a b : Int) : Int := if a < b then a else b
def maxI (a b : Int) : Int := if a > b then a else b
def signI (n : Int) : Int := if n < 0 then -1 else if n > 0 then 1 else 0
def clampI (x lo hi : Int) : Int := maxI lo (minI x hi)

/-- `pow(b, e)` 的循环：r 从 1 开始乘 e 次。 -/
def powLoop (b : Int) : Nat → Int
  | 0 => 1
  | n + 1 => powLoop b n * b

theorem powLoop_eq (b : Int) (n : Nat) : powLoop b n = b ^ n := by
  induction n with
  | zero => simp [powLoop]
  | succ n ih => simp [powLoop, ih, Int.pow_succ]

/-- clamp 的结果在 [lo, hi] 里；x 本来就在里面时不变。要求 lo ≤ hi。 -/
theorem clamp_spec (x lo hi : Int) (h : lo ≤ hi) :
    lo ≤ clampI x lo hi ∧ clampI x lo hi ≤ hi ∧ (lo ≤ x → x ≤ hi → clampI x lo hi = x) := by
  unfold clampI maxI minI
  by_cases h1 : x < hi <;> simp [h1] <;> (by_cases h2 : lo > x <;> by_cases h3 : lo > hi) <;>
    simp [h2, h3] <;> omega

theorem sign_mul_abs (n : Int) : signI n * (if n < 0 then -n else n) = n := by
  unfold signI
  by_cases h1 : n < 0 <;> by_cases h2 : n > 0 <;> simp [h1, h2] <;> omega

end Core.S1
