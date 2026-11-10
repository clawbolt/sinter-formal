/-!
# S7：UTF-8——`Char` 和按字符遍历字符串

C48 加入字符类型 `Char`（一个 Unicode 标量值：小于 `0x110000`，不是代理区 `0xD800`–`0xDFFF`），
字符串 `Str` 仍然存 UTF-8 字节。这里给出编码和解码的规格，和 sinterc 生成的 C 代码一一对应：

- `encode n`：按码点大小写成 1–4 个字节（`str_push_char`）；
- `decode1 bs`：从字节串开头解出一个字符（`for c in s.chars()` 每一轮做的事）。
  不合法的字节（多余的续字节、过长的编码、代理区、超出范围、截断）解成替换字符 `U+FFFD`，只吃掉一个字节，
  所以任何字节串都能解完——`read_file`、`read_line` 读进来的不一定是合法的 UTF-8；
- `decodeAll`：一直解到末尾（`chars` 遍历的结果、`char_count` 数的个数）。

**定理**：
- `dec_encode`：合法的字符编码之后，`decode1` 正好解出它、剩下后面的字节；
- `decodeAll_encodeAll`：一串合法字符编码再解码，得到原来的字符串——所以字符串字面量、`str_push_char`
  拼出来的字符串，按字符遍历得到的就是写进去的那些字符；
- `push_chars`：在后面 `str_push_char(s, c)` 之后，按字符遍历多出正好一个 `c`；
- `decode1_valid`：解码得到的总是合法字符（包括替换字符），所以 `Char` 类型的值永远合法。
-/

namespace Core.S7

/-- Unicode 标量值。 -/
def Valid (n : Nat) : Prop := n < 0x110000 ∧ ¬(0xD800 ≤ n ∧ n ≤ 0xDFFF)

instance (n : Nat) : Decidable (Valid n) := by unfold Valid; exact inferInstance

def encode (n : Nat) : List Nat :=
  if n < 0x80 then [n]
  else if n < 0x800 then [0xC0 + n / 64, 0x80 + n % 64]
  else if n < 0x10000 then [0xE0 + n / 4096, 0x80 + n / 64 % 64, 0x80 + n % 64]
  else [0xF0 + n / 262144, 0x80 + n / 4096 % 64, 0x80 + n / 64 % 64, 0x80 + n % 64]

def decode1 : List Nat → Option (Nat × List Nat)
  | [] => none
  | b0 :: r =>
    if b0 < 0x80 then some (b0, r)
    else if 0xC2 ≤ b0 ∧ b0 < 0xE0 then
      match r with
      | b1 :: r' =>
        if 0x80 ≤ b1 ∧ b1 < 0xC0 then some ((b0 - 0xC0) * 64 + (b1 - 0x80), r') else some (0xFFFD, r)
      | [] => some (0xFFFD, r)
    else if 0xE0 ≤ b0 ∧ b0 < 0xF0 then
      match r with
      | b1 :: b2 :: r' =>
        if 0x80 ≤ b1 ∧ b1 < 0xC0 ∧ 0x80 ≤ b2 ∧ b2 < 0xC0 ∧
           0x800 ≤ (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) ∧
           ¬(0xD800 ≤ (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) ∧
             (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80) ≤ 0xDFFF)
        then some ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80), r') else some (0xFFFD, r)
      | _ => some (0xFFFD, r)
    else if 0xF0 ≤ b0 ∧ b0 < 0xF5 then
      match r with
      | b1 :: b2 :: b3 :: r' =>
        if 0x80 ≤ b1 ∧ b1 < 0xC0 ∧ 0x80 ≤ b2 ∧ b2 < 0xC0 ∧ 0x80 ≤ b3 ∧ b3 < 0xC0 ∧
           0x10000 ≤ (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80) ∧
           (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80) < 0x110000
        then some ((b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80), r')
        else some (0xFFFD, r)
      | _ => some (0xFFFD, r)
    else some (0xFFFD, r)

/-- 解到末尾；`f` 是最多的轮数（每一轮至少吃掉一个字节，取字节数就够）。 -/
def decodeAll : Nat → List Nat → List Nat
  | 0, _ => []
  | f + 1, bs =>
    match decode1 bs with
    | some (c, r) => c :: decodeAll f r
    | none => []

def encodeAll : List Nat → List Nat
  | [] => []
  | c :: cs => encode c ++ encodeAll cs

/-- 字符串按字符遍历的结果。 -/
def chars (bs : List Nat) : List Nat := decodeAll bs.length bs

/-! ## 编码再解码 -/

theorem encode_ne_nil (n : Nat) : (encode n).length ≥ 1 := by
  unfold encode
  repeat' split
  all_goals simp

theorem dec_encode (n : Nat) (hv : Valid n) (r : List Nat) : decode1 (encode n ++ r) = some (n, r) := by
  obtain ⟨h1, h2⟩ := hv
  unfold encode
  repeat' split
  all_goals
    simp only [List.cons_append, List.nil_append, decode1]
    repeat' (first | (exfalso; omega) | split)
    all_goals (simp only [Option.some.injEq, Prod.mk.injEq, and_true] <;> omega)

theorem encodeAll_append (cs ds : List Nat) : encodeAll (cs ++ ds) = encodeAll cs ++ encodeAll ds := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [encodeAll, ih]

theorem decodeAll_encodeAll : ∀ (cs : List Nat), (∀ c ∈ cs, Valid c) →
    ∀ f, (encodeAll cs).length ≤ f → decodeAll f (encodeAll cs) = cs
  | [], _, f, _ => by cases f <;> simp [encodeAll, decodeAll, decode1]
  | c :: cs, hv, f, hf => by
    have hc : Valid c := hv c (by simp)
    have hcs : ∀ d ∈ cs, Valid d := fun d hd => hv d (by simp [hd])
    have hl := encode_ne_nil c
    simp only [encodeAll, List.length_append] at hf
    cases f with
    | zero => omega
    | succ f =>
      simp only [encodeAll, decodeAll, dec_encode c hc]
      rw [decodeAll_encodeAll cs hcs f (by omega)]

/-- **字符串字面量、`str_push_char` 拼出来的字符串，按字符遍历得到的就是写进去的字符。** -/
theorem chars_encodeAll (cs : List Nat) (hv : ∀ c ∈ cs, Valid c) : chars (encodeAll cs) = cs :=
  decodeAll_encodeAll cs hv _ (Nat.le_refl _)

/-- `str_push_char(s, c)` 之后，按字符遍历多出正好一个 `c`。 -/
theorem push_chars (cs : List Nat) (c : Nat) (hv : ∀ d ∈ cs, Valid d) (hc : Valid c) :
    chars (encodeAll cs ++ encode c) = cs ++ [c] := by
  have e : encodeAll cs ++ encode c = encodeAll (cs ++ [c]) := by
    rw [encodeAll_append]; simp [encodeAll]
  rw [e]
  apply chars_encodeAll
  intro d hd
  simp at hd
  rcases hd with hd | hd
  · exact hv d hd
  · rw [hd]; exact hc

/-! ## 解出来的总是合法字符 -/

theorem decode1_valid {bs : List Nat} {c : Nat} {r' : List Nat} (h : decode1 bs = some (c, r')) : Valid c := by
  unfold decode1 at h
  repeat' split at h
  all_goals
    first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, _⟩ := h
       unfold Valid
       omega)
    | simp at h

/-! ## 例子 -/

-- '中' 是 U+4E2D：E4 B8 AD
#eval encode 0x4E2D
-- "a中😀" 编码再解码
#eval chars (encodeAll [0x61, 0x4E2D, 0x1F600])
-- 不合法的字节：0xFF、孤立的续字节 0x80、截断的 E4 B8，各解成一个 U+FFFD（65533），后面的照常解
#eval chars [0xFF, 0x41, 0x80, 0xE4, 0xB8]
-- 过长的编码 C0 80（本该是 1 个字节的 0）、代理区 ED A0 80：都不接受
#eval chars [0xC0, 0x80, 0xED, 0xA0, 0x80]

end Core.S7
