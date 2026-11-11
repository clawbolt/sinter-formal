import Core.Library.Utf8

/-!
# UTF-8 的合法性检查——`str_from_utf8`

字节串 `Bytes` 存任意字节（`read_bytes` 读进来的就是它）。`str_from_utf8(b)` 只在 `b` 是合法的 UTF-8 时
返回 `.Some(s)`，否则 `.None`。检查和 `Library.Utf8` 的解码共用 `decode1`：每一轮解出一个字符 `c`，
再看 `encode c` 是不是正好是被吃掉的那几个字节（`valid`）。不合法的字节解成 `U+FFFD` 只吃一个字节，
而 `encode 0xFFFD` 是三个字节，所以对不上；真正写出来的 `U+FFFD`（EF BF BD）能对上。

**定理**：
- `valid_sound`：检查通过时，字节串正好是按字符解出来的那些字符的编码，而且都是合法字符；
- `valid_complete`：合法字符的编码一定能通过检查；
- `utf8_iff`：检查通过当且仅当字节串是某串合法字符的编码；
- `chars_of_utf8`：检查通过时，按字符遍历（`Library.Utf8` 的 `chars`）再编码回去得到原来的字节——
  所以 `str_from_utf8` 得到的字符串按字符遍历时没有替换字符以外的意外，转回 `Bytes` 也不变。
-/

namespace Core.Library.Utf8Check
open Core.Library.Utf8

/-- 合法性检查；`f` 是最多的轮数（取字节数就够）。 -/
def valid : Nat → List Nat → Bool
  | 0, bs => bs.isEmpty
  | f + 1, bs =>
    match decode1 bs with
    | some (c, r) => decide (encode c ++ r = bs) && valid f r
    | none => bs.isEmpty

def utf8 (bs : List Nat) : Bool := valid bs.length bs

theorem decode1_nil : decode1 [] = none := rfl

theorem valid_sound : ∀ (f : Nat) (bs : List Nat), valid f bs = true →
    encodeAll (decodeAll f bs) = bs ∧ ∀ c ∈ decodeAll f bs, Valid c
  | 0, bs, h => by
    simp [valid] at h
    subst h
    simp [decodeAll, encodeAll]
  | f + 1, bs, h => by
    cases hd : decode1 bs with
    | none =>
      simp [valid, hd] at h
      subst h
      simp [decodeAll, encodeAll, decode1_nil]
    | some p =>
      obtain ⟨c, r⟩ := p
      simp [valid, hd] at h
      obtain ⟨he, hr⟩ := h
      obtain ⟨e1, v1⟩ := valid_sound f r hr
      refine ⟨?_, ?_⟩
      · simp [decodeAll, hd, encodeAll, e1, he]
      · intro d hdm
        simp [decodeAll, hd] at hdm
        rcases hdm with rfl | hdm
        · exact decode1_valid hd
        · exact v1 d hdm

theorem valid_complete : ∀ (cs : List Nat), (∀ c ∈ cs, Valid c) →
    ∀ f, (encodeAll cs).length ≤ f → valid f (encodeAll cs) = true
  | [], _, f, _ => by cases f <;> simp [encodeAll, valid, decode1_nil]
  | c :: cs, hv, f, hf => by
    have hc : Valid c := hv c (by simp)
    have hcs : ∀ d ∈ cs, Valid d := fun d hd => hv d (by simp [hd])
    have hl := encode_ne_nil c
    simp only [encodeAll, List.length_append] at hf
    cases f with
    | zero => omega
    | succ f =>
      simp only [encodeAll, valid, dec_encode c hc]
      simp [valid_complete cs hcs f (by omega)]

/-- **检查通过当且仅当是合法字符的编码。** -/
theorem utf8_iff (bs : List Nat) : utf8 bs = true ↔ ∃ cs, (∀ c ∈ cs, Valid c) ∧ encodeAll cs = bs := by
  constructor
  · intro h
    obtain ⟨e, v⟩ := valid_sound _ _ h
    exact ⟨_, v, e⟩
  · rintro ⟨cs, hv, rfl⟩
    exact valid_complete cs hv _ (Nat.le_refl _)

/-- 检查通过的字节串，按字符遍历再编码回去不变。 -/
theorem chars_of_utf8 {bs : List Nat} (h : utf8 bs = true) :
    encodeAll (chars bs) = bs ∧ ∀ c ∈ chars bs, Valid c :=
  valid_sound _ _ h

/-! ## 例子 -/

-- "a中" 合法；单独的 0xFF、截断的 E4 B8、过长的 C0 80、代理区 ED A0 80 都不合法；写出来的 U+FFFD 合法
example : utf8 [0x61, 0xE4, 0xB8, 0xAD] = true := by decide
example : utf8 [0xFF] = false := by decide
example : utf8 [0xE4, 0xB8] = false := by decide
example : utf8 [0xC0, 0x80] = false := by decide
example : utf8 [0xED, 0xA0, 0x80] = false := by decide
example : utf8 [0xEF, 0xBF, 0xBD] = true := by decide

end Core.Library.Utf8Check
