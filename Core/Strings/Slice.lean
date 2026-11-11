/-!
# 零拷贝的字符串切片 `StrView in a` 和静态的字符串字面量

现在的 `slice`、`split` 每取一段都复制成一个新的 `Str`，要分配一次。这里加上不拥有内存的切片：它指向一块缓冲区里的一段 `[off, off + len)`。

**设计**：缓冲区归 arena 所有（`text(a, s)` 把字符串放进 arena，`read_file_in(a, path)` 直接读进 arena），
切片的类型是 `StrView in a`，和 `&T in a` 一样挂在区域 `a` 上。所以“切片活不过缓冲区”就是已有的区域规则
（`Regions.*` 的证明）：区域里的值离不开它的 arena 块。不引入“借用某个变量”这种新概念，
缓冲区放进 arena 之后不再改动、不能移走，也就没有“借用期间被 push 导致重新分配”的问题（反例见一）。
这里证明区域规则之外新增的三件事。

## 一、下标和子切片
切片在它的缓冲区里（`View.ok`）；`sub(v, a, b)` 检查 `a ≤ b ≤ len`（否则 panic），结果仍在缓冲区里（`sub_ok`），
内容等于原切片内容的 `[a, b)`（`sub_content`），和现在复制一份的 `slice` 一样；`byte(v, i)` 读到的是缓冲区里
`off + i` 那个字节（`byte_ok`、`byte_content`）。`split`、`trim`、`lines` 都用 `sub` 实现，不需要另外证明。

## 二、arena 只增不改
arena 是一串缓冲区，只会在后面追加，整块一起释放（区域结束时）。追加之后，已有的切片仍然有效、读到的内容不变
（`grow_valid`、`grow_read`）；新追加的缓冲区上有覆盖整块的切片（`fresh_valid`、`fresh_read`）。

## 三、静态的字符串字面量
`Str` 的值要么是程序里的字面量（放在只读的静态存储里，不占堆），要么拥有一块堆内存。
- 字面量不分配；复制字面量还是字面量；析构字面量什么都不做；
- 要修改（`push`、`push_char`、`Bytes` 的 `set` 等）时，字面量先复制成堆上的字符串再改。
不变式：分配计数 = 现在拥有的值里堆字符串的个数（`reach_inv`）。所以析构一个堆字符串时计数至少是 1，
从不释放静态存储（`drop_exact`），所有值都析构以后计数是 0（`no_leak`）；内容和“全部在堆上”的表示一样（`observe_step`）。
-/

namespace Core.Strings.Slice

/-! ## 一、下标和子切片 -/

/-- 切片：缓冲区里从 `off` 开始的 `len` 个字节。 -/
structure View where
  off : Nat
  len : Nat
  deriving DecidableEq

/-- 切片在长度为 `n` 的缓冲区里。 -/
def View.ok (n : Nat) (v : View) : Prop := v.off + v.len ≤ n

def content {α : Type} (buf : List α) (v : View) : List α := (buf.drop v.off).take v.len

/-- 子切片 `[a, b)`：越界时没有结果（运行时 panic）。 -/
def sub (v : View) (a b : Nat) : Option View :=
  if a ≤ b ∧ b ≤ v.len then some ⟨v.off + a, b - a⟩ else none

/-- 第 `i` 个字节在缓冲区里的位置。 -/
def byte (v : View) (i : Nat) : Option Nat := if i < v.len then some (v.off + i) else none

theorem content_length {α : Type} {buf : List α} {v : View} (hv : v.ok buf.length) :
    (content buf v).length = v.len := by
  simp only [content, List.length_take, List.length_drop]
  unfold View.ok at hv
  omega

theorem sub_ok {n : Nat} {v w : View} {a b : Nat} (hv : v.ok n) (h : sub v a b = some w) : w.ok n := by
  unfold sub at h
  split at h
  · rename_i hab
    cases h
    unfold View.ok at *
    dsimp only
    omega
  · cases h

theorem sub_content {α : Type} {buf : List α} {v w : View} {a b : Nat} (h : sub v a b = some w) :
    content buf w = ((content buf v).drop a).take (b - a) := by
  unfold sub at h
  split at h
  · rename_i hab
    cases h
    apply List.ext_getElem?
    intro i
    simp only [content, List.getElem?_take, List.getElem?_drop]
    by_cases hi : i < b - a
    · have : a + i < v.len := by omega
      simp [hi, this, Nat.add_assoc]
    · simp [hi]
  · cases h

theorem byte_ok {n : Nat} {v : View} {i k : Nat} (hv : v.ok n) (h : byte v i = some k) : k < n := by
  unfold byte at h
  split at h
  · cases h
    unfold View.ok at hv
    omega
  · cases h

theorem byte_content {α : Type} {buf : List α} {v : View} {i : Nat} (hi : i < v.len) :
    (content buf v)[i]? = buf[v.off + i]? := by
  simp [content, List.getElem?_drop, hi]

-- "a,bc"：切片 [2, 4) 是 "bc"，它的 [1, 2) 是 "c"
example : sub ⟨0, 4⟩ 2 4 = some ⟨2, 2⟩ := by decide
example : content [97, 44, 98, 99] ⟨2, 2⟩ = [98, 99] := by decide
example : sub ⟨2, 2⟩ 1 2 = some ⟨3, 1⟩ := by decide
-- 越界的子切片被拒绝（panic）
example : sub ⟨2, 2⟩ 1 3 = none := by decide

/-! ### 反例：切片指向一个还能修改的 `Str`

缓冲区如果还能 `push`（重新分配、搬走）或者变短，原来的切片就指到缓冲区外面了。所以缓冲区要先放进 arena，
之后不再改动。 -/
example : View.ok 3 ⟨1, 2⟩ := by simp [View.ok]
example : ¬ View.ok 1 ⟨1, 2⟩ := by simp [View.ok]

/-! ## 二、arena 只增不改 -/

abbrev Arena (α : Type) := List (List α)

/-- arena 里的切片：第 `buf` 块缓冲区上的 `view`。 -/
structure Ref where
  buf : Nat
  view : View

def valid {α : Type} (A : Arena α) (r : Ref) : Prop := ∃ b, A[r.buf]? = some b ∧ r.view.ok b.length

def read {α : Type} (A : Arena α) (r : Ref) : Option (List α) := A[r.buf]?.map (fun b => content b r.view)

theorem grow_get {α : Type} {A : Arena α} {i : Nat} {b : List α} (h : A[i]? = some b) (c : List α) :
    (A ++ [c])[i]? = some b := by
  obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem?_append_left hl, h]

theorem grow_valid {α : Type} {A : Arena α} {r : Ref} (h : valid A r) (c : List α) : valid (A ++ [c]) r := by
  obtain ⟨b, hb, hv⟩ := h
  exact ⟨b, grow_get hb c, hv⟩

theorem grow_read {α : Type} {A : Arena α} {r : Ref} (h : valid A r) (c : List α) : read (A ++ [c]) r = read A r := by
  obtain ⟨b, hb, _⟩ := h
  simp only [read, grow_get hb c, hb]

theorem fresh_valid {α : Type} (A : Arena α) (c : List α) : valid (A ++ [c]) ⟨A.length, ⟨0, c.length⟩⟩ :=
  ⟨c, by simp, by unfold View.ok; simp⟩

theorem fresh_read {α : Type} (A : Arena α) (c : List α) : read (A ++ [c]) ⟨A.length, ⟨0, c.length⟩⟩ = some c := by
  simp [read, content]

/-- arena 里的切片取子切片，仍然有效。 -/
theorem sub_valid {α : Type} {A : Arena α} {r : Ref} {a b : Nat} {w : View} (h : valid A r)
    (hw : sub r.view a b = some w) : valid A ⟨r.buf, w⟩ := by
  obtain ⟨c, hc, hv⟩ := h
  exact ⟨c, hc, sub_ok hv hw⟩

/-! ## 三、静态的字符串字面量 -/

/-- `Str` 的值：字面量（静态存储）或者拥有一块堆内存。 -/
inductive S
  | lit (c : List Nat)
  | heap (c : List Nat)

def S.content : S → List Nat
  | .lit c => c
  | .heap c => c

/-- 占用几块堆内存。 -/
def S.w : S → Nat
  | .lit _ => 0
  | .heap _ => 1

theorem S.w_le (s : S) : s.w ≤ 1 := by cases s <;> simp [S.w]

/-- 拥有的值里堆字符串的个数。 -/
def hc (o : List S) : Nat := (o.map S.w).sum

/-- 状态：现在拥有的值、分配计数。字面量和 `make`（拼接、转换等新造的字符串）放到最后；
    复制：字面量还是字面量，堆字符串分配一块新的；修改：结果总在堆上，字面量要先分配；
    析构：堆字符串释放一块，字面量什么都不做。值在列表里的位置随意（`a ++ s :: b`）。 -/
inductive Step : List S × Nat → List S × Nat → Prop
  | lit (o : List S) (live : Nat) (c : List Nat) : Step (o, live) (o ++ [.lit c], live)
  | make (o : List S) (live : Nat) (c : List Nat) : Step (o, live) (o ++ [.heap c], live + 1)
  | clone (a b : List S) (s : S) (live : Nat) : Step (a ++ s :: b, live) (a ++ s :: b ++ [s], live + s.w)
  | push (a b : List S) (s : S) (t : List Nat) (live : Nat) :
      Step (a ++ s :: b, live) (a ++ .heap (s.content ++ t) :: b, live + (1 - s.w))
  | drop (a b : List S) (s : S) (live : Nat) : Step (a ++ s :: b, live) (a ++ b, live - s.w)

inductive Reach : List S × Nat → Prop
  | start : Reach ([], 0)
  | step {x y : List S × Nat} : Reach x → Step x y → Reach y

theorem step_inv {x y : List S × Nat} (h : x.2 = hc x.1) (st : Step x y) : y.2 = hc y.1 := by
  cases st with
  | lit o live c => simp [hc, S.w] at h ⊢ <;> omega
  | make o live c => simp [hc, S.w] at h ⊢ <;> omega
  | clone a b s live => simp [hc] at h ⊢ <;> omega
  | push a b s t live =>
    have := S.w_le s
    have hh : S.w (.heap (s.content ++ t)) = 1 := rfl
    dsimp only at h ⊢
    simp only [hc, List.map_append, List.map_cons, List.sum_append, List.sum_cons, hh] at h ⊢
    omega
  | drop a b s live => simp [hc] at h ⊢ <;> omega

/-- 分配计数总是等于拥有的堆字符串的个数。 -/
theorem reach_inv {x : List S × Nat} (h : Reach x) : x.2 = hc x.1 := by
  induction h with
  | start => simp [hc]
  | step _ st ih => exact step_inv ih st

/-- 析构时的减法是精确的：析构堆字符串时计数至少是 1，字面量不释放任何东西。 -/
theorem drop_exact {a b : List S} {s : S} {live : Nat} (h : Reach (a ++ s :: b, live)) :
    s.w ≤ live := by
  have h1 := reach_inv h
  dsimp only at h1
  have h2 : hc (a ++ s :: b) = hc a + s.w + hc b := by
    simp only [hc, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  omega

/-- 所有值都析构以后，没有泄漏。 -/
theorem no_leak {live : Nat} (h : Reach ([], live)) : live = 0 := by
  have := reach_inv h
  simpa [hc] using this

/-- 内容和“全部在堆上”的表示一样：每一步看到的内容按普通的字符串语义变化。 -/
inductive RStep : List (List Nat) → List (List Nat) → Prop
  | new (o : List (List Nat)) (c : List Nat) : RStep o (o ++ [c])
  | clone (a b : List (List Nat)) (c : List Nat) : RStep (a ++ c :: b) (a ++ c :: b ++ [c])
  | push (a b : List (List Nat)) (c t : List Nat) : RStep (a ++ c :: b) (a ++ (c ++ t) :: b)
  | drop (a b : List (List Nat)) (c : List Nat) : RStep (a ++ c :: b) (a ++ b)

def observe (o : List S) : List (List Nat) := o.map S.content

theorem observe_step {x y : List S × Nat} (st : Step x y) : RStep (observe x.1) (observe y.1) := by
  cases st with
  | lit o live c => simpa [observe, S.content] using RStep.new (observe o) c
  | make o live c => simpa [observe, S.content] using RStep.new (observe o) c
  | clone a b s live => simpa [observe] using RStep.clone (observe a) (observe b) s.content
  | push a b s t live => simpa [observe, S.content] using RStep.push (observe a) (observe b) s.content t
  | drop a b s live => simpa [observe] using RStep.drop (observe a) (observe b) s.content

/-! ### 反例：析构时总是 free

如果字面量也按“占一块堆内存”算（析构时 free），一个字面量的计数就和真实的分配数（0）不一致，
析构它会去 free 静态存储。 -/
example : hc [.lit [97]] = 0 := by decide
example : ([S.lit [97]].map (fun _ => 1)).sum ≠ 0 := by decide

end Core.Strings.Slice
