/-!
# M28：逐块读行

C62 的 `read_file_in` 一次读完整个文件，峰值内存和文件一样大。C63 逐块读（`read_chunk`）：上一块最后一个换行之后
不完整的部分（`carry`）留下来，接在下一块前面，从头切；完整的行交出去，新的不完整部分再留到下一块。
每一块在自己的内层 arena 里处理，所以峰值内存只和块大小、最长的一行有关，和文件大小无关。

这里证明：**不管输入怎么切成块**，逐块得到的行和整个文件一次读进来再切（`view.lines` 的语义）完全相同（`stream_eq`）。
关键的不变式是留下的 `carry` 里没有换行（`carry_noNl`）：所以把它接在下一块前面从头切，等于接着上一块的状态往下切
（`chunkStep_eq`）。反例：每块各自切行、不留 `carry` 的话，跨块的行会被切成两行。

模型：字节是任意类型 `α` 的元素，换行是 `nl`。切行的状态是（已经完整的行，当前这一行已经读到的部分）；
最后一行后面没有换行时也算一行，空的输入没有行，和 `std.view` 的 `lines` 相同（行尾的 `\r` 另外去掉，这里不涉及）。
-/

namespace Core.M28

variable {α : Type} [DecidableEq α] (nl : α)

/-- 读一个字节：是换行就把当前这一行交出去，否则接在当前这一行后面。 -/
def step (st : List (List α) × List α) (x : α) : List (List α) × List α :=
  if x = nl then (st.1 ++ [st.2], []) else (st.1, st.2 ++ [x])

def scan (st : List (List α) × List α) (xs : List α) : List (List α) × List α := xs.foldl (step nl) st

/-- 读完以后：当前这一行不空时也是一行。 -/
def finish (st : List (List α) × List α) : List (List α) := if st.2 = [] then st.1 else st.1 ++ [st.2]

/-- 整个文件读进来再切。 -/
def lines (xs : List α) : List (List α) := finish (scan nl ([], []) xs)

/-- 逐块：上一块留下的 `carry` 接在这一块前面，从头切；完整的行交出去，不完整的部分留到下一块。 -/
def chunkStep (st : List (List α) × List α) (c : List α) : List (List α) × List α :=
  (st.1 ++ (scan nl ([], []) (st.2 ++ c)).1, (scan nl ([], []) (st.2 ++ c)).2)

def stream (cs : List (List α)) : List (List α) := finish (cs.foldl (chunkStep nl) ([], []))

theorem scan_cons (st : List (List α) × List α) (x : α) (xs : List α) :
    scan nl st (x :: xs) = scan nl (step nl st x) xs := rfl

theorem scan_append (st : List (List α) × List α) (xs ys : List α) :
    scan nl st (xs ++ ys) = scan nl (scan nl st xs) ys := by
  simp only [scan, List.foldl_append]

/-- 已经完整的行只是前缀，不影响后面怎么切。 -/
theorem scan_prefix (xs : List α) : ∀ (d : List (List α)) (cur : List α),
    scan nl (d, cur) xs = (d ++ (scan nl ([], cur) xs).1, (scan nl ([], cur) xs).2) := by
  induction xs with
  | nil => intro d cur; simp [scan]
  | cons x xs ih =>
    intro d cur
    by_cases h : x = nl
    · rw [scan_cons, scan_cons, show step nl (d, cur) x = (d ++ [cur], []) by simp [step, h],
        show step nl ([], cur) x = ([cur], []) by simp [step, h], ih (d ++ [cur]) [], ih [cur] []]
      simp
    · rw [scan_cons, scan_cons, show step nl (d, cur) x = (d, cur ++ [x]) by simp [step, h],
        show step nl ([], cur) x = ([], cur ++ [x]) by simp [step, h], ih d (cur ++ [x])]

/-- 没有换行的一段只是接在当前这一行后面。 -/
theorem scan_noNl {ys : List α} (h : nl ∉ ys) : ∀ (d : List (List α)) (cur : List α),
    scan nl (d, cur) ys = (d, cur ++ ys) := by
  induction ys with
  | nil => intro d cur; simp [scan]
  | cons y ys ih =>
    intro d cur
    have hy : ¬ y = nl := by intro e; apply h; simp [e]
    have hys : nl ∉ ys := by intro m; apply h; simp [m]
    rw [scan_cons, show step nl (d, cur) y = (d, cur ++ [y]) by simp [step, hy], ih hys d (cur ++ [y])]
    simp

/-- 不变式：当前这一行（下一块的 `carry`）里没有换行。 -/
theorem carry_noNl (xs : List α) : ∀ (d : List (List α)) (cur : List α),
    nl ∉ cur → nl ∉ (scan nl (d, cur) xs).2 := by
  induction xs with
  | nil => intro d cur h; simpa [scan] using h
  | cons x xs ih =>
    intro d cur h
    by_cases hx : x = nl
    · rw [scan_cons, show step nl (d, cur) x = (d ++ [cur], []) by simp [step, hx]]
      exact ih _ _ (by simp)
    · rw [scan_cons, show step nl (d, cur) x = (d, cur ++ [x]) by simp [step, hx]]
      have : nl ≠ x := fun e => hx e.symm
      exact ih _ _ (by simp [h, this])

/-- `carry` 里没有换行时，把它接在这一块前面从头切，等于接着上一块的状态往下切。 -/
theorem chunkStep_eq {d : List (List α)} {carry : List α} (h : nl ∉ carry) (c : List α) :
    chunkStep nl (d, carry) c = scan nl (d, carry) c := by
  have h1 : scan nl ([], []) (carry ++ c) = scan nl ([], carry) c := by
    rw [scan_append, scan_noNl nl h]
    simp
  simp only [chunkStep, h1]
  rw [scan_prefix nl c d carry]

theorem chunk_eq (cs : List (List α)) : ∀ (d : List (List α)) (carry : List α),
    nl ∉ carry → cs.foldl (chunkStep nl) (d, carry) = scan nl (d, carry) cs.flatten := by
  induction cs with
  | nil => intro d carry _; simp [scan]
  | cons c cs ih =>
    intro d carry h
    rw [List.foldl_cons, List.flatten_cons, scan_append, chunkStep_eq nl h c]
    have hn : nl ∉ (scan nl (d, carry) c).2 := carry_noNl nl c d carry h
    have e : scan nl (d, carry) c = ((scan nl (d, carry) c).1, (scan nl (d, carry) c).2) := rfl
    rw [e]
    exact ih _ _ hn

/-- 不管输入怎么切成块，逐块得到的行和整个读进来再切的行相同。 -/
theorem stream_eq (cs : List (List α)) : stream nl cs = lines nl cs.flatten := by
  unfold stream lines
  rw [chunk_eq nl cs [] [] (by simp)]

-- "1\n23\n4" 切成 "1\n2"、"3\n"、"4"（换行记作 0）：第二行跨了两块
example : stream 0 [[1, 0, 2], [3, 0], [4]] = [[1], [2, 3], [4]] := by decide
example : lines 0 [1, 0, 2, 3, 0, 4] = [[1], [2, 3], [4]] := by decide
-- 末尾有换行、空行、空的输入
example : stream 0 [[1, 0], [0]] = [[1], []] := by decide
example : stream (0 : Nat) [] = [] := by decide

/-! ### 反例：每块各自切行，不留 carry

跨块的那一行被切成了两行。 -/
example : ([[1, 0, 2], [3, 0], [4]].flatMap (lines 0)) = [[1], [2], [3], [4]] := by decide
example : ([[1, 0, 2], [3, 0], [4]].flatMap (lines 0)) ≠ lines 0 [1, 0, 2, 3, 0, 4] := by decide

end Core.M28
