/-!
# 标准库 `std.str`、`std.vec` 的规格和定律

字符串按字节处理，模型是 `List Nat`；`Vec` 的模型是 `List`。下面每个参考实现都照着 `std/*.sn` 的循环写，
再证明它满足的性质。

- `starts_with(s, p)`：`s` 的前 `len(p)` 个字节等于 `p`，恰好是 `s = p ++ t`（`startsWith_iff`）。
- `find(s, p)`：返回的位置上确实以 `p` 开头，并且前面没有（`findL_some`）；`.None` 时任何位置都不以 `p` 开头（`findL_none`）。
  空的 `p` 出现在 0。
- `trim(s)`：`s = a ++ trim(s) ++ b`，`a`、`b` 全是空白，结果的头尾都不是空白（`trim_spec`）。
- `split`、`join`：`join(split(s, sep), sep) == s`，对任何 `sep`（包括空串）都成立（`join_split`）。
- `vec.reverse`：把元素依次 pop 进新的 Vec，结果就是反转（`revLoop_eq`）。
-/

namespace Core.Library.StrVec

/-! ## starts_with -/

def StartsWith (s p : List Nat) : Prop := s.take p.length = p

instance (s p : List Nat) : Decidable (StartsWith s p) :=
  inferInstanceAs (Decidable (s.take p.length = p))

theorem startsWith_iff (s p : List Nat) : StartsWith s p ↔ ∃ t, s = p ++ t := by
  constructor
  · intro h
    refine ⟨s.drop p.length, ?_⟩
    calc s = s.take p.length ++ s.drop p.length := by simp
      _ = p ++ s.drop p.length := by rw [show s.take p.length = p from h]
  · rintro ⟨t, rfl⟩
    simp [StartsWith]

/-! ## find -/

/-- `find(s, p)`：从 0 开始逐个位置试。 -/
def findL (p : List Nat) : List Nat → Option Nat
  | [] => if p = [] then some 0 else none
  | x :: xs => if StartsWith (x :: xs) p then some 0 else (findL p xs).map (· + 1)

theorem findL_some (p : List Nat) : ∀ (s : List Nat) (i : Nat),
    findL p s = some i → StartsWith (s.drop i) p ∧ ∀ j < i, ¬ StartsWith (s.drop j) p
  | [], i, h => by
    by_cases hp : p = []
    · subst hp
      simp [findL] at h
      subst h
      refine ⟨?_, by intro j hj; omega⟩
      simp [StartsWith]
    · simp [findL, hp] at h
  | x :: xs, i, h => by
    by_cases hs : StartsWith (x :: xs) p
    · simp [findL, hs] at h
      subst h
      exact ⟨by simpa using hs, by intro j hj; omega⟩
    · simp [findL, hs] at h
      obtain ⟨k, hk, rfl⟩ := h
      have ih := findL_some p xs k hk
      refine ⟨by simpa using ih.1, ?_⟩
      intro j hj
      cases j with
      | zero => simpa using hs
      | succ j => simpa using ih.2 j (by omega)

theorem findL_none (p : List Nat) : ∀ (s : List Nat),
    findL p s = none → ∀ j, ¬ StartsWith (s.drop j) p
  | [], h, j => by
    by_cases hp : p = []
    · subst hp
      simp [findL] at h
    · intro e
      simp [StartsWith] at e
      simp_all
  | x :: xs, h, j => by
    by_cases hs : StartsWith (x :: xs) p
    · simp [findL, hs] at h
    · simp [findL, hs] at h
      have ih := findL_none p xs h
      cases j with
      | zero => simpa using hs
      | succ j => simpa using ih j

/-! ## trim -/

/-- 空格、制表符、换行、回车。 -/
def isSp (b : Nat) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-- 去掉开头的空白（trim 的第一个循环）。 -/
def dropSp : List Nat → List Nat
  | [] => []
  | x :: xs => if isSp x then dropSp xs else x :: xs

/-- `trim(s)`：先去掉开头的空白，再从结尾往回去掉空白。 -/
def trimL (s : List Nat) : List Nat := (dropSp (dropSp s).reverse).reverse

theorem dropSp_spec : ∀ (s : List Nat), ∃ a, s = a ++ dropSp s ∧ (∀ x ∈ a, isSp x = true) ∧
    ∀ y ys, dropSp s = y :: ys → isSp y = false
  | [] => ⟨[], by simp [dropSp]⟩
  | x :: xs => by
    by_cases h : isSp x = true
    · obtain ⟨a, h1, h2, h3⟩ := dropSp_spec xs
      refine ⟨x :: a, ?_, ?_, ?_⟩
      · simp [dropSp, h]
        exact h1
      · intro z hz
        simp at hz
        rcases hz with rfl | hz
        · exact h
        · exact h2 z hz
      · simpa [dropSp, h] using h3
    · refine ⟨[], ?_, ?_, ?_⟩
      · simp [dropSp, h]
      · simp
      · intro y ys e
        simp [dropSp, h] at e
        rw [← e.1]
        simpa using h

theorem trim_spec (s : List Nat) : ∃ a b, s = a ++ trimL s ++ b ∧
    (∀ x ∈ a, isSp x = true) ∧ (∀ x ∈ b, isSp x = true) ∧
    (∀ y ys, trimL s = y :: ys → isSp y = false) ∧ (∀ ys y, trimL s = ys ++ [y] → isSp y = false) := by
  obtain ⟨a, ha, ha2, ha3⟩ := dropSp_spec s
  obtain ⟨c, hc, hc2, hc3⟩ := dropSp_spec (dropSp s).reverse
  have hu : dropSp s = trimL s ++ c.reverse := by
    unfold trimL
    rw [← List.reverse_append, ← hc, List.reverse_reverse]
  refine ⟨a, c.reverse, ?_, ha2, ?_, ?_, ?_⟩
  · rw [List.append_assoc, ← hu]
    exact ha
  · intro x hx
    exact hc2 x (List.mem_reverse.mp hx)
  · intro y ys e
    apply ha3 y (ys ++ c.reverse)
    simp [hu, e]
  · intro ys y e
    apply hc3 y ys.reverse
    have := congrArg List.reverse e
    simpa [trimL] using this

/-! ## split、join -/

/-- `split` 的循环。`cur` 是当前这一段已经读到的字节。
    `fuel` 只是为了让递归在结构上终止；`splitL` 给的足够多，用完时把剩下的整段放进去，所以 `join_go` 对任何 fuel 都成立。 -/
def splitGo (sep : List Nat) : Nat → List Nat → List Nat → List (List Nat)
  | 0, s, cur => [cur ++ s]
  | _ + 1, [], cur => [cur]
  | n + 1, x :: xs, cur =>
    if StartsWith (x :: xs) sep then cur :: splitGo sep n ((x :: xs).drop sep.length) []
    else splitGo sep n xs (cur ++ [x])

/-- `split(s, sep)`：`sep` 是空串时不切。 -/
def splitL (sep s : List Nat) : List (List Nat) :=
  if sep = [] then [s] else splitGo sep (s.length + 1) s []

/-- `join(parts, sep)`：第一段前面不加 `sep`。 -/
def joinL (sep : List Nat) : List (List Nat) → List Nat
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ sep ++ joinL sep (q :: ps)

theorem splitGo_ne (sep : List Nat) : ∀ n s cur, splitGo sep n s cur ≠ []
  | 0, s, cur => by simp [splitGo]
  | _ + 1, [], cur => by simp [splitGo]
  | n + 1, x :: xs, cur => by
    by_cases h : StartsWith (x :: xs) sep
    · simp [splitGo, h]
    · simp only [splitGo, h, ite_false]
      exact splitGo_ne sep n xs (cur ++ [x])

theorem joinL_cons (sep p : List Nat) (ps : List (List Nat)) (h : ps ≠ []) :
    joinL sep (p :: ps) = p ++ sep ++ joinL sep ps := by
  cases ps with
  | nil => contradiction
  | cons q qs => rfl

theorem join_go (sep : List Nat) : ∀ n s cur, joinL sep (splitGo sep n s cur) = cur ++ s
  | 0, s, cur => by simp [splitGo, joinL]
  | _ + 1, [], cur => by simp [splitGo, joinL]
  | n + 1, x :: xs, cur => by
    by_cases h : StartsWith (x :: xs) sep
    · simp only [splitGo, h, ite_true]
      rw [joinL_cons _ _ _ (splitGo_ne sep n _ []), join_go sep n, List.nil_append]
      have e : sep ++ (x :: xs).drop sep.length = x :: xs := by
        have h' : (x :: xs).take sep.length = sep := h
        calc sep ++ (x :: xs).drop sep.length
            = (x :: xs).take sep.length ++ (x :: xs).drop sep.length := by rw [h']
          _ = x :: xs := by simp
      rw [List.append_assoc, e]
    · simp only [splitGo, h, ite_false]
      rw [join_go sep n]
      simp

/-- **结论**：`join(split(s, sep), sep) == s`。 -/
theorem join_split (sep s : List Nat) : joinL sep (splitL sep s) = s := by
  unfold splitL
  by_cases h : sep = []
  · simp [h, joinL]
  · simp [h, join_go]

/-! ## vec.reverse -/

/-- `reverse` 的循环：`r` 是还没 pop 的元素（从栈顶开始，也就是 Vec 反过来），每次 pop 一个 push 到 `out` 的末尾。 -/
def revLoop {α : Type} : List α → List α → List α
  | [], out => out
  | x :: r, out => revLoop r (out ++ [x])

theorem revLoop_app {α : Type} : ∀ (r out : List α), revLoop r out = out ++ r
  | [], out => by simp [revLoop]
  | x :: r, out => by simp [revLoop, revLoop_app r]

/-- **结论**：对 Vec `v` 跑完循环，得到 `v` 反过来。 -/
theorem revLoop_eq {α : Type} (v : List α) : revLoop v.reverse [] = v.reverse := by
  simp [revLoop_app]

end Core.Library.StrVec
