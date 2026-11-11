import Core.Library.Math

/-!
# `std.map` 的二分查找

`std.map` 里的 `lower(m, k)`：第一个不小于 `k` 的键的下标（没有时是键的个数）。`index_of`、`insert`、`remove`
都靠它找位置。原来是从头往后找（`lin`），现在改成二分查找（`bs`），查找从线性时间变成对数时间。

**模型**：键是 `a 0, a 1, …, a (n-1)`，严格递增（`Sorted`，比较用满足 `Library.Math` 定律的 `cmp`）。
`IsLower i`：`i` 之前的键都小于 `k`，从 `i` 开始的键都不小于 `k`。

**定理**：
- `bs_lower`：二分查找的结果满足 `IsLower`（循环不变式：`lo` 之前的都小于 `k`，`hi` 开始的都不小于 `k`；
  每一轮 `hi - lo` 变小，所以 `n + 1` 轮之内结束）；
- `lin_lower`：原来的线性查找也满足 `IsLower`；
- `lower_unique`：满足 `IsLower` 的下标只有一个；
- `bs_eq_lin`：所以二分查找和原来的线性查找结果相同——`std.map` 的行为不变，`Library.Map` 的定律照样成立。

中点写成 `lo + (hi - lo) / 2`，和 `std/map.sn` 一样（不会溢出）。
-/

namespace Core.Library.MapSearch
open Core.Library.Math (OrdLaws)

variable {α : Type} (cmp : α → α → Int) (a : Nat → α) (n : Nat) (k : α)

/-- 键严格递增。 -/
def Sorted : Prop := ∀ i j, i < j → j < n → cmp (a i) (a j) = -1

/-- `i` 之前的键都小于 `k`，从 `i` 开始的键都不小于 `k`。 -/
def IsLower (i : Nat) : Prop :=
  i ≤ n ∧ (∀ j, j < i → cmp (a j) k = -1) ∧ (∀ j, i ≤ j → j < n → cmp (a j) k ≠ -1)

/-- 二分查找：在 `[lo, hi)` 里找，`f` 是最多的轮数。 -/
def bs : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      if cmp (a (lo + (hi - lo) / 2)) k = -1 then bs f (lo + (hi - lo) / 2 + 1) hi
      else bs f lo (lo + (hi - lo) / 2)
    else lo

/-- 原来的线性查找：从 `i` 往后，遇到不小于 `k` 的键或到头为止。 -/
def lin : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => if i < n ∧ cmp (a i) k = -1 then lin f (i + 1) else i

variable {cmp a n k}

theorem bs_ok (L : OrdLaws cmp) (hs : Sorted cmp a n) :
    ∀ f lo hi, hi - lo ≤ f → lo ≤ hi → hi ≤ n →
      (∀ j, j < lo → cmp (a j) k = -1) → (∀ j, hi ≤ j → j < n → cmp (a j) k ≠ -1) →
      IsLower cmp a n k (bs cmp a k f lo hi)
  | 0, lo, hi, hf, h1, h2, hl, hh => by
    simp only [bs]
    have e : hi = lo := by omega
    subst e
    exact ⟨h2, hl, hh⟩
  | f + 1, lo, hi, hf, h1, h2, hl, hh => by
    simp only [bs]
    by_cases hlt : lo < hi
    · rw [ite_eq_left hlt]
      by_cases hc : cmp (a (lo + (hi - lo) / 2)) k = -1
      · rw [ite_eq_left hc]
        refine bs_ok L hs f _ hi (by omega) (by omega) h2 ?_ hh
        intro j hj
        by_cases hjm : j = lo + (hi - lo) / 2
        · rw [hjm]; exact hc
        · exact L.trans _ _ _ (hs j _ (by omega) (by omega)) hc
      · rw [ite_eq_right hc]
        refine bs_ok L hs f lo _ (by omega) (by omega) (by omega) hl ?_
        intro j hj hjn hcj
        by_cases hjm : j = lo + (hi - lo) / 2
        · rw [hjm] at hcj; exact hc hcj
        · exact hc (L.trans _ _ _ (hs _ j (by omega) hjn) hcj)
    · rw [ite_eq_right hlt]
      have e : hi = lo := by omega
      subst e
      exact ⟨h2, hl, hh⟩

/-- 从 `[0, n)` 开始、最多 `n + 1` 轮的二分查找满足 `IsLower`。 -/
theorem bs_lower (L : OrdLaws cmp) (hs : Sorted cmp a n) : IsLower cmp a n k (bs cmp a k (n + 1) 0 n) :=
  bs_ok L hs (n + 1) 0 n (by omega) (by omega) (Nat.le_refl n)
    (fun j h => absurd h (Nat.not_lt_zero j)) (fun j h1 h2 => absurd h2 (by omega))

theorem lin_ok (L : OrdLaws cmp) (hs : Sorted cmp a n) :
    ∀ f i, n - i ≤ f → i ≤ n → (∀ j, j < i → cmp (a j) k = -1) → IsLower cmp a n k (lin cmp a n k f i)
  | 0, i, hf, hi, hl => by
    simp only [lin]
    have e : i = n := by omega
    subst e
    exact ⟨Nat.le_refl _, hl, fun j h1 h2 => absurd h2 (by omega)⟩
  | f + 1, i, hf, hi, hl => by
    simp only [lin]
    by_cases hc : i < n ∧ cmp (a i) k = -1
    · rw [ite_eq_left hc]
      refine lin_ok L hs f (i + 1) (by omega) (by omega) ?_
      intro j hj
      by_cases hji : j = i
      · rw [hji]; exact hc.2
      · exact hl j (by omega)
    · rw [ite_eq_right hc]
      refine ⟨hi, hl, fun j hj hjn hcj => ?_⟩
      by_cases hji : j = i
      · subst hji; exact hc ⟨hjn, hcj⟩
      · exact hc ⟨by omega, L.trans _ _ _ (hs i j (by omega) hjn) hcj⟩

theorem lin_lower (L : OrdLaws cmp) (hs : Sorted cmp a n) : IsLower cmp a n k (lin cmp a n k (n + 1) 0) :=
  lin_ok L hs (n + 1) 0 (by omega) (by omega) (fun j h => absurd h (Nat.not_lt_zero j))

/-- 满足 `IsLower` 的下标只有一个。 -/
theorem lower_unique {i i' : Nat} (h : IsLower cmp a n k i) (h' : IsLower cmp a n k i') : i = i' := by
  obtain ⟨hn, hl, hh⟩ := h
  obtain ⟨hn', hl', hh'⟩ := h'
  rcases Nat.lt_trichotomy i i' with c | c | c
  · exact absurd (hl' i c) (hh i (Nat.le_refl i) (by omega))
  · exact c
  · exact absurd (hl i' c) (hh' i' (Nat.le_refl i') (by omega))

/-- **结论**：二分查找和原来的线性查找结果相同。 -/
theorem bs_eq_lin (L : OrdLaws cmp) (hs : Sorted cmp a n) :
    bs cmp a k (n + 1) 0 n = lin cmp a n k (n + 1) 0 :=
  lower_unique (bs_lower L hs) (lin_lower L hs)

/-! ## 例子：键 1, 3, 5, 7 -/

def keys : Nat → Int := fun i => ([1, 3, 5, 7] : List Int).getD i 0

#eval (List.range 9).map (fun (k : Nat) => (bs Core.Library.Math.cmpI keys (Int.ofNat k) 5 0 4, lin Core.Library.Math.cmpI keys 4 (Int.ofNat k) 5 0))

end Core.Library.MapSearch
