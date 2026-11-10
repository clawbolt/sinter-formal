/-!
# S8：堆排序——`std.vec` 的 `sort`、`sort_by`

`std.vec.sort_by(v, less)` 是堆排序，只用 `vec_swap`（Lean M20）交换元素，不需要把元素移出 Vec。
这里把 Vec 看成下标到值的函数 `Arr`，把 `less` 看成整数的 `<`，给出和 `std/vec.sn` 一一对应的算法：

- `siftDown a m i`：在前 `m` 个元素里，从 `i` 往下调整：取较大的孩子，比 `i` 大就交换、继续往下；
- `heapify a m k`：依次对 `k-1, …, 0` 调用 `siftDown`，建成大根堆；
- `extract a m`：堆的大小是 `m` 时，把堆顶（最大的）换到 `m-1`，堆缩小一格再调整，直到堆空；
- `heapSort a n = extract (heapify a n (n / 2)) n`。

**定理**：
- `heapSort_sorted`：结果的前 `n` 个元素从小到大排好；
- `heapSort_swaps`：结果由若干次 `[0, n)` 里的交换得到（`Swaps`）——所以是原来元素的一个排列，
  不会多出、丢掉或复制元素，`n` 以后的元素不变。

不保证稳定：相等的元素排序后先后可能变。证明只用到 `≤` 是全序；`sort_by` 的 `less` 要是严格弱序
（`sort` 用 `std.math` 的 `Ord`，I64、Str 的实现已经满足，见 S1）。
-/

namespace Core.S8

abbrev Arr := Nat → Int

def swap (a : Arr) (i j : Nat) : Arr := fun k => if k = i then a j else if k = j then a i else a k

theorem swap_i (a : Arr) (i j : Nat) : swap a i j i = a j := by simp [swap]

theorem swap_j (a : Arr) (i j : Nat) : swap a i j j = a i := by
  unfold swap
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem swap_o (a : Arr) (i j k : Nat) (hi : k ≠ i) (hj : k ≠ j) : swap a i j k = a k := by
  simp [swap, hi, hj]

/-! ## 交换序列：排列 -/

/-- `b` 由 `a` 经过若干次 `[0, m)` 里的交换得到。 -/
inductive Swaps (m : Nat) : Arr → Arr → Prop
  | refl (a : Arr) : Swaps m a a
  | step (a b : Arr) (i j : Nat) : i < m → j < m → Swaps m (swap a i j) b → Swaps m a b

theorem Swaps.trans {m : Nat} {a b c : Arr} (h1 : Swaps m a b) (h2 : Swaps m b c) : Swaps m a c := by
  revert h2
  induction h1 with
  | refl => exact id
  | step a b i j hi hj _ ih => intro h2; exact Swaps.step _ _ i j hi hj (ih h2)

theorem Swaps.mono {m m' : Nat} {a b : Arr} (h : Swaps m a b) (hm : m ≤ m') : Swaps m' a b := by
  induction h with
  | refl a => exact Swaps.refl a
  | step a b i j hi hj _ ih => exact Swaps.step _ _ i j (by omega) (by omega) ih

/-- `[0, m)` 以外的元素不变。 -/
theorem Swaps.frame {m : Nat} {a b : Arr} (h : Swaps m a b) : ∀ q, m ≤ q → b q = a q := by
  induction h with
  | refl => intro q _; rfl
  | step a b i j hi hj _ ih => intro q hq; rw [ih q hq, swap_o a i j q (by omega) (by omega)]

/-- `[0, m)` 里的元素都不超过 `x`，交换之后仍然如此。 -/
theorem Swaps.bound {m : Nat} {a b : Arr} {x : Int} (h : Swaps m a b) :
    (∀ p, p < m → a p ≤ x) → ∀ p, p < m → b p ≤ x := by
  induction h with
  | refl => exact id
  | step a b i j hi hj _ ih =>
    intro ha
    apply ih
    intro p hp
    simp only [swap]
    split
    · exact ha j hj
    · split
      · exact ha i hi
      · exact ha p hp

/-! ## 下沉 -/

def siftDown (a : Arr) (m i : Nat) : Arr :=
  if h : 2 * i + 1 < m then
    if 2 * i + 2 < m ∧ a (2 * i + 1) < a (2 * i + 2) then
      if a i < a (2 * i + 2) then siftDown (swap a i (2 * i + 2)) m (2 * i + 2) else a
    else
      if a i < a (2 * i + 1) then siftDown (swap a i (2 * i + 1)) m (2 * i + 1) else a
  else a
termination_by m - i

/-- 前 `m` 个元素里，父节点下标不小于 `k` 的位置都满足堆性质（不大于父节点）。 -/
abbrev HeapFrom (a : Arr) (m k : Nat) : Prop :=
  ∀ j, 0 < j → j < m → k ≤ (j - 1) / 2 → a j ≤ a ((j - 1) / 2)

/-- 除了 `i` 和它的孩子之间，都满足堆性质；`i` 的孩子也不大于 `i` 的父节点。 -/
abbrev Near (a : Arr) (m k i : Nat) : Prop :=
  (∀ j, 0 < j → j < m → k ≤ (j - 1) / 2 → (j - 1) / 2 ≠ i → a j ≤ a ((j - 1) / 2)) ∧
  (∀ j, 0 < j → j < m → (j - 1) / 2 = i → 0 < i → k ≤ (i - 1) / 2 → a j ≤ a ((i - 1) / 2))

theorem near_stop (a : Arr) (m k i : Nat)
    (hbig : ∀ s, (s = 2 * i + 1 ∨ s = 2 * i + 2) → s < m → a s ≤ a i)
    (h : Near a m k i) : HeapFrom a m k := by
  obtain ⟨h1, _⟩ := h
  intro j hj0 hjm hkj
  by_cases hp : (j - 1) / 2 = i
  · rw [hp]; exact hbig j (by omega) hjm
  · exact h1 j hj0 hjm hkj hp

/-- `i` 和较大的孩子 `c` 交换之后，问题移到 `c`。 -/
theorem near_step (a : Arr) (m k i c : Nat) (hc : c = 2 * i + 1 ∨ c = 2 * i + 2) (hcm : c < m)
    (hk : k ≤ i) (hbig : ∀ s, (s = 2 * i + 1 ∨ s = 2 * i + 2) → s < m → a s ≤ a c)
    (hlt : a i < a c) (h : Near a m k i) : Near (swap a i c) m k c := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · intro j hj0 hjm hkj hp
    by_cases hjc : j = c
    · rw [hjc]
      have hpi : (c - 1) / 2 = i := by omega
      rw [hpi, swap_j, swap_i]
      omega
    · by_cases hji : j = i
      · rw [hji] at hkj ⊢
        have hi0 : 0 < i := by omega
        rw [swap_i, swap_o a i c ((i - 1) / 2) (by omega) (by omega)]
        exact h2 c (by omega) hcm (by omega) hi0 hkj
      · rw [swap_o a i c j hji hjc]
        by_cases hpi : (j - 1) / 2 = i
        · rw [hpi, swap_i]
          exact hbig j (by omega) hjm
        · rw [swap_o a i c ((j - 1) / 2) hpi hp]
          exact h1 j hj0 hjm hkj hpi
  · intro j hj0 hjm hp _ _
    have hpc : (c - 1) / 2 = i := by omega
    rw [hpc, swap_i, swap_o a i c j (by omega) (by omega)]
    have := h1 j hj0 hjm (by omega) (by omega)
    rw [hp] at this
    exact this

/-- **下沉之后，从 `k` 起都满足堆性质。** `n` 是步数的上界。 -/
theorem sift_heap (n : Nat) : ∀ (a : Arr) (m k i : Nat), m - i ≤ n → k ≤ i → Near a m k i →
    HeapFrom (siftDown a m i) m k := by
  induction n with
  | zero =>
    intro a m k i hn _ h
    rw [siftDown, dite_eq_right (by omega : ¬ 2 * i + 1 < m)]
    exact near_stop a m k i (fun s hs hsm => by omega) h
  | succ n ih =>
    intro a m k i hn hk h
    rw [siftDown]
    by_cases hl : 2 * i + 1 < m
    · rw [dite_eq_left hl]
      by_cases hr : 2 * i + 2 < m ∧ a (2 * i + 1) < a (2 * i + 2)
      · rw [ite_eq_left hr]
        obtain ⟨hr1, hr2⟩ := hr
        have hbig : ∀ s, (s = 2 * i + 1 ∨ s = 2 * i + 2) → s < m → a s ≤ a (2 * i + 2) := by
          intro s hs _
          rcases hs with rfl | rfl <;> omega
        by_cases hlt : a i < a (2 * i + 2)
        · rw [ite_eq_left hlt]
          exact ih _ m k _ (by omega) (by omega)
            (near_step a m k i (2 * i + 2) (Or.inr rfl) hr1 hk hbig hlt h)
        · rw [ite_eq_right hlt]
          exact near_stop a m k i (fun s hs hsm => by have := hbig s hs hsm; omega) h
      · rw [ite_eq_right hr]
        have hr' : 2 * i + 2 < m → a (2 * i + 2) ≤ a (2 * i + 1) := fun h' =>
          Int.not_lt.mp (fun hc => hr ⟨h', hc⟩)
        have hbig : ∀ s, (s = 2 * i + 1 ∨ s = 2 * i + 2) → s < m → a s ≤ a (2 * i + 1) := by
          intro s hs hsm
          rcases hs with rfl | rfl
          · omega
          · exact hr' hsm
        by_cases hlt : a i < a (2 * i + 1)
        · rw [ite_eq_left hlt]
          exact ih _ m k _ (by omega) (by omega)
            (near_step a m k i (2 * i + 1) (Or.inl rfl) hl hk hbig hlt h)
        · rw [ite_eq_right hlt]
          exact near_stop a m k i (fun s hs hsm => by have := hbig s hs hsm; omega) h
    · rw [dite_eq_right hl]
      exact near_stop a m k i (fun s hs hsm => by omega) h

theorem sift_swaps (n : Nat) : ∀ (a : Arr) (m i : Nat), m - i ≤ n → Swaps m a (siftDown a m i) := by
  induction n with
  | zero =>
    intro a m i hn
    rw [siftDown, dite_eq_right (by omega : ¬ 2 * i + 1 < m)]
    exact Swaps.refl a
  | succ n ih =>
    intro a m i hn
    rw [siftDown]
    by_cases hl : 2 * i + 1 < m
    · rw [dite_eq_left hl]
      by_cases hr : 2 * i + 2 < m ∧ a (2 * i + 1) < a (2 * i + 2)
      · rw [ite_eq_left hr]
        by_cases hlt : a i < a (2 * i + 2)
        · rw [ite_eq_left hlt]
          exact Swaps.step _ _ i (2 * i + 2) (by omega) hr.1 (ih _ m _ (by omega))
        · rw [ite_eq_right hlt]; exact Swaps.refl a
      · rw [ite_eq_right hr]
        by_cases hlt : a i < a (2 * i + 1)
        · rw [ite_eq_left hlt]
          exact Swaps.step _ _ i (2 * i + 1) (by omega) hl (ih _ m _ (by omega))
        · rw [ite_eq_right hlt]; exact Swaps.refl a
    · rw [dite_eq_right hl]; exact Swaps.refl a

/-! ## 建堆 -/

def heapify (a : Arr) (m : Nat) : Nat → Arr
  | 0 => a
  | k + 1 => heapify (siftDown a m k) m k

theorem heapify_heap (m : Nat) : ∀ (k : Nat) (a : Arr), HeapFrom a m k → HeapFrom (heapify a m k) m 0 := by
  intro k
  induction k with
  | zero => intro a h; simp only [heapify]; exact h
  | succ k ih =>
    intro a h
    simp only [heapify]
    apply ih
    apply sift_heap (m - k) a m k k (Nat.le_refl _) (Nat.le_refl _)
    refine ⟨?_, ?_⟩
    · intro j hj0 hjm hkj hp
      exact h j hj0 hjm (by omega)
    · intro j _ _ _ hk0 hkk
      omega

theorem heapify_swaps (m : Nat) : ∀ (k : Nat) (a : Arr), Swaps m a (heapify a m k) := by
  intro k
  induction k with
  | zero => intro a; simp only [heapify]; exact Swaps.refl a
  | succ k ih =>
    intro a
    simp only [heapify]
    exact (sift_swaps _ a m k (Nat.le_refl _)).trans (ih _)

/-! ## 依次取出堆顶 -/

def extract (a : Arr) : Nat → Arr
  | 0 => a
  | m + 1 => extract (siftDown (swap a 0 m) m 0) m

/-- 堆顶是前 `m` 个元素里最大的。 -/
theorem heap_root (a : Arr) (m : Nat) (h : HeapFrom a m 0) : ∀ t p, p ≤ t → p < m → a p ≤ a 0 := by
  intro t
  induction t with
  | zero =>
    intro p hp _
    have : p = 0 := by omega
    rw [this]; exact Int.le_refl _
  | succ t ih =>
    intro p hp hpm
    by_cases h0 : p = 0
    · rw [h0]; exact Int.le_refl _
    · have h1 := h p (by omega) hpm (Nat.zero_le _)
      have h2 := ih ((p - 1) / 2) (by omega) (by omega)
      omega

abbrev Sorted (a : Arr) (n : Nat) : Prop := ∀ p q, p ≤ q → q < n → a p ≤ a q

/-- 取出过程的不变式：前 `m` 个是堆；`[m, n)` 已排好；前面的都不大于后面的。 -/
abbrev Inv (a : Arr) (m n : Nat) : Prop :=
  HeapFrom a m 0 ∧ (∀ p q, m ≤ p → p ≤ q → q < n → a p ≤ a q) ∧
  (∀ p q, p < m → m ≤ q → q < n → a p ≤ a q)

theorem extract_sorted (n : Nat) : ∀ (m : Nat) (a : Arr), m ≤ n → Inv a m n → Sorted (extract a m) n := by
  intro m
  induction m with
  | zero =>
    intro a _ h
    simp only [extract]
    intro p q hpq hq
    exact h.2.1 p q (Nat.zero_le _) hpq hq
  | succ m ih =>
    intro a hmn h
    obtain ⟨hh, hs, hb⟩ := h
    simp only [extract]
    refine ih _ (by omega) ?_
    have hroot : ∀ p, p < m + 1 → a p ≤ a 0 := fun p hp => heap_root a (m + 1) hh p p (Nat.le_refl _) hp
    have hsw := sift_swaps (m - 0) (swap a 0 m) m 0 (Nat.le_refl _)
    have hfr := hsw.frame
    have hbm : swap a 0 m m = a 0 := swap_j a 0 m
    have hbq : ∀ q, m < q → swap a 0 m q = a q := fun q hq => swap_o a 0 m q (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · apply sift_heap (m - 0) _ m 0 0 (Nat.le_refl _) (Nat.le_refl _)
      refine ⟨?_, ?_⟩
      · intro j hj0 hjm _ hp
        rw [swap_o a 0 m j (by omega) (by omega), swap_o a 0 m ((j - 1) / 2) hp (by omega)]
        exact hh j hj0 (by omega) (Nat.zero_le _)
      · intro j _ _ _ h0 _
        omega
    · intro p q hmp hpq hq
      rw [hfr p hmp, hfr q (by omega)]
      by_cases hp : p = m
      · by_cases hqm : q = m
        · rw [hp, hqm]; exact Int.le_refl _
        · rw [hp, hbm, hbq q (by omega)]
          exact hb 0 q (by omega) (by omega) hq
      · rw [hbq p (by omega), hbq q (by omega)]
        exact hs p q (by omega) hpq hq
    · intro p q hp hmq hq
      rw [hfr q hmq]
      refine hsw.bound ?_ p hp
      intro r hr
      have hr' : swap a 0 m r ≤ a 0 ∧ ∀ q', m < q' → q' < n → swap a 0 m r ≤ a q' := by
        by_cases hr0 : r = 0
        · rw [hr0, swap_i]
          exact ⟨hroot m (by omega), fun q' h1 h2 => hb m q' (by omega) (by omega) h2⟩
        · rw [swap_o a 0 m r hr0 (by omega)]
          exact ⟨hroot r (by omega), fun q' h1 h2 => hb r q' (by omega) (by omega) h2⟩
      by_cases hqm : q = m
      · rw [hqm, hbm]; exact hr'.1
      · rw [hbq q (by omega)]; exact hr'.2 q (by omega) hq

theorem extract_swaps (n : Nat) : ∀ (m : Nat) (a : Arr), m ≤ n → Swaps n a (extract a m) := by
  intro m
  induction m with
  | zero => intro a _; simp only [extract]; exact Swaps.refl a
  | succ m ih =>
    intro a hmn
    simp only [extract]
    exact Swaps.step _ _ 0 m (by omega) (by omega)
      (((sift_swaps (m - 0) _ m 0 (Nat.le_refl _)).mono (by omega)).trans (ih _ (by omega)))

/-! ## 堆排序 -/

def heapSort (a : Arr) (n : Nat) : Arr := extract (heapify a n (n / 2)) n

/-- **排好序。** -/
theorem heapSort_sorted (a : Arr) (n : Nat) : Sorted (heapSort a n) n := by
  unfold heapSort
  apply extract_sorted n n _ (Nat.le_refl _)
  refine ⟨?_, ?_, ?_⟩
  · apply heapify_heap
    intro j hj0 hjm hk
    omega
  · intro p q h1 h2 h3; omega
  · intro p q h1 h2 h3; omega

/-- **是原来元素的一个排列**（若干次 `[0, n)` 里的交换）。 -/
theorem heapSort_swaps (a : Arr) (n : Nat) : Swaps n a (heapSort a n) := by
  unfold heapSort
  exact (heapify_swaps n (n / 2) a).trans (extract_swaps n n _ (Nat.le_refl _))

/-! ## 例子 -/

def ofList (l : List Int) : Arr := fun i => l.getD i 0
def toList (a : Arr) (n : Nat) : List Int := (List.range n).map a

#eval toList (heapSort (ofList [5, 3, 8, 1, 9, 2, 7, 2]) 8) 8
#eval toList (heapSort (ofList [3, 2, 1, 0, -1]) 5) 5

end Core.S8
