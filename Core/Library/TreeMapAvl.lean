import Core.Library.TreeMap

/-!
# `std.treemap` 的 AVL 平衡

`Library.TreeMap` 只证明了树上的查找、插入、删除是对的。这里证明它们也保持 **AVL 平衡**，所以树高是对数的。

**平衡**（`Bal`）：每个节点存的高度等于两个子树高度的较大者加 1，两个子树的高度差不超过 1。

**定理**：
- `bal_ok`：两个平衡的子树高度差不超过 2 时，再平衡 `T.bal` 的结果平衡，高度是较高的子树加 0 或 1
  （没有旋转时正好加 1）；
- `insT_bal`：插入保持平衡，高度不变或加 1；
- `popT_bal`、`join_bal`、`delT_bal`：取出最小键、合并、删除保持平衡，删除后高度不变或减 1；
- `height_log`：平衡的树满足 `2 ^ (高度 / 2) ≤ 节点数 + 1`，即高度不超过 `2·log₂(n + 1) + 1`。
  查找、插入、删除都只走一条从根到叶的路径，所以都是对数时间。
-/

namespace Core.Library.TreeMap

variable {α β : Type}

def Bal : T α β → Prop
  | .leaf => True
  | .node l _ _ h r =>
    Bal l ∧ Bal r ∧ h = max l.height r.height + 1 ∧ l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1

def size : T α β → Nat
  | .leaf => 0
  | .node l _ _ _ r => size l + 1 + size r

theorem bal_leaf : Bal (.leaf : T α β) := trivial

/- 高度的展开式。`T.height` 不是递归定义，`simp only [T.height]` 会把它展开成 `match`，所以用这几条。 -/
theorem height_node {l r : T α β} {k : α} {v : β} {h : Nat} : (T.node l k v h r).height = h := rfl
theorem leftH_node {l r : T α β} {k : α} {v : β} {h : Nat} : (T.node l k v h r).leftH = l.height := rfl
theorem rightH_node {l r : T α β} {k : α} {v : β} {h : Nat} : (T.node l k v h r).rightH = r.height := rfl
theorem height_mk {l r : T α β} {k : α} {v : β} : (T.mk l k v r).height = max l.height r.height + 1 := rfl

/-- 高度的算术：展开节点和 `mk` 的高度，交给 omega。 -/
macro "hgt" : tactic =>
  `(tactic| first
    | omega
    | (simp only [height_mk, height_node, leftH_node, rightH_node] at * <;> omega))

theorem bal_mk {l r : T α β} {k : α} {v : β} (a : Bal l) (b : Bal r)
    (c : l.height ≤ r.height + 1) (d : r.height ≤ l.height + 1) : Bal (T.mk l k v r) := by
  simp only [T.mk, Bal]
  exact ⟨a, b, trivial, c, d⟩

/-! ## 再平衡 -/

theorem bal_ok {l r : T α β} (k : α) (v : β) (hl : Bal l) (hr : Bal r)
    (h1 : l.height ≤ r.height + 2) (h2 : r.height ≤ l.height + 2) :
    Bal (T.bal l k v r) ∧ max l.height r.height ≤ (T.bal l k v r).height ∧
    (T.bal l k v r).height ≤ max l.height r.height + 1 ∧
    ((T.bal l k v r).height = max l.height r.height + 1 ∨ l.height = r.height + 2 ∨ r.height = l.height + 2) := by
  unfold T.bal
  by_cases c1 : l.height > r.height + 1
  · simp only [c1, ↓reduceIte]
    rcases l with _ | ⟨ll, lk, lv, lh, lr⟩
    · exact absurd c1 (Nat.not_lt_zero _)
    simp only [Bal] at hl
    obtain ⟨b1, b2, e, d1, d2⟩ := hl
    by_cases c2 : (T.node ll lk lv lh lr).leftH ≥ (T.node ll lk lv lh lr).rightH
    · simp only [c2, ↓reduceIte]
      rw [show T.rotR (T.mk (T.node ll lk lv lh lr) k v r) = T.mk ll lk lv (T.mk lr k v r) from rfl]
      refine ⟨bal_mk b1 (bal_mk b2 hr ?_ ?_) ?_ ?_, ?_, ?_, ?_⟩ <;> hgt
    · simp only [c2, ↓reduceIte]
      rcases lr with _ | ⟨lrl, lrk, lrv, lrh, lrr⟩
      · exact absurd (Nat.zero_le _) c2
      simp only [Bal] at b2
      obtain ⟨c3, c4, e2, f1, f2⟩ := b2
      rw [show T.rotR (T.mk (T.rotL (T.node ll lk lv lh (T.node lrl lrk lrv lrh lrr))) k v r) =
        T.mk (T.mk ll lk lv lrl) lrk lrv (T.mk lrr k v r) from rfl]
      refine ⟨bal_mk (bal_mk b1 c3 ?_ ?_) (bal_mk c4 hr ?_ ?_) ?_ ?_, ?_, ?_, ?_⟩ <;> hgt
  · simp only [c1, ↓reduceIte]
    by_cases c3 : r.height > l.height + 1
    · simp only [c3, ↓reduceIte]
      rcases r with _ | ⟨rl, rk, rv, rh, rr⟩
      · exact absurd c3 (Nat.not_lt_zero _)
      simp only [Bal] at hr
      obtain ⟨b1, b2, e, d1, d2⟩ := hr
      by_cases c4 : (T.node rl rk rv rh rr).rightH ≥ (T.node rl rk rv rh rr).leftH
      · simp only [c4, ↓reduceIte]
        rw [show T.rotL (T.mk l k v (T.node rl rk rv rh rr)) = T.mk (T.mk l k v rl) rk rv rr from rfl]
        refine ⟨bal_mk (bal_mk hl b1 ?_ ?_) b2 ?_ ?_, ?_, ?_, ?_⟩ <;> hgt
      · simp only [c4, ↓reduceIte]
        rcases rl with _ | ⟨rll, rlk, rlv, rlh, rlr⟩
        · exact absurd (Nat.zero_le _) c4
        simp only [Bal] at b1
        obtain ⟨c5, c6, e2, f1, f2⟩ := b1
        rw [show T.rotL (T.mk l k v (T.rotR (T.node (T.node rll rlk rlv rlh rlr) rk rv rh rr))) =
          T.mk (T.mk l k v rll) rlk rlv (T.mk rlr rk rv rr) from rfl]
        refine ⟨bal_mk (bal_mk hl c5 ?_ ?_) (bal_mk c6 b2 ?_ ?_) ?_ ?_, ?_, ?_, ?_⟩ <;> hgt
    · simp only [c3, ↓reduceIte]
      refine ⟨bal_mk hl hr ?_ ?_, ?_, ?_, Or.inl rfl⟩ <;> hgt

/-! ## 插入 -/

theorem insT_bal (cmp : α → α → Int) (k : α) (v : β) : ∀ t : T α β, Bal t →
    Bal (insT cmp k v t) ∧ t.height ≤ (insT cmp k v t).height ∧ (insT cmp k v t).height ≤ t.height + 1
  | .leaf, _ => by simp [insT, Bal, T.height]
  | .node l k' v' h r, hb => by
    simp only [Bal] at hb
    obtain ⟨bl, br, e, d1, d2⟩ := hb
    simp only [insT]
    split
    · obtain ⟨b, x1, x2⟩ := insT_bal cmp k v l bl
      obtain ⟨y1, y2, y3, y4⟩ := bal_ok k' v' b br (by omega) (by omega)
      refine ⟨y1, ?_, ?_⟩ <;> simp only [height_node] <;> omega
    · split
      · refine ⟨?_, Nat.le_refl _, Nat.le_succ _⟩
        simp only [Bal]
        exact ⟨bl, br, e, d1, d2⟩
      · obtain ⟨b, x1, x2⟩ := insT_bal cmp k v r br
        obtain ⟨y1, y2, y3, y4⟩ := bal_ok k' v' bl b (by omega) (by omega)
        refine ⟨y1, ?_, ?_⟩ <;> simp only [height_node] <;> omega

/-! ## 删除 -/

theorem popT_bal : ∀ (l : T α β) (k : α) (v : β) (r : T α β), Bal l → Bal r →
    l.height ≤ r.height + 1 → r.height ≤ l.height + 1 →
    Bal (popT l k v r) ∧ max l.height r.height ≤ (popT l k v r).height ∧
    (popT l k v r).height ≤ max l.height r.height + 1
  | .leaf, _, _, r, _, br, _, d => by
    simp only [popT, T.height] at *
    exact ⟨br, by omega, by omega⟩
  | .node ll lk lv lh lr, k, v, r, bl, br, d1, d2 => by
    simp only [Bal] at bl
    obtain ⟨b1, b2, e, f1, f2⟩ := bl
    obtain ⟨p, x1, x2⟩ := popT_bal ll lk lv lr b1 b2 f1 f2
    simp only [popT]
    simp only [height_node] at d1 d2 ⊢
    obtain ⟨y1, y2, y3, y4⟩ := bal_ok k v p br (by omega) (by omega)
    exact ⟨y1, by omega, by omega⟩

theorem join_bal : ∀ (l r : T α β), Bal l → Bal r → l.height ≤ r.height + 1 → r.height ≤ l.height + 1 →
    Bal (join l r) ∧ max l.height r.height ≤ (join l r).height ∧ (join l r).height ≤ max l.height r.height + 1
  | l, .leaf, bl, _, d, _ => by
    simp only [join, T.height] at *
    exact ⟨bl, by omega, by omega⟩
  | l, .node rl rk rv rh rr, bl, br, d1, d2 => by
    simp only [Bal] at br
    obtain ⟨b1, b2, e, f1, f2⟩ := br
    obtain ⟨p, x1, x2⟩ := popT_bal rl rk rv rr b1 b2 f1 f2
    simp only [join]
    simp only [height_node] at d1 d2 ⊢
    obtain ⟨y1, y2, y3, y4⟩ := bal_ok (popK rl rk rv).1 (popK rl rk rv).2 bl p (by omega) (by omega)
    exact ⟨y1, by omega, by omega⟩

theorem delT_bal (cmp : α → α → Int) (k : α) : ∀ t : T α β, Bal t →
    Bal (delT cmp k t) ∧ t.height ≤ (delT cmp k t).height + 1 ∧ (delT cmp k t).height ≤ t.height
  | .leaf, _ => by simp [delT, Bal, T.height]
  | .node l k' v' h r, hb => by
    simp only [Bal] at hb
    obtain ⟨bl, br, e, d1, d2⟩ := hb
    simp only [delT]
    split
    · obtain ⟨b, x1, x2⟩ := delT_bal cmp k l bl
      obtain ⟨y1, y2, y3, y4⟩ := bal_ok k' v' b br (by omega) (by omega)
      refine ⟨y1, ?_, ?_⟩ <;> simp only [height_node] <;> omega
    · split
      · obtain ⟨y1, y2, y3⟩ := join_bal l r bl br d1 d2
        refine ⟨y1, ?_, ?_⟩ <;> simp only [height_node] <;> omega
      · obtain ⟨b, x1, x2⟩ := delT_bal cmp k r br
        obtain ⟨y1, y2, y3, y4⟩ := bal_ok k' v' bl b (by omega) (by omega)
        refine ⟨y1, ?_, ?_⟩ <;> simp only [height_node] <;> omega

/-! ## 树高是对数 -/

theorem height_log : ∀ t : T α β, Bal t → 2 ^ (t.height / 2) ≤ size t + 1
  | .leaf, _ => by simp [T.height, size]
  | .node l k v h r, hb => by
    simp only [Bal] at hb
    obtain ⟨bl, br, e, d1, d2⟩ := hb
    have il := height_log l bl
    have ir := height_log r br
    simp only [T.height, size]
    have a : (h - 2) / 2 ≤ l.height / 2 := Nat.div_le_div_right (by omega)
    have b : (h - 2) / 2 ≤ r.height / 2 := Nat.div_le_div_right (by omega)
    have pl := Nat.pow_le_pow_right (show 2 > 0 by omega) a
    have pr := Nat.pow_le_pow_right (show 2 > 0 by omega) b
    by_cases hh : h ≥ 2
    · have q : h / 2 = (h - 2) / 2 + 1 := by omega
      rw [q, Nat.pow_succ]
      omega
    · have q : h / 2 = 0 := by omega
      rw [q, Nat.pow_zero]
      omega

/-- 例子：`Library.TreeMap` 里依次插入 1…7 得到的树是平衡的（从空树开始插入多少次都一样）。 -/
theorem ex_bal : Bal ex := by
  unfold ex
  suffices ∀ (xs : List Nat) (t : T Int Nat), Bal t →
      Bal (xs.foldl (fun t i => insT Core.Library.Math.cmpI (Int.ofNat (i + 1)) i t) t) from this _ _ bal_leaf
  intro xs
  induction xs with
  | nil => intro t h; exact h
  | cons x xs ih => intro t h; exact ih _ (insT_bal _ _ _ _ h).1

end Core.Library.TreeMap
