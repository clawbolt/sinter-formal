import Core.Library.Map

/-!
# 平衡树的映射（`std.treemap`）

`std.map` 的插入、删除要挪动元素（线性时间）。`std.treemap` 改用平衡二叉树（AVL）：查找、插入、删除都只走一条从根到叶的路径。

**模型**：树 `T`，每个节点有键、值、高度和左右子树。树的**中序遍历**（`toList`：左子树、节点、右子树）
就是 S4 里的有序键值对列表。

**定理**：
- `toList_rotR`、`toList_rotL`、`toList_bal`：旋转和再平衡不改变中序遍历；
- `lookupT_eq`、`insT_eq`、`delT_eq`：中序遍历有序时，树上的查找、插入、删除分别等于 `Library.Map` 的 `lookup`、`ins`、`del`
  （删除有两个子树的节点时，用右子树的最小键顶替：`toList_popMin`、`toList_join`）；
- 所以 `Library.Map` 的定律对树照样成立（`insT_sorted`、`delT_sorted`、`lookupT_ins`、`lookupT_del`）。

这里只证明正确性；AVL 的平衡（两边子树高度差不超过 1，所以树高是 O(log n)）在 `Library.TreeMapAvl` 里证明。
-/

namespace Core.Library.TreeMap
open Core.Library.Math (OrdLaws)
open Core.Library.Map (Sorted lookup ins del)

variable {α β : Type}

inductive T (α β : Type) where
  | leaf : T α β
  | node : T α β → α → β → Nat → T α β → T α β

namespace T

/-- 中序遍历。 -/
def toList : T α β → List (α × β)
  | leaf => []
  | node l k v _ r => toList l ++ (k, v) :: toList r

def height : T α β → Nat
  | leaf => 0
  | node _ _ _ h _ => h

def leftH : T α β → Nat
  | leaf => 0
  | node l _ _ _ _ => l.height

def rightH : T α β → Nat
  | leaf => 0
  | node _ _ _ _ r => r.height

/-- 造一个节点，高度按两个子树算。 -/
def mk (l : T α β) (k : α) (v : β) (r : T α β) : T α β := node l k v (max l.height r.height + 1) r

def rotR : T α β → T α β
  | node (node a xk xv _ b) yk yv _ c => mk a xk xv (mk b yk yv c)
  | t => t

def rotL : T α β → T α β
  | node a xk xv _ (node b yk yv _ c) => mk (mk a xk xv b) yk yv c
  | t => t

/-- 再平衡：左边高出 1 以上时右旋（左子树偏右时先把它左旋），右边同理。 -/
def bal (l : T α β) (k : α) (v : β) (r : T α β) : T α β :=
  if l.height > r.height + 1 then
    if l.leftH ≥ l.rightH then rotR (mk l k v r) else rotR (mk (rotL l) k v r)
  else if r.height > l.height + 1 then
    if r.rightH ≥ r.leftH then rotL (mk l k v r) else rotL (mk l k v (rotR r))
  else mk l k v r

end T

def lookupT (cmp : α → α → Int) (k : α) : T α β → Option β
  | .leaf => none
  | .node l k' v' _ r =>
    if cmp k k' = -1 then lookupT cmp k l else if cmp k k' = 0 then some v' else lookupT cmp k r

def insT (cmp : α → α → Int) (k : α) (v : β) : T α β → T α β
  | .leaf => .node .leaf k v 1 .leaf
  | .node l k' v' h r =>
    if cmp k k' = -1 then T.bal (insT cmp k v l) k' v' r
    else if cmp k k' = 0 then .node l k v h r
    else T.bal l k' v' (insT cmp k v r)

/-- 节点 `(l, k, v, r)` 里最小的键值对，和去掉它之后的树。 -/
def popK : T α β → α → β → α × β
  | .leaf, k, v => (k, v)
  | .node ll lk lv _ _, _, _ => popK ll lk lv

def popT : T α β → α → β → T α β → T α β
  | .leaf, _, _, r => r
  | .node ll lk lv _ lr, k, v, r => T.bal (popT ll lk lv lr) k v r

/-- 合并两棵树（左边的键都小于右边的）：用右边最小的键值对作新的根。 -/
def join : T α β → T α β → T α β
  | l, .leaf => l
  | l, .node rl rk rv _ rr => T.bal l (popK rl rk rv).1 (popK rl rk rv).2 (popT rl rk rv rr)

def delT (cmp : α → α → Int) (k : α) : T α β → T α β
  | .leaf => .leaf
  | .node l k' v' _ r =>
    if cmp k k' = -1 then T.bal (delT cmp k l) k' v' r
    else if cmp k k' = 0 then join l r
    else T.bal l k' v' (delT cmp k r)

/-! ## 旋转、再平衡不改变中序遍历 -/

theorem toList_rotR : ∀ t : T α β, (T.rotR t).toList = t.toList
  | .leaf => rfl
  | .node .leaf _ _ _ _ => rfl
  | .node (.node a xk xv _ b) yk yv _ c => by simp [T.rotR, T.mk, T.toList]

theorem toList_rotL : ∀ t : T α β, (T.rotL t).toList = t.toList
  | .leaf => rfl
  | .node _ _ _ _ .leaf => rfl
  | .node a xk xv _ (.node b yk yv _ c) => by simp [T.rotL, T.mk, T.toList]

theorem toList_bal (l : T α β) (k : α) (v : β) (r : T α β) :
    (T.bal l k v r).toList = l.toList ++ (k, v) :: r.toList := by
  unfold T.bal
  repeat' split
  all_goals simp only [toList_rotR, toList_rotL, T.mk, T.toList]

theorem toList_popMin : ∀ (l : T α β) (k : α) (v : β) (r : T α β),
    popK l k v :: (popT l k v r).toList = l.toList ++ (k, v) :: r.toList
  | .leaf, k, v, r => by simp [popK, popT, T.toList]
  | .node ll lk lv _ lr, k, v, r => by
    simp only [popK, popT, toList_bal, T.toList]
    rw [← List.cons_append, toList_popMin ll lk lv lr, List.append_assoc]

theorem toList_join : ∀ (l r : T α β), (join l r).toList = l.toList ++ r.toList
  | l, .leaf => by simp [join, T.toList]
  | l, .node rl rk rv _ rr => by
    simp only [join, toList_bal, T.toList]
    rw [← toList_popMin rl rk rv rr]

/-! ## 列表上的引理（`Library.Map` 的 `lookup`、`ins`、`del` 跳过一段、停在一段里） -/

section
variable {cmp : α → α → Int}

theorem flip (L : OrdLaws cmp) {a b : α} (h : cmp a b = -1) : cmp b a = 1 := by
  have := L.swap a b
  omega

theorem sorted_app : ∀ (A B : List (α × β)), Sorted cmp (A ++ B) →
    Sorted cmp A ∧ Sorted cmp B ∧ ∀ a ∈ A, ∀ b ∈ B, cmp a.1 b.1 = -1
  | [], B, h => ⟨trivial, h, fun a ha => by simp at ha⟩
  | (k, v) :: A, B, h => by
    simp only [List.cons_append] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨s1, s2, s3⟩ := sorted_app A B h2
    refine ⟨⟨fun p hp => h1 p (List.mem_append_left _ hp), s1⟩, s2, fun a ha b hb => ?_⟩
    rcases List.mem_cons.1 ha with e | e
    · rw [e]; exact h1 b (List.mem_append_right _ hb)
    · exact s3 a e b hb

theorem lookup_none {k : α} : ∀ {B : List (α × β)}, (∀ p ∈ B, cmp k p.1 ≠ 0) → lookup cmp k B = none
  | [], _ => rfl
  | (k', v') :: B, h => by
    have h0 : cmp k k' ≠ 0 := h (k', v') (by simp)
    simp only [lookup, h0, ite_false]
    exact lookup_none (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem lookup_app_left {k : α} {B : List (α × β)} (hB : ∀ p ∈ B, cmp k p.1 ≠ 0) :
    ∀ (A : List (α × β)), lookup cmp k (A ++ B) = lookup cmp k A
  | [] => lookup_none hB
  | (k', v') :: A => by
    simp only [List.cons_append, lookup]
    rw [lookup_app_left hB A]

theorem lookup_skip {k : α} {B : List (α × β)} :
    ∀ {A : List (α × β)}, (∀ p ∈ A, cmp k p.1 ≠ 0) → lookup cmp k (A ++ B) = lookup cmp k B
  | [], _ => rfl
  | (k', v') :: A, h => by
    have h0 : cmp k k' ≠ 0 := h (k', v') (by simp)
    simp only [List.cons_append, lookup, h0, ite_false]
    exact lookup_skip (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem ins_app_left {k k' : α} {v v' : β} {B : List (α × β)} (h : cmp k k' = -1) :
    ∀ (A : List (α × β)), ins cmp k v (A ++ (k', v') :: B) = ins cmp k v A ++ (k', v') :: B
  | [] => by simp [ins, h]
  | (a, b) :: A => by
    simp only [List.cons_append, ins]
    by_cases h1 : cmp k a = -1
    · simp [h1]
    · by_cases h2 : cmp k a = 0
      · simp [h2]
      · simp only [h1, h2, ite_false, List.cons_append]
        rw [ins_app_left h A]

theorem ins_skip {k : α} {v : β} {B : List (α × β)} :
    ∀ {A : List (α × β)}, (∀ p ∈ A, cmp k p.1 ≠ -1 ∧ cmp k p.1 ≠ 0) → ins cmp k v (A ++ B) = A ++ ins cmp k v B
  | [], _ => rfl
  | (a, b) :: A, h => by
    have h0 : cmp k a ≠ -1 ∧ cmp k a ≠ 0 := h (a, b) (by simp)
    simp only [List.cons_append, ins, h0.1, h0.2, ite_false]
    rw [ins_skip (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem del_none {k : α} : ∀ {B : List (α × β)}, (∀ p ∈ B, cmp k p.1 ≠ 0) → del cmp k B = B
  | [], _ => rfl
  | (k', v') :: B, h => by
    have h0 : cmp k k' ≠ 0 := h (k', v') (by simp)
    simp only [del, h0, ite_false]
    rw [del_none (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem del_app_left {k : α} {B : List (α × β)} (hB : ∀ p ∈ B, cmp k p.1 ≠ 0) :
    ∀ (A : List (α × β)), del cmp k (A ++ B) = del cmp k A ++ B
  | [] => by simp only [List.nil_append, del]; exact del_none hB
  | (k', v') :: A => by
    simp only [List.cons_append, del]
    by_cases h : cmp k k' = 0
    · simp [h]
    · simp only [h, ite_false, List.cons_append]
      rw [del_app_left hB A]

theorem del_skip {k : α} {B : List (α × β)} :
    ∀ {A : List (α × β)}, (∀ p ∈ A, cmp k p.1 ≠ 0) → del cmp k (A ++ B) = A ++ del cmp k B
  | [], _ => rfl
  | (k', v') :: A, h => by
    have h0 : cmp k k' ≠ 0 := h (k', v') (by simp)
    simp only [List.cons_append, del, h0, ite_false]
    rw [del_skip (fun p hp => h p (List.mem_cons_of_mem _ hp))]

/-! ## 树上的查找、插入、删除等于 `Library.Map` 的参考实现 -/

theorem lookupT_eq (L : OrdLaws cmp) (k : α) :
    ∀ (t : T α β), Sorted cmp t.toList → lookupT cmp k t = lookup cmp k t.toList
  | .leaf, _ => rfl
  | .node l k' v' _ r, hs => by
    simp only [T.toList] at hs ⊢
    obtain ⟨sA, ⟨hB, sB⟩, cross⟩ := sorted_app _ _ hs
    have hA : ∀ a ∈ l.toList, cmp a.1 k' = -1 := fun a ha => cross a ha (k', v') (by simp)
    simp only [lookupT]
    by_cases h1 : cmp k k' = -1
    · rw [ite_eq_left h1, lookupT_eq L k l sA, lookup_app_left]
      intro p hp
      rcases List.mem_cons.1 hp with e | e
      · rw [e]; show cmp k k' ≠ 0; omega
      · have := L.trans _ _ _ h1 (hB p e); omega
    · rw [ite_eq_right h1]
      by_cases h2 : cmp k k' = 0
      · rw [ite_eq_left h2, lookup_skip]
        · simp [lookup, h2]
        · intro a ha
          have := flip L (hA a ha)
          rw [← (L.zero k k').1 h2] at this
          omega
      · rw [ite_eq_right h2]
        have h3 : cmp k k' = 1 := by
          rcases L.range k k' with c | c | c
          · exact absurd c h1
          · exact absurd c h2
          · exact c
        have hk' : cmp k' k = -1 := by have := L.swap k k'; omega
        rw [lookup_skip, lookupT_eq L k r sB]
        · simp only [lookup, h2, ite_false]
        · intro a ha
          have := flip L (L.trans _ _ _ (hA a ha) hk')
          omega

theorem insT_eq (L : OrdLaws cmp) (k : α) (v : β) :
    ∀ (t : T α β), Sorted cmp t.toList → (insT cmp k v t).toList = ins cmp k v t.toList
  | .leaf, _ => rfl
  | .node l k' v' h r, hs => by
    simp only [T.toList] at hs ⊢
    obtain ⟨sA, ⟨_, sB⟩, cross⟩ := sorted_app _ _ hs
    have hA : ∀ a ∈ l.toList, cmp a.1 k' = -1 := fun a ha => cross a ha (k', v') (by simp)
    simp only [insT]
    by_cases h1 : cmp k k' = -1
    · rw [ite_eq_left h1, toList_bal, insT_eq L k v l sA, ins_app_left h1]
    · rw [ite_eq_right h1]
      by_cases h2 : cmp k k' = 0
      · rw [ite_eq_left h2]
        simp only [T.toList]
        rw [ins_skip]
        · simp [ins, h2]
        · intro a ha
          have := flip L (hA a ha)
          rw [← (L.zero k k').1 h2] at this
          exact ⟨by omega, by omega⟩
      · rw [ite_eq_right h2]
        have h3 : cmp k k' = 1 := by
          rcases L.range k k' with c | c | c
          · exact absurd c h1
          · exact absurd c h2
          · exact c
        have hk' : cmp k' k = -1 := by have := L.swap k k'; omega
        rw [toList_bal, insT_eq L k v r sB, ins_skip]
        · simp [ins, h1, h2]
        · intro a ha
          have := flip L (L.trans _ _ _ (hA a ha) hk')
          exact ⟨by omega, by omega⟩

theorem delT_eq (L : OrdLaws cmp) (k : α) :
    ∀ (t : T α β), Sorted cmp t.toList → (delT cmp k t).toList = del cmp k t.toList
  | .leaf, _ => rfl
  | .node l k' v' _ r, hs => by
    simp only [T.toList] at hs ⊢
    obtain ⟨sA, ⟨hB, sB⟩, cross⟩ := sorted_app _ _ hs
    have hA : ∀ a ∈ l.toList, cmp a.1 k' = -1 := fun a ha => cross a ha (k', v') (by simp)
    simp only [delT]
    by_cases h1 : cmp k k' = -1
    · rw [ite_eq_left h1, toList_bal, delT_eq L k l sA, del_app_left]
      intro p hp
      rcases List.mem_cons.1 hp with e | e
      · rw [e]; show cmp k k' ≠ 0; omega
      · have := L.trans _ _ _ h1 (hB p e); omega
    · rw [ite_eq_right h1]
      by_cases h2 : cmp k k' = 0
      · rw [ite_eq_left h2, toList_join, del_skip]
        · simp [del, h2]
        · intro a ha
          have := flip L (hA a ha)
          rw [← (L.zero k k').1 h2] at this
          omega
      · rw [ite_eq_right h2]
        have h3 : cmp k k' = 1 := by
          rcases L.range k k' with c | c | c
          · exact absurd c h1
          · exact absurd c h2
          · exact c
        have hk' : cmp k' k = -1 := by have := L.swap k k'; omega
        rw [toList_bal, delT_eq L k r sB, del_skip]
        · simp [del, h2]
        · intro a ha
          have := flip L (L.trans _ _ _ (hA a ha) hk')
          omega

/-! ## `Library.Map` 的定律对树照样成立 -/

theorem insT_sorted (L : OrdLaws cmp) (k : α) (v : β) (t : T α β) (hs : Sorted cmp t.toList) :
    Sorted cmp (insT cmp k v t).toList := by
  rw [insT_eq L k v t hs]
  exact Core.Library.Map.ins_sorted L k v _ hs

theorem delT_sorted (L : OrdLaws cmp) (k : α) (t : T α β) (hs : Sorted cmp t.toList) :
    Sorted cmp (delT cmp k t).toList := by
  rw [delT_eq L k t hs]
  exact Core.Library.Map.del_sorted k _ hs

theorem lookupT_ins (L : OrdLaws cmp) (k : α) (v : β) (t : T α β) (hs : Sorted cmp t.toList) :
    lookupT cmp k (insT cmp k v t) = some v := by
  rw [lookupT_eq L k _ (insT_sorted L k v t hs), insT_eq L k v t hs]
  exact Core.Library.Map.lookup_ins L k v _

theorem lookupT_del (L : OrdLaws cmp) (k : α) (t : T α β) (hs : Sorted cmp t.toList) :
    lookupT cmp k (delT cmp k t) = none := by
  rw [lookupT_eq L k _ (delT_sorted L k t hs), delT_eq L k t hs]
  exact Core.Library.Map.lookup_del L k _ hs

end

/-! ## 例子：依次插入 1…7，中序遍历有序，高度是 3；删掉 4（根）之后仍有序 -/

def ex : T Int Nat := (List.range 7).foldl (fun t i => insT Core.Library.Math.cmpI (Int.ofNat (i + 1)) i t) .leaf

#eval (ex.toList, ex.height)
#eval ((delT Core.Library.Math.cmpI 4 ex).toList, lookupT Core.Library.Math.cmpI 5 (delT Core.Library.Math.cmpI 4 ex))

end Core.Library.TreeMap
