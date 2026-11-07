import Core.Basic

/-!
# M11（一）：递归类型——经过 `Box` 的链与树

**问题**：`enum List<T> { Cons(Node<T>), Nil }`、`struct Node<T> { v: T, next: Box<List<T>> }` 这样的类型，
一个值在堆上是一条链（一般是一棵树）：每个 `Box` 指向的格子里还可以有 `Box`。
M8 的模型里载荷不再含载荷；这里允许任意深。需要保证：析构按结构递归，一定结束，
不会重复释放，作用域结束时把所有变量拥有的值析构完之后堆是空的（没有泄漏）。

**堆**：`Heap` 是格子的列表，新分配的在前；每个格子记下它拥有的子格子（它的值里的 `Box`，
按类型的结构排好，例如 `Cons` 的格子拥有 `next`）。类型只决定“子格子是哪些”，
所以这里把类型抽象掉，直接记子格子。直接包含自己、中间没有 `Box` 的类型大小是无限的，
编译器在定义处拒绝，与安全无关。

**操作**（由所有权检查保证只作用在变量拥有的值上，即“根”）：
`alloc`：分配新格子，把若干根移进去当子格子（`box(Node { v, next })`）；
`unbox`：按移动拆开一个根，释放它的格子，子格子交给变量（`match` 拆开 `Box` 里的值）；
`drop`：析构一个根，递归释放它和它拥有的整棵子树。

**不变式** `Inv`：格子不重复；子格子都比父格子早分配（`Ordered`，于是没有环）；
根和所有格子的子格子合起来，恰好是每个活着的格子各一次（唯一拥有者，`Perm`）。

**主定理** `scope_end`：从空堆出发经过任意这些操作，作用域结束时析构所有根一定成功（没有重复释放），
而且之后堆是空的（没有泄漏）。析构用“格子数”作燃料，每释放一个格子用掉一份，所以一定结束。

**例子**说明：两个拥有者（共享）会重复释放；没有拥有者的环永远不会被释放——
`Ordered` 排除了环，而只用移动来构造（先有子格子，再分配父格子）总是满足 `Ordered`。
-/

namespace Core.M11

abbrev Cell := Nat

/-- 堆：新分配的在前；每个格子拥有的子格子。 -/
abbrev Heap := List (Cell × List Cell)

def keys : Heap → List Cell
  | [] => []
  | (k, _) :: h => k :: keys h

def kids : Heap → List Cell
  | [] => []
  | (_, cs) :: h => cs ++ kids h

def look : Heap → Cell → Option (List Cell)
  | [], _ => none
  | (k, cs) :: h, l => if k = l then some cs else look h l

def del : Heap → Cell → Heap
  | [], _ => []
  | (k, cs) :: h, l => if k = l then h else (k, cs) :: del h l

/-- 子格子都比父格子早分配（在列表里更靠后），所以拥有关系没有环。 -/
def Ordered : Heap → Prop
  | [] => True
  | (_, cs) :: h => (∀ c ∈ cs, c ∈ keys h) ∧ Ordered h

/-- 析构 `ls` 里的格子和它们拥有的子树。读到已经释放的格子就是错误（重复释放）。燃料用完也算错误。 -/
def dropList : Nat → Heap → List Cell → Option Heap
  | _, h, [] => some h
  | 0, _, _ :: _ => none
  | n + 1, h, l :: ls =>
    match look h l with
    | some cs => dropList n (del h l) (cs ++ ls)
    | none    => none

structure Inv (h : Heap) (roots : List Cell) : Prop where
  nd  : (keys h).Nodup
  ord : Ordered h
  own : (roots ++ kids h).Perm (keys h)

/-! ## 删除一个格子 -/

theorem look_some : ∀ (h : Heap) (l : Cell), l ∈ keys h → ∃ cs, look h l = some cs
  | [], _, hl => by simp [keys] at hl
  | (k, ks) :: h, l, hl => by
    by_cases hk : k = l
    · exact ⟨ks, by simp [look, hk]⟩
    · simp only [keys, List.mem_cons] at hl
      rcases hl with e | hl
      · exact absurd e.symm hk
      · obtain ⟨cs, e⟩ := look_some h l hl
        exact ⟨cs, by simp [look, hk, e]⟩

theorem look_keys : ∀ (h : Heap) (l : Cell) (cs : List Cell), look h l = some cs →
    (keys h).Perm (l :: keys (del h l))
  | [], _, _, e => by simp [look] at e
  | (k, ks) :: h, l, cs, e => by
    by_cases hk : k = l
    · subst hk
      have : del ((k, ks) :: h) k = h := by simp [del]
      rw [this]
      exact List.Perm.refl _
    · simp [look, hk] at e
      have ih := look_keys h l cs e
      have : del ((k, ks) :: h) l = (k, ks) :: del h l := by simp [del, hk]
      rw [this]
      show (k :: keys h).Perm (l :: k :: keys (del h l))
      exact (ih.cons k).trans (List.Perm.swap l k _)

theorem look_kids : ∀ (h : Heap) (l : Cell) (cs : List Cell), look h l = some cs →
    (kids h).Perm (cs ++ kids (del h l))
  | [], _, _, e => by simp [look] at e
  | (k, ks) :: h, l, cs, e => by
    by_cases hk : k = l
    · simp [look, hk] at e
      subst e
      have : del ((k, ks) :: h) l = h := by simp [del, hk]
      rw [this]
      exact List.Perm.refl _
    · simp [look, hk] at e
      have ih := look_kids h l cs e
      have : del ((k, ks) :: h) l = (k, ks) :: del h l := by simp [del, hk]
      rw [this]
      show (ks ++ kids h).Perm (cs ++ (ks ++ kids (del h l)))
      refine (ih.append_left ks).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

theorem mem_del : ∀ (h : Heap) (l c : Cell), c ∈ keys h → c ≠ l → c ∈ keys (del h l)
  | [], _, _, hc, _ => by simp [keys] at hc
  | (k, ks) :: h, l, c, hc, hne => by
    simp only [keys, List.mem_cons] at hc
    by_cases hk : k = l
    · have : del ((k, ks) :: h) l = h := by simp [del, hk]
      rw [this]
      rcases hc with e | hc
      · exact absurd (e.trans hk) hne
      · exact hc
    · have : del ((k, ks) :: h) l = (k, ks) :: del h l := by simp [del, hk]
      rw [this]
      show c ∈ k :: keys (del h l)
      rcases hc with e | hc
      · simp [e]
      · exact List.mem_cons_of_mem _ (mem_del h l c hc hne)

theorem ord_del : ∀ (h : Heap) (l : Cell), Ordered h → l ∉ kids h → Ordered (del h l)
  | [], _, _, _ => by simp [del, Ordered]
  | (k, ks) :: h, l, ho, hn => by
    simp only [Ordered] at ho
    simp only [kids, List.mem_append, not_or] at hn
    by_cases hk : k = l
    · have : del ((k, ks) :: h) l = h := by simp [del, hk]
      rw [this]
      exact ho.2
    · have : del ((k, ks) :: h) l = (k, ks) :: del h l := by simp [del, hk]
      rw [this]
      show (∀ c ∈ ks, c ∈ keys (del h l)) ∧ Ordered (del h l)
      exact ⟨fun c hc => mem_del h l c (ho.1 c hc) (fun e => hn.1 (e ▸ hc)), ord_del h l ho.2 hn.2⟩

theorem kids_sub : ∀ (h : Heap), Ordered h → ∀ c ∈ kids h, c ∈ keys h
  | [], _, c, hc => by simp [kids] at hc
  | (k, ks) :: h, ho, c, hc => by
    simp only [Ordered] at ho
    show c ∈ k :: keys h
    rcases List.mem_append.1 hc with hc | hc
    · exact List.mem_cons_of_mem _ (ho.1 c hc)
    · exact List.mem_cons_of_mem _ (kids_sub h ho.2 c hc)

/-! ## 操作保持不变式 -/

/-- 按移动拆开一个根：释放它的格子，子格子成为根。 -/
theorem unbox_inv (h : Heap) (l : Cell) (rest : List Cell) (hI : Inv h (l :: rest)) :
    ∃ cs, look h l = some cs ∧ Inv (del h l) (cs ++ rest) := by
  have hown : (l :: (rest ++ kids h)).Perm (keys h) := hI.own
  have hl : l ∈ keys h := hown.subset (by simp)
  obtain ⟨cs, hc⟩ := look_some h l hl
  have p1 := look_keys h l cs hc
  have p2 := look_kids h l cs hc
  have hn : l ∉ kids h := by
    have hnd := hown.nodup_iff.2 hI.nd
    simp only [List.nodup_cons, List.mem_append, not_or] at hnd
    exact hnd.1.2
  refine ⟨cs, hc, ⟨(p1.nodup_iff.1 hI.nd).of_cons, ord_del h l hI.ord hn, ?_⟩⟩
  have q : (rest ++ kids h).Perm (keys (del h l)) := List.Perm.cons_inv (hown.trans p1)
  have q2 : (rest ++ (cs ++ kids (del h l))).Perm (keys (del h l)) := (p2.append_left rest).symm.trans q
  have q3 : (cs ++ rest ++ kids (del h l)).Perm (rest ++ (cs ++ kids (del h l))) := by
    rw [← List.append_assoc]
    exact List.perm_append_comm.append_right _
  exact q3.trans q2

/-- 分配新格子，把若干根移进去当子格子。 -/
theorem alloc_inv (h : Heap) (l : Cell) (cs rest : List Cell) (hI : Inv h (cs ++ rest))
    (hl : l ∉ keys h) : Inv ((l, cs) :: h) (l :: rest) where
  nd := by
    show (l :: keys h).Nodup
    exact List.nodup_cons.2 ⟨hl, hI.nd⟩
  ord := by
    show (∀ c ∈ cs, c ∈ keys h) ∧ Ordered h
    exact ⟨fun c hc => hI.own.subset (by simp [hc]), hI.ord⟩
  own := by
    show (l :: (rest ++ (cs ++ kids h))).Perm (l :: keys h)
    refine List.Perm.cons l ?_
    have q : (rest ++ (cs ++ kids h)).Perm (cs ++ rest ++ kids h) := by
      rw [← List.append_assoc]
      exact List.perm_append_comm.append_right _
    exact q.trans hI.own

/-- 析构成功时，剩下的根仍然满足不变式。 -/
theorem drop_inv : ∀ (n : Nat) (h : Heap) (ls rest : List Cell) (h' : Heap), Inv h (ls ++ rest) →
    dropList n h ls = some h' → Inv h' rest
  | _, h, [], rest, h', hI, e => by
    simp [dropList] at e
    subst e
    exact hI
  | 0, _, _ :: _, _, _, _, e => by simp [dropList] at e
  | n + 1, h, l :: ls, rest, h', hI, e => by
    obtain ⟨cs, hc, hI2⟩ := unbox_inv h l (ls ++ rest) hI
    simp [dropList, hc] at e
    have hI3 : Inv (del h l) ((cs ++ ls) ++ rest) := by rw [List.append_assoc]; exact hI2
    exact drop_inv n (del h l) (cs ++ ls) rest h' hI3 e

/-- 燃料不少于格子数时，析构一定成功：不会读到已释放的格子，也不会因为燃料用完而停下（析构一定结束）。 -/
theorem drop_total : ∀ (n : Nat) (h : Heap) (ls rest : List Cell), Inv h (ls ++ rest) →
    (keys h).length ≤ n → ∃ h', dropList n h ls = some h'
  | _, h, [], _, _, _ => ⟨h, by simp [dropList]⟩
  | 0, h, l :: ls, rest, hI, hlen => by
    have hl : l ∈ keys h := hI.own.subset (by simp)
    have := List.length_pos_of_mem hl
    exact absurd hlen (by omega)
  | n + 1, h, l :: ls, rest, hI, hlen => by
    obtain ⟨cs, hc, hI2⟩ := unbox_inv h l (ls ++ rest) hI
    have hlen' : (keys (del h l)).length ≤ n := by
      have := (look_keys h l cs hc).length_eq
      simp at this
      omega
    have hI3 : Inv (del h l) ((cs ++ ls) ++ rest) := by rw [List.append_assoc]; exact hI2
    obtain ⟨h', e⟩ := drop_total n (del h l) (cs ++ ls) rest hI3 hlen'
    exact ⟨h', by simp [dropList, hc, e]⟩

/-- 没有根时堆是空的：每个格子都有拥有者，而最新的格子不可能被更早的格子拥有。 -/
theorem no_leak : ∀ (h : Heap), Inv h [] → h = []
  | [], _ => rfl
  | (k, ks) :: h, hI => by
    exfalso
    have hk : k ∈ ks ++ kids h := hI.own.symm.subset (by simp [keys])
    have ho : Ordered ((k, ks) :: h) := hI.ord
    simp only [Ordered] at ho
    have hin : k ∈ keys h := by
      rcases List.mem_append.1 hk with hc | hc
      · exact ho.1 k hc
      · exact kids_sub h ho.2 k hc
    have hnd : (k :: keys h).Nodup := hI.nd
    exact (List.nodup_cons.1 hnd).1 hin

/-! ## 主定理 -/

/-- 从空堆出发能到达的状态：分配、按移动拆开、析构一个根，以及根的重新排列（变量之间移动）。 -/
inductive Reach : Heap → List Cell → Prop
  | empty : Reach [] []
  | alloc {h l cs rest} : Reach h (cs ++ rest) → l ∉ keys h → Reach ((l, cs) :: h) (l :: rest)
  | unbox {h l cs rest} : Reach h (l :: rest) → look h l = some cs → Reach (del h l) (cs ++ rest)
  | drop {h h' l rest n} : Reach h (l :: rest) → dropList n h [l] = some h' → Reach h' rest
  | perm {h r r'} : Reach h r → r.Perm r' → Reach h r'

theorem reach_inv {h : Heap} {r : List Cell} (hr : Reach h r) : Inv h r := by
  induction hr with
  | empty => exact ⟨List.nodup_nil, trivial, List.Perm.refl _⟩
  | @alloc h l cs rest _ hl ih => exact alloc_inv h l cs rest ih hl
  | @unbox h l cs rest _ hc ih =>
    obtain ⟨cs', hc', hI⟩ := unbox_inv h l rest ih
    rw [hc] at hc'
    cases hc'
    exact hI
  | @drop h h' l rest n _ e ih => exact drop_inv n h [l] rest h' ih e
  | @perm h r r' _ hp ih => exact ⟨ih.nd, ih.ord, (hp.symm.append_right _).trans ih.own⟩

/-- **主定理**：作用域结束时析构所有根，一定成功（没有重复释放、一定结束），并且之后堆是空的（没有泄漏）。 -/
theorem scope_end {h : Heap} {roots : List Cell} (hr : Reach h roots) :
    dropList (keys h).length h roots = some [] := by
  have hI' : Inv h (roots ++ []) := by rw [List.append_nil]; exact reach_inv hr
  obtain ⟨h', e⟩ := drop_total _ h roots [] hI' (Nat.le_refl _)
  have := no_leak h' (drop_inv _ h roots [] h' hI' e)
  rw [e, this]

/-! ## 例子 -/

/-- 链 3 → 2 → 1：析构头一个格子，整条链都被释放。 -/
def chain : Heap := [(3, [2]), (2, [1]), (1, [])]
example : dropList 3 chain [3] = some [] := rfl

/-- 按移动拆开 3，2 交给变量，再析构 2。 -/
example : dropList 3 (del chain 3) [2] = some [] := rfl

/-- 两个拥有者（共享同一个格子）：重复释放。 -/
example : dropList 3 [(2, [1]), (1, [])] [2, 1] = none := rfl

/-- 没有拥有者的环：永远不会被释放（泄漏）。`Ordered` 排除了它。 -/
example : dropList 2 [(1, [2]), (2, [1])] [] = some [(1, [2]), (2, [1])] := rfl
example : ¬ Ordered [(1, [2]), (2, [1])] := by
  simp [Ordered, keys]

end Core.M11
