import Core.Datatypes.Vec

/-!
# `for x in inout v`——循环里改 Vec 的元素

**语法和规则**：`for x in inout v { … }`，每一轮 `x` 是第 i 个元素的可变借用（`inout`）。
- 循环体可以读 `x`、在原地改 `x`（字段赋值、`inout` 实参），也可以给 `x` 整体赋值；
- 循环体里**不能提到 `v`**：不能 `push`、`pop`、读、再借——`v` 整个借给了循环；
- 不能把 `x` 移走（它是借来的）；给 `x` 整体赋值先析构旧值。

分两部分证明。

**（一）排他性**：循环体不提到 `v` 时，每一轮访问的下标都在界内，`v` 的长度不变（`loop_ok`）。
反例 `bad_pop`：循环体里 `pop(v)` 之后，最后一轮的下标越界——这正是“不能提到 `v`”要排除的。

**（二）拥有关系**：给 `x` 整体赋值，就是把数组格子 `k` 的子格子 `pre ++ e :: post` 换成 `pre ++ n :: post`，
旧值 `e` 成为一个根、随后析构。这一步由 `Datatypes.Vec` 已有的操作组合而成（`detach` 后缀、重新排列根、`attach` 回去），
所以 `Datatypes.Vec` 的不变式和 `scope_end` 照样成立（`replace_reach`、`replace_scope_end`）。
条件只有一个：数组不在新值的子树里（`¬ Below … [n] k`）——和 `push` 一样，由排他性保证
（循环体里不能提到 `v`，新值也就不可能拥有 `v` 的缓冲区）。`post` 里的元素不会拥有数组，这一条由秩推出，不是假设。
-/

namespace Core.Datatypes.VecInout

/-! ## （一）排他性：下标在界内，长度不变 -/

/-- 循环体里的操作（只关心向量的长度和元素）。`push y a`、`pop y` 作用于变量 `y` 的向量；
    `setX a` 是 `x = a`（整体赋值第 i 个元素），`addX a` 是在原地改 `x`。 -/
inductive Op
  | push (y a : Nat)
  | pop (y : Nat)
  | setX (a : Nat)
  | addX (a : Nat)

/-- 操作是否提到了循环的向量 `v`。 -/
def touches (v : Nat) : Op → Bool
  | .push y _ => y == v
  | .pop y => y == v
  | _ => false

abbrev St := Nat → List Nat

def upd (σ : St) (y : Nat) (l : List Nat) : St := fun z => if z = y then l else σ z

/-- 一个操作；访问 `x`（`v` 的第 i 个元素）越界时出错（`none`）。 -/
def step (v i : Nat) (σ : St) : Op → Option St
  | .push y a => some (upd σ y (σ y ++ [a]))
  | .pop y => some (upd σ y (σ y).dropLast)
  | .setX a => if i < (σ v).length then some (upd σ v ((σ v).set i a)) else none
  | .addX a => if h : i < (σ v).length then some (upd σ v ((σ v).set i ((σ v)[i] + a))) else none

def body (v i : Nat) : St → List Op → Option St
  | σ, [] => some σ
  | σ, o :: os =>
    match step v i σ o with
    | some σ' => body v i σ' os
    | none => none

/-- 从下标 `i` 开始再跑 `k` 轮。 -/
def loop (v : Nat) (b : List Op) : Nat → Nat → St → Option St
  | 0, _, σ => some σ
  | k + 1, i, σ =>
    match body v i σ b with
    | some σ' => loop v b k (i + 1) σ'
    | none => none

/-- 编译器的检查：循环体不提到 `v`。 -/
def okBody (v : Nat) (b : List Op) : Bool := b.all (fun o => !touches v o)

theorem step_ok (v i : Nat) (σ : St) (o : Op) (ho : touches v o = false) (hi : i < (σ v).length) :
    ∃ σ', step v i σ o = some σ' ∧ (σ' v).length = (σ v).length := by
  cases o with
  | push y a =>
    have hne : v ≠ y := by
      intro e; subst e; simp [touches] at ho
    exact ⟨_, rfl, by simp [upd, hne]⟩
  | pop y =>
    have hne : v ≠ y := by
      intro e; subst e; simp [touches] at ho
    exact ⟨_, rfl, by simp [upd, hne]⟩
  | setX a => exact ⟨upd σ v ((σ v).set i a), by simp [step, hi], by simp [upd]⟩
  | addX a => exact ⟨upd σ v ((σ v).set i ((σ v)[i] + a)), by simp [step, hi], by simp [upd]⟩

theorem body_ok (v i : Nat) : ∀ (b : List Op) (σ : St), okBody v b = true → i < (σ v).length →
    ∃ σ', body v i σ b = some σ' ∧ (σ' v).length = (σ v).length
  | [], σ, _, _ => ⟨σ, rfl, rfl⟩
  | o :: os, σ, hb, hi => by
    simp only [okBody, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hb
    obtain ⟨σ1, e1, l1⟩ := step_ok v i σ o hb.1 hi
    obtain ⟨σ2, e2, l2⟩ := body_ok v i os σ1 (by simpa [okBody] using hb.2) (by omega)
    exact ⟨σ2, by simp [body, e1, e2], by omega⟩

/-- **结论（一）**：循环体不提到 `v` 时，从下标 `i` 跑到末尾，每一轮都不越界，`v` 的长度不变。 -/
theorem loop_ok (v : Nat) (b : List Op) (hb : okBody v b = true) :
    ∀ (k i : Nat) (σ : St), i + k = (σ v).length →
      ∃ σ', loop v b k i σ = some σ' ∧ (σ' v).length = (σ v).length
  | 0, _, σ, _ => ⟨σ, rfl, rfl⟩
  | k + 1, i, σ, hk => by
    obtain ⟨σ1, e1, l1⟩ := body_ok v i b σ hb (by omega)
    obtain ⟨σ2, e2, l2⟩ := loop_ok v b hb k (i + 1) σ1 (by omega)
    exact ⟨σ2, by simp [loop, e1, e2], by omega⟩

/-- 整个循环：从 0 跑 `len(v)` 轮。 -/
theorem for_inout_ok (v : Nat) (b : List Op) (hb : okBody v b = true) (σ : St) :
    ∃ σ', loop v b (σ v).length 0 σ = some σ' ∧ (σ' v).length = (σ v).length :=
  loop_ok v b hb _ 0 σ (by omega)

/-- **反例**：循环体里 `pop(v)` 再写 `x`，第二轮越界。规则拒绝它（`okBody` 为假）。 -/
theorem bad_pop : loop 0 [.pop 0, .setX 5] 2 0 (fun _ => [1, 2]) = none ∧
    okBody 0 [.pop 0, .setX 5] = false := ⟨rfl, rfl⟩

/-! ## （二）拥有关系：整体赋值 `x = 新值` -/

open Core.Datatypes.Recursive (Cell Heap keys kids look del dropList)
open Core.Datatypes.Vec (Ranked Below Reach setKids look_mem keys_of_mem mem_set reach_inv drop_total)

theorem look_set : ∀ (h : Heap) (l : Cell) (ns : List Cell), l ∈ keys h → look (setKids h l ns) l = some ns
  | [], _, _, hl => by simp [keys] at hl
  | (k, ks) :: h, l, ns, hl => by
    by_cases hk : k = l
    · simp [setKids, look, hk]
    · simp only [keys, List.mem_cons] at hl
      rcases hl with hl | hl
      · exact absurd hl.symm hk
      · simp only [setKids, hk, ite_false, look]
        exact look_set h l ns hl

theorem below_rank {r : Cell → Nat} {h : Heap} {xs : List Cell} (hr : Ranked r h) {c : Cell}
    (hb : Below h xs c) : ∃ x ∈ xs, r c ≤ r x := by
  induction hb with
  | root hc => exact ⟨_, hc, Nat.le_refl _⟩
  | step _ hp hc ih =>
    obtain ⟨x, hx, hle⟩ := ih
    exact ⟨x, hx, Nat.le_of_lt (Nat.lt_of_lt_of_le (hr _ _ hp _ hc) hle)⟩

theorem below_cons {h : Heap} {n : Cell} {post : List Cell} {c : Cell} (hb : Below h (n :: post) c) :
    Below h [n] c ∨ Below h post c := by
  induction hb with
  | root hc =>
    simp only [List.mem_cons] at hc
    rcases hc with hc | hc
    · exact Or.inl (Below.root (by simp [hc]))
    · exact Or.inr (Below.root hc)
  | step _ hp hc ih =>
    rcases ih with ih | ih
    · exact Or.inl (Below.step ih hp hc)
    · exact Or.inr (Below.step ih hp hc)

/-- **结论（二）**：数组格子 `k` 的元素是 `pre ++ e :: post`，新值 `n` 是一个根。整体赋值之后元素是 `pre ++ n :: post`，
    旧值 `e` 成为根（随后析构），仍是 `Datatypes.Vec` 能到达的状态。 -/
theorem replace_reach {h : Heap} {k e n : Cell} {pre post rest : List Cell}
    (hr : Reach h (n :: rest)) (hk : look h k = some (pre ++ e :: post))
    (hn : ¬ Below (setKids h k pre) [n] k) :
    Reach (setKids (setKids h k pre) k (pre ++ n :: post)) (e :: rest) := by
  -- 取下后缀 e :: post
  have h1 : Reach (setKids h k pre) ((e :: post) ++ (n :: rest)) := Reach.detach hr hk
  -- 根重新排列成 (n :: post) ++ (e :: rest)
  have hp : ((e :: post) ++ (n :: rest)).Perm ((n :: post) ++ (e :: rest)) := by
    simp only [List.cons_append]
    exact (List.perm_middle.cons e).trans ((List.Perm.swap n e _).trans (List.perm_middle.symm.cons n))
  have h2 : Reach (setKids h k pre) ((n :: post) ++ (e :: rest)) := Reach.perm h1 hp
  -- k 还在堆里，子格子是 pre
  have hmem := look_mem h k _ hk
  have hlook : look (setKids h k pre) k = some pre := look_set h k pre (keys_of_mem h k _ hmem)
  -- post 里的元素不拥有数组：秩
  obtain ⟨r, hrk⟩ := (reach_inv hr).rank
  have hr1 : Ranked r (setKids h k pre) := by
    intro p cs hpc c hc
    rcases mem_set h k pre (p, cs) hpc with hpc | hpc
    · exact hrk p cs hpc c hc
    · simp only [Prod.mk.injEq] at hpc
      obtain ⟨rfl, rfl⟩ := hpc
      exact hrk _ _ hmem c (by simp [hc])
  have hpost : ¬ Below (setKids h k pre) post k := by
    intro hb
    obtain ⟨x, hx, hle⟩ := below_rank hr1 hb
    have := hrk _ _ hmem x (by simp [hx])
    omega
  have hnb : ¬ Below (setKids h k pre) (n :: post) k := by
    intro hb
    rcases below_cons hb with hb | hb
    · exact hn hb
    · exact hpost hb
  exact Reach.attach h2 hlook hnb

/-- 元素个数不变。 -/
theorem replace_len (pre post : List Cell) (e n : Cell) :
    (pre ++ n :: post).length = (pre ++ e :: post).length := by simp

/-- 析构旧值之后仍是能到达的状态，所以作用域结束时析构成功、不泄漏（`Datatypes.Vec` 的 `scope_end`）。 -/
theorem replace_scope_end {h : Heap} {k e n : Cell} {pre post rest : List Cell}
    (hr : Reach h (n :: rest)) (hk : look h k = some (pre ++ e :: post))
    (hn : ¬ Below (setKids h k pre) [n] k) :
    ∃ h', Reach h' rest ∧ dropList (keys h').length h' rest = some [] := by
  have h2 := replace_reach hr hk hn
  have hI : Core.Datatypes.Vec.Inv _ ([e] ++ rest) := reach_inv h2
  obtain ⟨h', e'⟩ := drop_total _ _ [e] rest hI (Nat.le_refl _)
  have h3 : Reach h' rest := Reach.drop h2 e'
  exact ⟨h', h3, Core.Datatypes.Vec.scope_end h3⟩

end Core.Datatypes.VecInout
