import Core.M2b

/-!
# M13（一）：部分移动

结构体变量有 `K` 个字段，每个字段拥有一个值（例如一个 `Box`）。
检查器按**字段**记状态：`let a = p.a` 只把 `p.a` 标成已移走，`p.b` 照常可以用、可以移走；
整体使用、整体移动要求每个字段都在；整体赋新值要求每个字段都已经没有值（之前用 `freeField` 释放掉剩下的字段，
编译器在赋值前自动这样做）。分支合并、`maybe` 的处理和 M2b 一样，只是按字段进行。

**做法**：变量 `x` 的字段 `f` 编号成一个位置 `pl K x f = f + x * K`。每个结构体操作展开（`expand`）
成 M2b 的若干条语句：整体操作是对每个字段各做一次，部分移动就是一次 `move`。
作用域结束时 M2b 的 `dropAll` 按每个位置的 drop flag 释放，也就是只释放还在的字段。

**主定理** `safety_and_no_leak`：本文件的检查器接受的程序，展开之后被 M2b 的检查器接受
（`itemsAgree`），所以由 M2b 的主定理，无论分支怎么走，执行和作用域结束时按字段的释放都不出错，
并且结束时堆是空的：部分移动之后剩下的字段恰好释放一次，移走的字段不会再被释放。
-/

namespace Core.M13
open Core.M1 (Stmt)
open Core.M2 (varsOk)
open Core.M2b (Own SEnv join checkS checkStmtV checkList)

/-! ## 字段的位置 -/

/-- 变量 `x` 的字段 `f`（每个变量 `K` 个字段）。 -/
def pl (K x f : Nat) : Nat := f + x * K

theorem pl_inj {K x y i j : Nat} (hi : i < K) (hj : j < K) (h : pl K x i = pl K y j) :
    x = y ∧ i = j := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hx : pl K x i / K = x := by
    simp only [pl]
    rw [Nat.add_mul_div_right i x hK, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hy : pl K y j / K = y := by
    simp only [pl]
    rw [Nat.add_mul_div_right j y hK, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hxy : x = y := by rw [← hx, ← hy, h]
  subst hxy
  simp only [pl] at h
  exact ⟨rfl, Nat.add_right_cancel h⟩

theorem pl_ne_same {K x i n : Nat} (hn : n < K) (hi : i < n) : pl K x n ≠ pl K x i := by
  intro heq
  have h := (pl_inj hn (Nat.lt_trans hi hn) heq).2
  rw [h] at hi
  exact Nat.lt_irrefl _ hi

theorem pl_ne_var {K x y i j : Nat} (hi : i < K) (hj : j < K) (hxy : x ≠ y) :
    pl K x i ≠ pl K y j :=
  fun heq => hxy (pl_inj hi hj heq).1

theorem pl_lt {K V x f : Nat} (hx : x < V) (hf : f < K) : pl K x f < V * K := by
  have h1 : f + x * K < K + x * K := Nat.add_lt_add_right hf _
  have h2 : (x + 1) * K = K + x * K := by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have h3 : (x + 1) * K ≤ V * K := Nat.mul_le_mul (Nat.succ_le_of_lt hx) (Nat.le_refl K)
  exact Nat.lt_of_lt_of_le (by rw [h2]; exact h1) h3

/-! ## 结构体上的操作与静态检查 -/

inductive Op
  | new (x : Nat)                 -- x = S { … }：每个字段得到新值
  | moveField (x f y g : Nat)     -- 字段 y.g 接收 x.f（部分移动；y 是普通变量时取 g = 0）
  | moveAll (x y : Nat)           -- y = x：整体移动
  | useField (x f : Nat)          -- 读、借用一个字段
  | useAll (x : Nat)              -- 整体读、借用
  | freeField (x f : Nat)         -- 释放一个字段（交给会释放它的函数，或者整体赋值前释放剩下的字段）

/-- 字段 `0 … n-1` 的状态都是 `o`。 -/
def allIs (K : Nat) (σ : SEnv) (x : Nat) (o : Own) : Nat → Bool
  | 0     => true
  | n + 1 => allIs K σ x o n && decide (σ (pl K x n) = o)

/-- 把字段 `0 … n-1` 的状态都改成 `o`。 -/
def setAll (K : Nat) (σ : SEnv) (x : Nat) (o : Own) : Nat → SEnv
  | 0     => σ
  | n + 1 => upd (setAll K σ x o n) (pl K x n) o

/-- 整体移动后的状态：`x` 的字段都没有值，`y` 的字段都有值。 -/
def moveAllS (K : Nat) (σ : SEnv) (x y : Nat) : Nat → SEnv
  | 0     => σ
  | n + 1 => upd (upd (moveAllS K σ x y n) (pl K x n) .no) (pl K y n) .yes

/-- `V` 个变量、每个 `K` 个字段。 -/
def checkOp (K V : Nat) (σ : SEnv) : Op → Option SEnv
  | .new x =>
      if x < V ∧ allIs K σ x .no K = true then some (setAll K σ x .yes K) else none
  | .moveField x f y g =>
      if x < V ∧ y < V ∧ f < K ∧ g < K ∧ (x ≠ y ∨ f ≠ g) ∧
          σ (pl K x f) = .yes ∧ σ (pl K y g) = .no
      then some (upd (upd σ (pl K x f) .no) (pl K y g) .yes) else none
  | .moveAll x y =>
      if x < V ∧ y < V ∧ x ≠ y ∧ allIs K σ x .yes K = true ∧ allIs K σ y .no K = true
      then some (moveAllS K σ x y K) else none
  | .useField x f => if x < V ∧ f < K ∧ σ (pl K x f) = .yes then some σ else none
  | .useAll x => if x < V ∧ allIs K σ x .yes K = true then some σ else none
  | .freeField x f =>
      if x < V ∧ f < K ∧ σ (pl K x f) = .yes then some (upd σ (pl K x f) .no) else none

def checkOps (K V : Nat) (σ : SEnv) : List Op → Option SEnv
  | []      => some σ
  | o :: os =>
    match checkOp K V σ o with
    | some σ' => checkOps K V σ' os
    | none    => none

inductive SItem
  | op     (o : Op)
  | branch (a b : List Op)

def checkItem (K V : Nat) (σ : SEnv) : SItem → Option SEnv
  | .op o       => checkOp K V σ o
  | .branch a b =>
    match checkOps K V σ a, checkOps K V σ b with
    | some σa, some σb => some (join σa σb)
    | _, _             => none

def checkItems (K V : Nat) (σ : SEnv) : List SItem → Option SEnv
  | []        => some σ
  | it :: its =>
    match checkItem K V σ it with
    | some σ' => checkItems K V σ' its
    | none    => none

/-! ## 展开成 M2b 的语句 -/

def allocs (K x : Nat) : Nat → List Stmt
  | 0     => []
  | n + 1 => allocs K x n ++ [.alloc (pl K x n)]

def moves (K x y : Nat) : Nat → List Stmt
  | 0     => []
  | n + 1 => moves K x y n ++ [.move (pl K x n) (pl K y n)]

def uses (K x : Nat) : Nat → List Stmt
  | 0     => []
  | n + 1 => uses K x n ++ [.use (pl K x n)]

def expand (K : Nat) : Op → List Stmt
  | .new x             => allocs K x K
  | .moveField x f y g => [.move (pl K x f) (pl K y g)]
  | .moveAll x y       => moves K x y K
  | .useField x f      => [.use (pl K x f)]
  | .useAll x          => uses K x K
  | .freeField x f     => [.free (pl K x f)]

def expandOps (K : Nat) : List Op → List Stmt
  | []      => []
  | o :: os => expand K o ++ expandOps K os

def lowerItem (K : Nat) : SItem → List M2b.Item
  | .op o       => (expand K o).map M2b.Item.stmt
  | .branch a b => [.branch (expandOps K a) (expandOps K b)]

def lowerItems (K : Nat) : List SItem → List M2b.Item
  | []        => []
  | it :: its => lowerItem K it ++ lowerItems K its

/-! ## 展开后的检查 -/

theorem checkList_append (N : Nat) (a b : List Stmt) :
    ∀ σ, checkList N σ (a ++ b) = (checkList N σ a).bind (fun σ' => checkList N σ' b) := by
  induction a with
  | nil => intro σ; rfl
  | cons t ts ih =>
    intro σ
    simp only [List.cons_append, checkList]
    cases checkStmtV N σ t with
    | none => rfl
    | some σ' => exact ih σ'

theorem items_map_append (N : Nat) (ts : List Stmt) (rest : List M2b.Item) :
    ∀ σ, M2b.checkItems N σ (ts.map M2b.Item.stmt ++ rest) =
      (checkList N σ ts).bind (fun σ' => M2b.checkItems N σ' rest) := by
  induction ts with
  | nil => intro σ; rfl
  | cons t ts ih =>
    intro σ
    simp only [List.map_cons, List.cons_append, M2b.checkItems, M2b.checkItem, checkList]
    cases checkStmtV N σ t with
    | none => rfl
    | some σ' => exact ih σ'

theorem allIs_get {K : Nat} {σ : SEnv} {x : Nat} {o : Own} :
    ∀ n, allIs K σ x o n = true → ∀ i, i < n → σ (pl K x i) = o := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro h i hi
    simp only [allIs, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hin : i = n
    · rw [hin]; exact h.2
    · exact ih h.1 i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hin)

theorem setAll_other {K : Nat} {σ : SEnv} {x : Nat} {o : Own} :
    ∀ n p, (∀ i, i < n → p ≠ pl K x i) → setAll K σ x o n p = σ p := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro p hp
    simp only [setAll]
    rw [upd_other _ _ (hp n (Nat.lt_succ_self n))]
    exact ih p (fun i hi => hp i (Nat.lt_succ_of_lt hi))

theorem moveAllS_other {K : Nat} {σ : SEnv} {x y : Nat} :
    ∀ n p, (∀ i, i < n → p ≠ pl K x i ∧ p ≠ pl K y i) → moveAllS K σ x y n p = σ p := by
  intro n
  induction n with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro p hp
    simp only [moveAllS]
    rw [upd_other _ _ (hp n (Nat.lt_succ_self n)).2, upd_other _ _ (hp n (Nat.lt_succ_self n)).1]
    exact ih p (fun i hi => hp i (Nat.lt_succ_of_lt hi))

theorem allocs_ok {K V : Nat} {σ : SEnv} {x : Nat} (hx : x < V)
    (hno : ∀ i, i < K → σ (pl K x i) = .no) :
    ∀ n, n ≤ K → checkList (V * K) σ (allocs K x n) = some (setAll K σ x .yes n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnK : n < K := hn
    simp only [allocs]
    rw [checkList_append, ih (Nat.le_of_lt hnK)]
    have hcur : setAll K σ x .yes n (pl K x n) = .no := by
      rw [setAll_other n (pl K x n) (fun i hi => pl_ne_same hnK hi)]
      exact hno n hnK
    simp [checkList, checkStmtV, varsOk, checkS, hcur, pl_lt hx hnK, setAll]

theorem moves_ok {K V : Nat} {σ : SEnv} {x y : Nat} (hy : y < V) (hxy : x ≠ y)
    (hyes : ∀ i, i < K → σ (pl K x i) = .yes) (hno : ∀ i, i < K → σ (pl K y i) = .no) :
    ∀ n, n ≤ K → checkList (V * K) σ (moves K x y n) = some (moveAllS K σ x y n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnK : n < K := hn
    simp only [moves]
    rw [checkList_append, ih (Nat.le_of_lt hnK)]
    have hcx : moveAllS K σ x y n (pl K x n) = .yes := by
      rw [moveAllS_other n (pl K x n)
        (fun i hi => ⟨pl_ne_same hnK hi, pl_ne_var hnK (Nat.lt_trans hi hnK) hxy⟩)]
      exact hyes n hnK
    have hcy : moveAllS K σ x y n (pl K y n) = .no := by
      rw [moveAllS_other n (pl K y n)
        (fun i hi => ⟨pl_ne_var hnK (Nat.lt_trans hi hnK) (Ne.symm hxy), pl_ne_same hnK hi⟩)]
      exact hno n hnK
    have hne : pl K x n ≠ pl K y n := pl_ne_var hnK hnK hxy
    simp [checkList, checkStmtV, varsOk, checkS, hcx, hcy, hne, pl_lt hy hnK, moveAllS]

theorem uses_ok {K V : Nat} {σ : SEnv} {x : Nat}
    (hyes : ∀ i, i < K → σ (pl K x i) = .yes) :
    ∀ n, n ≤ K → checkList (V * K) σ (uses K x n) = some σ := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnK : n < K := hn
    simp only [uses]
    rw [checkList_append, ih (Nat.le_of_lt hnK)]
    simp [checkList, checkStmtV, varsOk, checkS, hyes n hnK]

theorem op_ok {K V : Nat} {σ σ' : SEnv} {o : Op} (h : checkOp K V σ o = some σ') :
    checkList (V * K) σ (expand K o) = some σ' := by
  cases o with
  | new x =>
    simp only [checkOp] at h
    split at h
    · rename_i hc
      obtain ⟨hx, hall⟩ := hc
      cases h
      exact allocs_ok hx (fun i hi => allIs_get K hall i hi) K (Nat.le_refl K)
    · contradiction
  | moveField x f y g =>
    simp only [checkOp] at h
    split at h
    · rename_i hc
      obtain ⟨_, hy, hf, hg, hne, h1, h2⟩ := hc
      cases h
      have hpq : pl K x f ≠ pl K y g := by
        intro heq
        obtain ⟨a, b⟩ := pl_inj hf hg heq
        cases hne with
        | inl h => exact h a
        | inr h => exact h b
      simp [expand, checkList, checkStmtV, varsOk, checkS, hpq, h1, h2, pl_lt hy hg]
    · contradiction
  | moveAll x y =>
    simp only [checkOp] at h
    split at h
    · rename_i hc
      obtain ⟨_, hy, hxy, h1, h2⟩ := hc
      cases h
      exact moves_ok hy hxy (fun i hi => allIs_get K h1 i hi) (fun i hi => allIs_get K h2 i hi)
        K (Nat.le_refl K)
    · contradiction
  | useField x f =>
    simp only [checkOp] at h
    split at h
    · rename_i hc
      obtain ⟨_, _, h1⟩ := hc
      cases h
      simp [expand, checkList, checkStmtV, varsOk, checkS, h1]
    · contradiction
  | useAll x =>
    simp only [checkOp] at h
    split at h
    · rename_i hc
      obtain ⟨_, h1⟩ := hc
      cases h
      exact uses_ok (fun i hi => allIs_get K h1 i hi) K (Nat.le_refl K)
    · contradiction
  | freeField x f =>
    simp only [checkOp] at h
    split at h
    · rename_i hc
      obtain ⟨_, _, h1⟩ := hc
      cases h
      simp [expand, checkList, checkStmtV, varsOk, checkS, h1]
    · contradiction

theorem ops_ok (K V : Nat) (os : List Op) :
    ∀ {σ σ' : SEnv}, checkOps K V σ os = some σ' → checkList (V * K) σ (expandOps K os) = some σ' := by
  induction os with
  | nil =>
    intro σ σ' h
    simp only [checkOps, Option.some.injEq] at h
    subst h
    rfl
  | cons o os ih =>
    intro σ σ' h
    simp only [checkOps] at h
    split at h
    · rename_i σ₁ h₁
      simp only [expandOps]
      rw [checkList_append, op_ok h₁]
      exact ih h
    · contradiction

/-- 本文件的检查器接受 ⇒ 展开后 M2b 的检查器接受，结束状态相同。 -/
theorem itemsAgree {K V : Nat} {its : List SItem} :
    ∀ {σ σ' : SEnv}, checkItems K V σ its = some σ' →
      M2b.checkItems (V * K) σ (lowerItems K its) = some σ' := by
  induction its with
  | nil =>
    intro σ σ' h
    simp only [checkItems, Option.some.injEq] at h
    subst h
    rfl
  | cons it its ih =>
    intro σ σ' h
    simp only [checkItems] at h
    split at h
    · rename_i σ₁ h₁
      cases it with
      | op o =>
        simp only [checkItem] at h₁
        simp only [lowerItems, lowerItem]
        rw [items_map_append, op_ok h₁]
        exact ih h
      | branch a b =>
        simp only [checkItem] at h₁
        split at h₁
        · rename_i σa σb ha hb
          cases h₁
          show M2b.checkItems (V * K) σ
            (M2b.Item.branch (expandOps K a) (expandOps K b) :: lowerItems K its) = some σ'
          simp only [M2b.checkItems, M2b.checkItem, ops_ok K V a ha, ops_ok K V b hb]
          exact ih h
        · contradiction
    · contradiction

/-! ## 主定理 -/

/-- **M13（一）主定理。** 按字段检查接受的程序（含部分移动），无论分支怎么走，
执行和作用域结束时按字段 drop flag 的释放都不出错，并且结束时堆是空的。 -/
theorem safety_and_no_leak (K V : Nat) (its : List SItem) (σ' : SEnv) (cs : List Bool)
    (h : checkItems K V (fun _ => .no) its = some σ') :
    ∃ s', (M2b.execItems M2b.St.empty cs (lowerItems K its)).bind
        (fun s => M2b.dropAll s (V * K)) = some s' ∧ ∀ l, s'.live l = false :=
  M2b.safety_and_no_leak (V * K) (lowerItems K its) σ' cs (itemsAgree h)

/-! ## 例子：两个字段（a = 0，b = 1），三个变量 -/

/-- `let p = P { a, b }`；`let q = p.a`（部分移动）；之后仍然可以用 `p.b`。 -/
def demo : List SItem := [.op (.new 0), .op (.moveField 0 0 1 0), .op (.useField 0 1)]

example : (checkItems 2 3 (fun _ => .no) demo).isSome = true := rfl

/-- 部分移动之后不能整体使用 `p`，也不能整体移动、不能再用 `p.a`。 -/
example : (checkItems 2 3 (fun _ => .no) (demo ++ [.op (.useAll 0)])).isNone = true := rfl
example : (checkItems 2 3 (fun _ => .no) (demo ++ [.op (.moveAll 0 2)])).isNone = true := rfl
example : (checkItems 2 3 (fun _ => .no) (demo ++ [.op (.useField 0 0)])).isNone = true := rfl

/-- 释放剩下的字段之后可以整体赋新值，然后又能整体使用。 -/
example : (checkItems 2 3 (fun _ => .no)
    (demo ++ [.op (.freeField 0 1), .op (.new 0), .op (.useAll 0)])).isSome = true := rfl

/-- 还有字段在时不能整体赋新值（会泄漏）。 -/
example : (checkItems 2 3 (fun _ => .no) (demo ++ [.op (.new 0)])).isNone = true := rfl

/-- 只在一个分支里移走 `p.a`：之后 `p.b` 照常可用，`p.a` 和整体都不能用；作用域结束时按 flag 释放。 -/
def demoBr : List SItem := [.op (.new 0), .branch [.moveField 0 0 1 0] [], .op (.useField 0 1)]

example : (checkItems 2 3 (fun _ => .no) demoBr).isSome = true := rfl
example : (checkItems 2 3 (fun _ => .no) (demoBr ++ [.op (.useAll 0)])).isNone = true := rfl
example : ((M2b.execItems M2b.St.empty [false, false, true] (lowerItems 2 demoBr)).bind
    (fun s => M2b.dropAll s 6)).isSome = true := rfl
example : ((M2b.execItems M2b.St.empty [false, false, false] (lowerItems 2 demoBr)).bind
    (fun s => M2b.dropAll s 6)).isSome = true := rfl

end Core.M13
