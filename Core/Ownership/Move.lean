import Core.Basic

/-!
# 所有权与移动（直线代码）

最小的核心演算。只有四种语句：

* `alloc x`：在堆上分配一个新值，交给 `x`
* `move x y`：`y := x`，所有权从 `x` 转到 `y`
* `use x`：读取 `x` 指向的值
* `free x`：释放 `x` 指向的值

**静态检查** `checkProg` 对应草案 II.1–II.2 的所有权规则。

**动态语义** `execProg` 故意做得“危险”：`move` 只拷贝指针，不清空 `x`，
和真实机器一样。所以如果检查器放过了“移动后再用”，
程序就可能读到已经被 `y` 释放的内存，执行返回 `none`。

**主定理** `safety`：检查器接受的程序，从空状态执行，一定不会返回 `none`，
也就是没有释放后使用、没有重复释放、没有通过已移走的变量访问内存。
-/

namespace Core.Ownership.Move

inductive Stmt where
  | alloc (x : Var)
  | move  (x y : Var)
  | use   (x : Var)
  | free  (x : Var)
  deriving Repr

/-! ## 静态检查 -/

/-- 静态环境：`σ x = true` 表示 `x` 当前拥有一个值。 -/
abbrev SEnv := Var → Bool

def checkStmt (σ : SEnv) : Stmt → Option SEnv
  | .alloc x  => if σ x = true then none else some (upd σ x true)
  | .move x y =>
      if x = y then none
      else if σ x = true then
        (if σ y = true then none else some (upd (upd σ x false) y true))
      else none
  | .use x    => if σ x = true then some σ else none
  | .free x   => if σ x = true then some (upd σ x false) else none

def checkProg (σ : SEnv) : List Stmt → Option SEnv
  | []      => some σ
  | t :: ts =>
    match checkStmt σ t with
    | some σ' => checkProg σ' ts
    | none    => none

/-! ## 动态语义 -/

structure St where
  env  : Var → Option Loc   -- 变量里存的指针（移动后旧变量仍然留着旧指针）
  live : Loc → Bool         -- 堆上哪些位置还没被释放
  next : Loc                -- 下一个可分配的位置

def execStmt (s : St) : Stmt → Option St
  | .alloc x =>
      some { env := upd s.env x (some s.next), live := upd s.live s.next true, next := s.next + 1 }
  | .move x y =>
      match s.env x with
      | some l => if s.live l = true then some { s with env := upd s.env y (some l) } else none
      | none   => none
  | .use x =>
      match s.env x with
      | some l => if s.live l = true then some s else none
      | none   => none
  | .free x =>
      match s.env x with
      | some l => if s.live l = true then some { s with live := upd s.live l false } else none
      | none   => none

def execProg (s : St) : List Stmt → Option St
  | []      => some s
  | t :: ts =>
    match execStmt s t with
    | some s' => execProg s' ts
    | none    => none

def St.empty : St := { env := fun _ => none, live := fun _ => false, next := 0 }

/-! ## 不变式：静态环境如何约束动态状态 -/

structure Inv (σ : SEnv) (s : St) : Prop where
  /-- 拥有值的变量，指向一个还活着的位置。 -/
  owned_live : ∀ x, σ x = true → ∃ l, s.env x = some l ∧ s.live l = true
  /-- 拥有者唯一：两个拥有值的变量不会指向同一位置。 -/
  unique : ∀ x y l, σ x = true → σ y = true → s.env x = some l → s.env y = some l → x = y
  /-- 所有指针都指向已经分配过的位置。 -/
  bounded : ∀ x l, s.env x = some l → l < s.next

theorem inv_empty : Inv (fun _ => false) St.empty :=
  { owned_live := by intro x h; simp at h
    unique := by intro x y l hx; simp at hx
    bounded := by intro x l h; simp [St.empty] at h }

/-! ## 每种语句保持不变式 -/

theorem sound_alloc {σ : SEnv} {s : St} {x : Var} (hi : Inv σ s) :
    Inv (upd σ x true)
      { env := upd s.env x (some s.next), live := upd s.live s.next true, next := s.next + 1 } := by
  constructor
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      exact ⟨s.next, by simp [upd], by simp [upd]⟩
    · simp [upd, hzx] at hz
      obtain ⟨l, hl, hlive⟩ := hi.owned_live z hz
      have hne : l ≠ s.next := Nat.ne_of_lt (hi.bounded z l hl)
      exact ⟨l, by simp [upd, hzx, hl], by simp [upd, hne, hlive]⟩
  · intro a b l ha hb hea heb
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · exfalso
      simp [upd, hax] at hea
      simp [upd, hbx] at heb
      subst hea
      exact Nat.lt_irrefl _ (hi.bounded b _ heb)
    · exfalso
      simp [upd, hax] at hea
      simp [upd, hbx] at heb
      subst heb
      exact Nat.lt_irrefl _ (hi.bounded a _ hea)
    · simp [upd, hax] at ha hea
      simp [upd, hbx] at hb heb
      exact hi.unique a b l ha hb hea heb
  · intro z l hz
    show l < s.next + 1
    by_cases hzx : z = x
    · simp [upd, hzx] at hz
      subst hz
      exact Nat.lt_succ_self _
    · simp [upd, hzx] at hz
      exact Nat.lt_succ_of_lt (hi.bounded z l hz)

theorem sound_move {σ : SEnv} {s : St} {x y : Var} {l : Loc}
    (hxy : x ≠ y) (hx : σ x = true)
    (hl : s.env x = some l) (hlive : s.live l = true) (hi : Inv σ s) :
    Inv (upd (upd σ x false) y true) { s with env := upd s.env y (some l) } := by
  -- 移动之后，除了 y，仍然拥有值的变量一定不是 x
  have own : ∀ z, z ≠ y → upd (upd σ x false) y true z = true → z ≠ x ∧ σ z = true := by
    intro z hzy hz
    by_cases hzx : z = x
    · subst hzx
      simp [upd, hxy] at hz
    · simp [upd, hzy, hzx] at hz
      exact ⟨hzx, hz⟩
  constructor
  · intro z hz
    by_cases hzy : z = y
    · subst hzy
      exact ⟨l, by simp [upd], hlive⟩
    · obtain ⟨_, hz'⟩ := own z hzy hz
      obtain ⟨m, hm, hmlive⟩ := hi.owned_live z hz'
      exact ⟨m, by simp [upd, hzy, hm], hmlive⟩
  · intro a b m ha hb hea heb
    by_cases hay : a = y <;> by_cases hby : b = y
    · rw [hay, hby]
    · exfalso
      obtain ⟨hbx, hb'⟩ := own b hby hb
      simp [upd, hay] at hea
      simp [upd, hby] at heb
      rw [← hea] at heb
      exact hbx (hi.unique x b l hx hb' hl heb).symm
    · exfalso
      obtain ⟨hax, ha'⟩ := own a hay ha
      simp [upd, hay] at hea
      simp [upd, hby] at heb
      rw [← heb] at hea
      exact hax (hi.unique x a l hx ha' hl hea).symm
    · obtain ⟨_, ha'⟩ := own a hay ha
      obtain ⟨_, hb'⟩ := own b hby hb
      simp [upd, hay] at hea
      simp [upd, hby] at heb
      exact hi.unique a b m ha' hb' hea heb
  · intro z m hz
    show m < s.next
    by_cases hzy : z = y
    · simp [upd, hzy] at hz
      rw [← hz]
      exact hi.bounded x l hl
    · simp [upd, hzy] at hz
      exact hi.bounded z m hz

theorem sound_free {σ : SEnv} {s : St} {x : Var} {l : Loc}
    (hx : σ x = true) (hl : s.env x = some l) (hi : Inv σ s) :
    Inv (upd σ x false) { s with live := upd s.live l false } := by
  constructor
  · intro z hz
    by_cases hzx : z = x
    · simp [upd, hzx] at hz
    · simp [upd, hzx] at hz
      obtain ⟨m, hm, hmlive⟩ := hi.owned_live z hz
      -- z 指向的位置不是刚释放的 l，否则 z 和 x 会共享同一个值
      have hml : m ≠ l := by
        intro h
        rw [h] at hm
        exact hzx (hi.unique z x l hz hx hm hl)
      exact ⟨m, hm, by simp [upd, hml, hmlive]⟩
  · intro a b m ha hb hea heb
    by_cases hax : a = x
    · simp [upd, hax] at ha
    · by_cases hbx : b = x
      · simp [upd, hbx] at hb
      · simp [upd, hax] at ha
        simp [upd, hbx] at hb
        exact hi.unique a b m ha hb hea heb
  · intro z m hz
    exact hi.bounded z m hz

/-! ## 主定理 -/

theorem checkStmt_sound {σ σ' : SEnv} {s : St} {t : Stmt}
    (hc : checkStmt σ t = some σ') (hi : Inv σ s) :
    ∃ s', execStmt s t = some s' ∧ Inv σ' s' := by
  cases t with
  | alloc x =>
    simp only [checkStmt] at hc
    split at hc
    · contradiction
    · cases hc
      exact ⟨_, rfl, sound_alloc hi⟩
  | move x y =>
    simp only [checkStmt] at hc
    split at hc
    · contradiction
    · rename_i hxy
      split at hc
      · rename_i hx
        split at hc
        · contradiction
        · cases hc
          obtain ⟨l, hl, hlive⟩ := hi.owned_live x hx
          refine ⟨{ s with env := upd s.env y (some l) }, ?_, sound_move hxy hx hl hlive hi⟩
          simp [execStmt, hl, hlive]
      · contradiction
  | use x =>
    simp only [checkStmt] at hc
    split at hc
    · rename_i hx
      cases hc
      obtain ⟨l, hl, hlive⟩ := hi.owned_live x hx
      exact ⟨s, by simp [execStmt, hl, hlive], hi⟩
    · contradiction
  | free x =>
    simp only [checkStmt] at hc
    split at hc
    · rename_i hx
      cases hc
      obtain ⟨l, hl, hlive⟩ := hi.owned_live x hx
      refine ⟨{ s with live := upd s.live l false }, ?_, sound_free hx hl hi⟩
      simp [execStmt, hl, hlive]
    · contradiction

theorem checkProg_sound (ts : List Stmt) :
    ∀ {σ σ' : SEnv} {s : St}, checkProg σ ts = some σ' → Inv σ s →
      ∃ s', execProg s ts = some s' ∧ Inv σ' s' := by
  induction ts with
  | nil =>
    intro σ σ' s hc hi
    simp [checkProg] at hc
    subst hc
    exact ⟨s, by simp [execProg], hi⟩
  | cons t ts ih =>
    intro σ σ' s hc hi
    simp only [checkProg] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, he₁, hi₁⟩ := checkStmt_sound h₁ hi
      obtain ⟨s₂, he₂, hi₂⟩ := ih hc hi₁
      exact ⟨s₂, by simp [execProg, he₁, he₂], hi₂⟩
    · contradiction

/-- **`Ownership.Move` 主定理。** 检查器接受的程序，从空状态执行不会出错：
没有释放后使用、没有重复释放、没有通过已移走的变量访问已释放的内存。 -/
theorem safety (ts : List Stmt) (σ' : SEnv)
    (h : checkProg (fun _ => false) ts = some σ') :
    ∃ s', execProg St.empty ts = some s' := by
  obtain ⟨s', he, _⟩ := checkProg_sound ts h inv_empty
  exact ⟨s', he⟩

/-! ## 例子 -/

/-- 正常的移动：检查器接受。 -/
example : (checkProg (fun _ => false) [.alloc 0, .move 0 1, .use 1, .free 1]).isSome = true := rfl

/-- 移动之后再用旧变量：检查器拒绝。 -/
example : (checkProg (fun _ => false) [.alloc 0, .move 0 1, .use 0]).isNone = true := rfl

/-- 重复释放：检查器拒绝。 -/
example : (checkProg (fun _ => false) [.alloc 0, .free 0, .free 0]).isNone = true := rfl

/-- 检查器为什么必要：同样的“移动后释放再使用”，动态执行真的会出错。 -/
example : (execProg St.empty [.alloc 0, .move 0 1, .free 1, .use 0]).isNone = true := rfl

end Core.Ownership.Move
