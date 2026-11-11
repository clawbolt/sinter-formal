import Core.Ownership.Move

/-!
# 作用域结束时自动释放，没有泄漏

在 `Ownership.Move` 的基础上：

* 作用域里的变量编号都小于 `N`，检查器会检查这一点（`varsOk`）；
* 作用域结束时，编译器按编号插入 `free`，释放所有仍然拥有值的变量（`epi`）。

**主定理** `no_leak`：检查器接受的程序，加上编译器插入的释放语句后执行，
不会出错，而且结束时堆上没有任何还活着的值。

证明复用 `Ownership.Move` 的 `Inv` 和 `checkStmt_sound`，只额外证明一条新不变式 `Inv2`：
每个活着的堆位置都有一个拥有者。
-/

namespace Core.Ownership.Drop
open Core.Ownership.Move

/-- 会产生新拥有者的语句，其目标变量必须是作用域里的变量。 -/
def varsOk (N : Nat) : Stmt → Bool
  | .alloc x  => decide (x < N)
  | .move _ y => decide (y < N)
  | .use _    => true
  | .free _   => true

def checkStmtN (N : Nat) (σ : SEnv) (t : Stmt) : Option SEnv :=
  if varsOk N t = true then checkStmt σ t else none

def checkProgN (N : Nat) (σ : SEnv) : List Stmt → Option SEnv
  | []      => some σ
  | t :: ts =>
    match checkStmtN N σ t with
    | some σ' => checkProgN N σ' ts
    | none    => none

/-! ## 新不变式 -/

structure Inv2 (N : Nat) (σ : SEnv) (s : St) : Prop where
  /-- 每个活着的位置都有一个拥有者。 -/
  live_owned : ∀ l, s.live l = true → ∃ x, σ x = true ∧ s.env x = some l
  /-- 拥有值的变量都在作用域里。 -/
  bound : ∀ x, σ x = true → x < N

theorem inv2_empty (N : Nat) : Inv2 N (fun _ => false) St.empty :=
  { live_owned := by intro l h; simp [St.empty] at h
    bound := by intro x h; simp at h }

theorem inv2_step {N : Nat} {σ σ' : SEnv} {s s' : St} {t : Stmt}
    (hv : varsOk N t = true) (hc : checkStmt σ t = some σ')
    (he : execStmt s t = some s') (h2 : Inv2 N σ s) :
    Inv2 N σ' s' := by
  cases t with
  | alloc x =>
    simp only [checkStmt] at hc
    split at hc
    · contradiction
    · rename_i hx
      cases hc
      simp only [execStmt] at he
      cases he
      simp only [varsOk, decide_eq_true_eq] at hv
      have hxf : σ x = false := by simpa using hx
      constructor
      · intro l hl
        by_cases hln : l = s.next
        · exact ⟨x, by simp [upd], by simp [upd, hln]⟩
        · simp [upd, hln] at hl
          obtain ⟨y, hy, hey⟩ := h2.live_owned l hl
          have hyx : y ≠ x := by
            intro h; rw [h] at hy; rw [hy] at hxf; contradiction
          exact ⟨y, by simp [upd, hyx, hy], by simp [upd, hyx, hey]⟩
      · intro z hz
        by_cases hzx : z = x
        · rw [hzx]; exact hv
        · simp [upd, hzx] at hz
          exact h2.bound z hz
  | move x y =>
    simp only [checkStmt] at hc
    split at hc
    · contradiction
    · rename_i hxy
      split at hc
      · split at hc
        · contradiction
        · rename_i hy
          cases hc
          simp only [varsOk, decide_eq_true_eq] at hv
          have hyf : σ y = false := by simpa using hy
          simp only [execStmt] at he
          split at he
          · rename_i l hl
            split at he
            · cases he
              constructor
              · intro m hm
                obtain ⟨z, hz, hez⟩ := h2.live_owned m hm
                by_cases hzx : z = x
                · -- 原来的拥有者是 x，现在变成 y
                  rw [hzx, hl] at hez
                  simp at hez
                  exact ⟨y, by simp [upd], by simp [upd, hez]⟩
                · have hzy : z ≠ y := by
                    intro h; rw [h] at hz; rw [hz] at hyf; contradiction
                  exact ⟨z, by simp [upd, hzx, hzy, hz], by simp [upd, hzy, hez]⟩
              · intro z hz
                by_cases hzy : z = y
                · rw [hzy]; exact hv
                · by_cases hzx : z = x
                  · rw [hzx] at hz; simp [upd, hxy] at hz
                  · simp [upd, hzy, hzx] at hz
                    exact h2.bound z hz
            · contradiction
          · contradiction
      · contradiction
  | use x =>
    simp only [checkStmt] at hc
    split at hc
    · cases hc
      simp only [execStmt] at he
      split at he
      · split at he
        · cases he; exact h2
        · contradiction
      · contradiction
    · contradiction
  | free x =>
    simp only [checkStmt] at hc
    split at hc
    · cases hc
      simp only [execStmt] at he
      split at he
      · rename_i l hl
        split at he
        · cases he
          constructor
          · intro m hm
            have hml : m ≠ l := by
              intro h; rw [h] at hm; simp [upd] at hm
            simp [upd, hml] at hm
            obtain ⟨z, hz, hez⟩ := h2.live_owned m hm
            -- 拥有者不是 x，否则 m 就是刚释放的 l
            have hzx : z ≠ x := by
              intro h; rw [h, hl] at hez; simp at hez; exact hml hez.symm
            exact ⟨z, by simp [upd, hzx, hz], hez⟩
          · intro z hz
            by_cases hzx : z = x
            · rw [hzx] at hz; simp [upd] at hz
            · simp [upd, hzx] at hz
              exact h2.bound z hz
        · contradiction
      · contradiction
    · contradiction

theorem checkProgN_sound (N : Nat) (ts : List Stmt) :
    ∀ {σ σ' : SEnv} {s : St}, checkProgN N σ ts = some σ' → Inv σ s → Inv2 N σ s →
      ∃ s', execProg s ts = some s' ∧ Inv σ' s' ∧ Inv2 N σ' s' := by
  induction ts with
  | nil =>
    intro σ σ' s hc hi h2
    simp [checkProgN] at hc
    subst hc
    exact ⟨s, by simp [execProg], hi, h2⟩
  | cons t ts ih =>
    intro σ σ' s hc hi h2
    simp only [checkProgN] at hc
    split at hc
    · rename_i σ₁ h₁
      simp only [checkStmtN] at h₁
      split at h₁
      · rename_i hv
        obtain ⟨s₁, he₁, hi₁⟩ := checkStmt_sound h₁ hi
        have h2₁ := inv2_step hv h₁ he₁ h2
        obtain ⟨s₂, he₂, hi₂, h2₂⟩ := ih hc hi₁ h2₁
        exact ⟨s₂, by simp [execProg, he₁, he₂], hi₂, h2₂⟩
      · contradiction
    · contradiction

theorem checkProgN_append (N : Nat) (a b : List Stmt) : ∀ (σ : SEnv),
    checkProgN N σ (a ++ b) = (checkProgN N σ a).bind (fun σ₁ => checkProgN N σ₁ b) := by
  induction a with
  | nil => intro σ; simp [checkProgN]
  | cons t ts ih =>
    intro σ
    simp only [List.cons_append, checkProgN]
    cases checkStmtN N σ t <;> simp [ih]

/-! ## 作用域结束时插入的释放语句 -/

/-- 按编号 `0, 1, …, n-1` 释放所有仍然拥有值的变量。 -/
def epi (σ : SEnv) : Nat → List Stmt
  | 0     => []
  | n + 1 => epi σ n ++ (if σ n = true then [.free n] else [])

/-- 前 `n` 个变量处理完之后的静态环境。 -/
def clear (σ : SEnv) : Nat → SEnv
  | 0     => σ
  | n + 1 => upd (clear σ n) n false

theorem clear_ge (σ : SEnv) : ∀ n x, n ≤ x → clear σ n x = σ x := by
  intro n
  induction n with
  | zero => intro x _; simp [clear]
  | succ n ih =>
    intro x hle
    have hlt : n < x := hle
    have hxn : x ≠ n := by
      intro h; rw [h] at hlt; exact Nat.lt_irrefl n hlt
    simp only [clear, upd, ite_eq_right hxn]
    exact ih x (Nat.le_of_lt hlt)

theorem clear_lt (σ : SEnv) : ∀ n x, x < n → clear σ n x = false := by
  intro n
  induction n with
  | zero => intro x h; exact absurd h (Nat.not_lt_zero x)
  | succ n ih =>
    intro x hlt
    by_cases hxn : x = n
    · simp only [clear, upd, ite_eq_left hxn]
    · simp only [clear, upd, ite_eq_right hxn]
      exact ih x (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hxn)

theorem check_epi (N : Nat) (σ : SEnv) : ∀ n, checkProgN N σ (epi σ n) = some (clear σ n) := by
  intro n
  induction n with
  | zero => simp [epi, checkProgN, clear]
  | succ n ih =>
    simp only [epi, clear]
    rw [checkProgN_append, ih]
    by_cases hn : σ n = true
    · have hcn : clear σ n n = true := by
        rw [clear_ge σ n n (Nat.le_refl n)]; exact hn
      simp [hn, checkProgN, checkStmtN, varsOk, checkStmt, hcn]
    · have hcn : clear σ n n = false := by
        rw [clear_ge σ n n (Nat.le_refl n)]; simpa using hn
      have hfix : upd (clear σ n) n false = clear σ n := by
        funext x
        by_cases hx : x = n
        · subst hx; simp [upd, hcn]
        · simp [upd, hx]
      simp [hn, checkProgN, hfix]

/-! ## 主定理 -/

/-- **`Ownership.Drop` 主定理。** 检查器接受的程序，加上作用域结束时插入的释放语句，
执行不会出错，并且结束时堆上没有任何还活着的值。 -/
theorem no_leak (N : Nat) (ts : List Stmt) (σ' : SEnv)
    (h : checkProgN N (fun _ => false) ts = some σ') :
    ∃ s', execProg St.empty (ts ++ epi σ' N) = some s' ∧ ∀ l, s'.live l = false := by
  have hall : checkProgN N (fun _ => false) (ts ++ epi σ' N) = some (clear σ' N) := by
    rw [checkProgN_append, h]
    simpa using check_epi N σ' N
  obtain ⟨s', he, _, h2⟩ := checkProgN_sound N _ hall inv_empty (inv2_empty N)
  refine ⟨s', he, ?_⟩
  intro l
  cases hl : s'.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := h2.live_owned l hl
    have hxN := h2.bound x hx
    rw [clear_lt σ' N x hxN] at hx
    contradiction

/-! ## 例子 -/

/-- 分配之后忘了释放：插入的释放语句会处理掉它。 -/
example : (execProg St.empty ([.alloc 0] ++ epi (upd (fun _ => false) 0 true) 1)).isSome = true := rfl

end Core.Ownership.Drop
