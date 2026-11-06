import Core.M2b

/-!
# M2b（下·一）：任意嵌套的分支

把程序写成一棵二叉树：

* `skip`：什么都不做
* `stmt t`：一条普通语句
* `seq p q`：先 `p` 后 `q`
* `branch p q`：按运行时条件走 `p` 或 `q`，两边都可以继续嵌套

`Prog` 是普通的归纳类型（子节点直接是 `Prog`，不是 `List Prog`），
所以可以直接用结构递归和 `induction`，不需要处理嵌套归纳类型。

动态侧的引理（`DInv`、`Compat`、`stepS`、合并引理、`dropAll`）全部复用 M2b（上），
这里只重写最外层的递归。

**主定理** `safety_and_no_leak`：检查器接受的程序，无论每个分支怎么走，
执行和作用域结束时按 drop flag 的释放都不会出错，并且结束时堆上没有活着的值。
-/

namespace Core.M2n
open Core.M1 (Stmt)
open Core.M2b

inductive Prog
  | skip
  | stmt   (t : Stmt)
  | seq    (p q : Prog)
  | branch (p q : Prog)

def check (N : Nat) : Prog → SEnv → Option SEnv
  | .skip,       σ => some σ
  | .stmt t,     σ => checkStmtV N σ t
  | .seq p q,    σ =>
    match check N p σ with
    | some σ₁ => check N q σ₁
    | none    => none
  | .branch p q, σ =>
    match check N p σ, check N q σ with
    | some σa, some σb => some (join σa σb)
    | _, _             => none

/-- 执行；`cs` 依次给出每个分支的选择，返回执行后的状态和剩下的选择。 -/
def exec : Prog → St → List Bool → Option (St × List Bool)
  | .skip,       s, cs => some (s, cs)
  | .stmt t,     s, cs =>
    match execS s t with
    | some s' => some (s', cs)
    | none    => none
  | .seq p q,    s, cs =>
    match exec p s cs with
    | some (s₁, cs₁) => exec q s₁ cs₁
    | none           => none
  | .branch p q, s, cs =>
    if cs.headD false = true then exec p s cs.tail else exec q s cs.tail

theorem sound (N : Nat) (p : Prog) :
    ∀ {σ σ' : SEnv} {s : St} (cs : List Bool),
      check N p σ = some σ' → Compat σ s.flag → DInv N s →
      ∃ s' cs', exec p s cs = some (s', cs') ∧ Compat σ' s'.flag ∧ DInv N s' := by
  induction p with
  | skip =>
    intro σ σ' s cs hc hc0 hd
    simp [check] at hc
    subst hc
    exact ⟨s, cs, by simp [exec], hc0, hd⟩
  | stmt t =>
    intro σ σ' s cs hc hc0 hd
    simp only [check, checkStmtV] at hc
    split at hc
    · rename_i hv
      obtain ⟨s', he, hc', hd'⟩ := stepS hv hc hc0 hd
      exact ⟨s', cs, by simp only [exec, he], hc', hd'⟩
    · contradiction
  | seq p q ihp ihq =>
    intro σ σ' s cs hc hc0 hd
    simp only [check] at hc
    split at hc
    · rename_i σ₁ h₁
      obtain ⟨s₁, cs₁, he₁, hc₁, hd₁⟩ := ihp cs h₁ hc0 hd
      obtain ⟨s₂, cs₂, he₂, hc₂, hd₂⟩ := ihq cs₁ hc hc₁ hd₁
      exact ⟨s₂, cs₂, by simp only [exec, he₁, he₂], hc₂, hd₂⟩
    · contradiction
  | branch p q ihp ihq =>
    intro σ σ' s cs hc hc0 hd
    simp only [check] at hc
    split at hc
    · rename_i σa σb ha hb
      cases hc
      by_cases hcs : cs.headD false = true
      · obtain ⟨s', cs', he, hc', hd'⟩ := ihp cs.tail ha hc0 hd
        refine ⟨s', cs', ?_, compat_join_left hc', hd'⟩
        simp only [exec]
        split
        · exact he
        · contradiction
      · obtain ⟨s', cs', he, hc', hd'⟩ := ihq cs.tail hb hc0 hd
        refine ⟨s', cs', ?_, compat_join_right hc', hd'⟩
        simp only [exec]
        split
        · contradiction
        · exact he
    · contradiction

/-- **M2b（下·一）主定理。** 检查器接受的程序，无论每个分支怎么走，
执行和作用域结束时按 drop flag 的释放都不会出错，并且结束时堆上没有活着的值。 -/
theorem safety_and_no_leak (N : Nat) (p : Prog) (σ' : SEnv) (cs : List Bool)
    (h : check N p (fun _ => .no) = some σ') :
    ∃ s', (exec p St.empty cs).bind (fun r => dropAll r.1 N) = some s' ∧
      ∀ l, s'.live l = false := by
  obtain ⟨s₁, cs₁, he₁, _, hd₁⟩ := sound N p cs h compat_empty (dinv_empty N)
  obtain ⟨s₂, he₂, hd₂, hf₂⟩ := dropAll_sound hd₁ N
  refine ⟨s₂, by rw [he₁]; exact he₂, ?_⟩
  intro l
  cases hl : s₂.live l with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨x, hx, _⟩ := hd₂.live_owned l hl
    have hxN := hd₂.bound x hx
    rw [hf₂ x hxN] at hx
    contradiction

/-! ## 例子 -/

/-- 两层嵌套：内层分支可能把 0 移给 1，外层另一边只读 0。 -/
def demo : Prog :=
  .seq (.stmt (.alloc 0))
    (.branch (.branch (.stmt (.move 0 1)) .skip) (.stmt (.use 0)))

/-- 检查器接受。 -/
example : (check 2 demo (fun _ => .no)).isSome = true := rfl

/-- 之后 0 是“可能已移走”，再使用就被拒绝。 -/
example : (check 2 (.seq demo (.stmt (.use 0))) (fun _ => .no)).isNone = true := rfl

/-- 三条不同的执行路径，结束时按 drop flag 释放，都不出错。 -/
example : ((exec demo St.empty [true, true]).bind (fun r => dropAll r.1 2)).isSome = true := rfl
example : ((exec demo St.empty [true, false]).bind (fun r => dropAll r.1 2)).isSome = true := rfl
example : ((exec demo St.empty [false]).bind (fun r => dropAll r.1 2)).isSome = true := rfl

end Core.M2n
