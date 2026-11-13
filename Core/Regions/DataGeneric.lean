import Core.Regions.Data
import Core.Regions.Generic

/-!
# 含引用的数据类型与区域参数的实例化

**问题**：迭代器这样的值里存着借用（`MapIter<&Map<K, V> in m>`），它的方法的签名里写着区域参数：
`fn next(inout it: MapIter<&Map<K, V> in r>) -> Option<&V in r>`。函数体在定义处把 `r` 当作抽象区域检查一次，
之后对每个调用处的实际区域实例化。`Regions.Generic` 对 `Regions.Model`（每个变量至多指向一个区域）证明了实例化，
`Regions.Data`（一个值里有一组指针，类型里可能有好几个区域）没有重新做这个模拟。这里补上。

**做法**：和 `Regions.Generic` 相同：`m` 个区域参数是抽象深度 `0 … m-1`，函数体从深度 `m` 开始；
调用处给出实际区域 `θ`，程序里的区域编号按 `ren` 换掉（`ralloc` 的区域、`empty` 的区域列表）。
参数 `x` 住在区域参数 `β x` 里，值的类型里的区域是 `κ x`（例如迭代器参数的类型里有 `r`）。

**条件**：同 `Regions.Generic`：`θ` 保持 outlives 顺序（`Mono`），实际区域都在调用者的深度之下（`Below`）。

**主定理**：
- `instance_accepted`：定义处接受 ⇒ 实例在调用处接受；
- `instance_safe`：再加上调用处的运行状态满足 `Regions.Data` 的不变式，实例执行不出错（每次读取时值里的每个区域都活着）。

模拟关系 `Rel` 把 `Regions.Generic` 的“至多一个区域”换成区域列表：两边的列表按 `ren` 逐个对应。
新的引理是 `regs_map`（几个变量的区域拼起来，换名和拼接可交换）和 `below_map`（抽象上能存的列表，换名后实际上也能存）。

**例子**：迭代器的 `next`：从迭代器参数（类型里有 `r`）复制出借用，交给住在 `r` 里的结果：定义处接受，实例接受；
把函数体里本地块的引用装进结果：定义处拒绝。
-/

namespace Core.Regions.DataGeneric
open Core.Regions.Data (Cmd P REnv below regs check1 check restrict exec Good sound St below_ok)
open Core.Regions.Generic (ren Mono Below ren_lt)

/-! ## 实例化：区域换名 -/

def renC (m d0 : Nat) (θ : Nat → Nat) : Cmd → Cmd
  | .decl x     => .decl x
  | .ralloc x k => .ralloc x (ren m d0 θ k)
  | .pack x ys  => .pack x ys
  | .empty x ks => .empty x (ks.map (ren m d0 θ))
  | .copy x y   => .copy x y
  | .read x     => .read x

def renP (m d0 : Nat) (θ : Nat → Nat) : P → P
  | .skip    => .skip
  | .cmd c   => .cmd (renC m d0 θ c)
  | .seq p q => .seq (renP m d0 θ p) (renP m d0 θ q)
  | .block p => .block (renP m d0 θ p)

/-! ## 模拟关系 -/

/-- 变量 `x` 在两边的静态信息对应：作用域深度对应，类型里的区域列表按 `ren` 逐个对应。 -/
def Rel (m d0 : Nat) (θ : Nat → Nat) (σa σc : REnv) (x : Nat) : Prop :=
  (σa x = none ∧ σc x = none) ∨
  ∃ dx ks dx', σa x = some (dx, ks) ∧ σc x = some (dx', ks.map (ren m d0 θ)) ∧
    (∀ k, k < dx → ren m d0 θ k < dx') ∧
    ((dx ≤ m ∧ dx' ≤ d0) ∨ (m ≤ dx ∧ dx' = dx - m + d0))

structure Inv (m d0 : Nat) (θ : Nat → Nat) (d d' : Nat) (σa σc : REnv) : Prop where
  hm  : m ≤ d
  hd  : d' = d - m + d0
  rel : ∀ x, Rel m d0 θ σa σc x

section
variable {m d0 : Nat} {θ : Nat → Nat}

theorem rel_upd {σa σc : REnv} {x : Nat} {a c : Option (Nat × List Nat)}
    (h : ∀ z, Rel m d0 θ σa σc z) (hx : Rel m d0 θ (upd σa x a) (upd σc x c) x) :
    ∀ z, Rel m d0 θ (upd σa x a) (upd σc x c) z := by
  intro z
  by_cases hz : z = x
  · rw [hz]; exact hx
  · have e1 : upd σa x a z = σa z := upd_other _ _ hz
    have e2 : upd σc x c z = σc z := upd_other _ _ hz
    unfold Rel
    rw [e1, e2]
    exact h z

/-- 抽象上能存的区域列表，换名后实际上也能存。 -/
theorem below_map {dx dx' : Nat} (hP : ∀ k, k < dx → ren m d0 θ k < dx') :
    ∀ {ks : List Nat}, below dx ks = true → below dx' (ks.map (ren m d0 θ)) = true := by
  intro ks
  induction ks with
  | nil => intro _; rfl
  | cons k ks ih =>
    intro h
    simp only [below, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.map_cons, below, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hP k h.1, ih h.2⟩

/-- 几个变量的区域拼起来：换名和拼接可交换。 -/
theorem regs_map {σa σc : REnv} (hrel : ∀ z, Rel m d0 θ σa σc z) :
    ∀ {ys : List Nat} {ks : List Nat}, regs σa ys = some ks → regs σc ys = some (ks.map (ren m d0 θ)) := by
  intro ys
  induction ys with
  | nil =>
    intro ks h
    simp only [regs, Option.some.injEq] at h
    subst h
    rfl
  | cons y ys ih =>
    intro ks h
    simp only [regs] at h
    split at h
    · rename_i dy ky rs hy hr
      cases h
      rcases hrel y with ⟨ha, _⟩ | ⟨dx, kk, dx', ha, hc, _, _⟩
      · rw [hy] at ha; cases ha
      · rw [hy] at ha
        simp only [Option.some.injEq, Prod.mk.injEq] at ha
        obtain ⟨rfl, rfl⟩ := ha
        simp [regs, hc, ih hr, List.map_append]
    · contradiction

/-- 一条命令：抽象上接受 ⇒ 换名后接受，关系保持。 -/
theorem step (hb : Below m d0 θ) {d d' : Nat} {σa σa' σc : REnv} {c : Cmd}
    (hI : Inv m d0 θ d d' σa σc) (h : check1 d σa c = some σa') :
    ∃ σc', check1 d' σc (renC m d0 θ c) = some σc' ∧ Inv m d0 θ d d' σa' σc' := by
  cases c with
  | decl x =>
    simp only [check1] at h
    split at h
    · rename_i hx
      cases h
      have hcx : σc x = none := by
        rcases hI.rel x with ⟨_, hc⟩ | ⟨_, _, _, ha, _, _, _⟩
        · exact hc
        · rw [hx] at ha; cases ha
      refine ⟨upd σc x (some (d', [])), by simp [renC, check1, hcx], ⟨hI.hm, hI.hd, ?_⟩⟩
      apply rel_upd hI.rel
      refine Or.inr ⟨d, [], d', by simp, by simp, ?_, Or.inr ⟨hI.hm, hI.hd⟩⟩
      intro k hk
      rw [hI.hd]
      exact ren_lt hb hI.hm hk
    · contradiction
  | ralloc x k =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨dx, kx, dx', ha, hc, hP, hcat⟩
    · simp [check1, ha] at h
    · simp only [check1, ha] at h
      by_cases hk : k < dx
      · simp only [hk, ↓reduceIte] at h
        cases h
        refine ⟨upd σc x (some (dx', [ren m d0 θ k])),
          by simp [renC, check1, hc, hP k hk], ⟨hI.hm, hI.hd, ?_⟩⟩
        apply rel_upd hI.rel
        exact Or.inr ⟨dx, [k], dx', by simp, by simp, hP, hcat⟩
      · simp [hk] at h
  | pack x ys =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨dx, kx, dx', ha, hc, hP, hcat⟩
    · simp [check1, ha] at h
    · cases hr : regs σa ys with
      | none => simp [check1, ha, hr] at h
      | some ks =>
        simp only [check1, ha, hr] at h
        by_cases hbl : below dx ks = true
        · simp only [hbl, ↓reduceIte] at h
          cases h
          have hr' := regs_map hI.rel hr
          have hb' := below_map hP hbl
          refine ⟨upd σc x (some (dx', ks.map (ren m d0 θ))),
            by simp [renC, check1, hc, hr', hb'], ⟨hI.hm, hI.hd, ?_⟩⟩
          apply rel_upd hI.rel
          exact Or.inr ⟨dx, ks, dx', by simp, by simp, hP, hcat⟩
        · simp [hbl] at h
  | empty x ks =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨dx, kx, dx', ha, hc, hP, hcat⟩
    · simp [check1, ha] at h
    · simp only [check1, ha] at h
      by_cases hbl : below dx ks = true
      · simp only [hbl, ↓reduceIte] at h
        cases h
        have hb' := below_map hP hbl
        refine ⟨upd σc x (some (dx', ks.map (ren m d0 θ))),
          by simp [renC, check1, hc, hb'], ⟨hI.hm, hI.hd, ?_⟩⟩
        apply rel_upd hI.rel
        exact Or.inr ⟨dx, ks, dx', by simp, by simp, hP, hcat⟩
      · simp [hbl] at h
  | copy x y =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨dx, kx, dx', ha, hc, _, _⟩
    · simp [check1, ha] at h
    · rcases hI.rel y with ⟨hay, _⟩ | ⟨dy, ky, dy', hay, hcy, hPy, hcaty⟩
      · simp [check1, ha, hay] at h
      · simp only [check1, ha, hay] at h
        by_cases hbl : below dy kx = true
        · simp only [hbl, ↓reduceIte] at h
          cases h
          have hb' := below_map hPy hbl
          refine ⟨upd σc y (some (dy', kx.map (ren m d0 θ))),
            by simp [renC, check1, hc, hcy, hb'], ⟨hI.hm, hI.hd, ?_⟩⟩
          apply rel_upd hI.rel
          exact Or.inr ⟨dy, kx, dy', by simp, by simp, hPy, hcaty⟩
        · simp [hbl] at h
  | read x =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨dx, kx, dx', ha, hc, _, _⟩
    · simp [check1, ha] at h
    · simp only [check1, ha, Option.some.injEq] at h
      subst h
      exact ⟨σc, by simp [renC, check1, hc], hI⟩

/-- 离开块：两边去掉的变量正好对应。 -/
theorem rel_restrict {d d' : Nat} {σa σc : REnv} (hmd : m ≤ d) (hd : d' = d - m + d0)
    (hrel : ∀ x, Rel m d0 θ σa σc x) : ∀ x, Rel m d0 θ (restrict d σa) (restrict d' σc) x := by
  intro x
  rcases hrel x with ⟨ha, hc⟩ | ⟨dx, ks, dx', ha, hc, hP, hcat⟩
  · left
    exact ⟨by simp [restrict, ha], by simp [restrict, hc]⟩
  · have key : dx ≤ d ↔ dx' ≤ d' := by
      rcases hcat with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    by_cases hdx : dx ≤ d
    · have hdx' : dx' ≤ d' := key.mp hdx
      right
      exact ⟨dx, ks, dx', by simp [restrict, ha, hdx], by simp [restrict, hc, hdx'], hP, hcat⟩
    · have hdx' : ¬ dx' ≤ d' := fun h => hdx (key.mpr h)
      left
      exact ⟨by simp [restrict, ha, hdx], by simp [restrict, hc, hdx']⟩

theorem sim (hb : Below m d0 θ) (p : P) :
    ∀ {d d' : Nat} {σa σa' σc : REnv}, Inv m d0 θ d d' σa σc → check p d σa = some σa' →
      ∃ σc', check (renP m d0 θ p) d' σc = some σc' ∧ Inv m d0 θ d d' σa' σc' := by
  induction p with
  | skip =>
    intro d d' σa σa' σc hI h
    simp only [check, Option.some.injEq] at h
    subst h
    exact ⟨σc, rfl, hI⟩
  | cmd c =>
    intro d d' σa σa' σc hI h
    exact step hb hI h
  | seq p q ihp ihq =>
    intro d d' σa σa' σc hI h
    simp only [check] at h
    split at h
    · rename_i σ₁ h₁
      obtain ⟨τ₁, hτ₁, hI₁⟩ := ihp hI h₁
      obtain ⟨τ₂, hτ₂, hI₂⟩ := ihq hI₁ h
      exact ⟨τ₂, by simp [renP, check, hτ₁, hτ₂], hI₂⟩
    · contradiction
  | block p ih =>
    intro d d' σa σa' σc hI h
    simp only [check] at h
    split at h
    · rename_i σ₁ h₁
      cases h
      have hI' : Inv m d0 θ (d + 1) (d' + 1) σa σc :=
        ⟨by have := hI.hm; omega, by have := hI.hm; have := hI.hd; omega, hI.rel⟩
      obtain ⟨τ₁, hτ₁, hI₁⟩ := ih hI' h₁
      exact ⟨restrict d' τ₁, by simp [renP, check, hτ₁],
        ⟨hI.hm, hI.hd, rel_restrict hI.hm hI.hd hI₁.rel⟩⟩
    · contradiction

/-! ## 函数入口与主定理 -/

/-- 定义处的入口：前 `np` 个变量是参数，参数 `x` 住在区域参数 `β x` 里，值的类型里的区域是 `κ x`。 -/
def entryA (np : Nat) (β : Nat → Nat) (κ : Nat → List Nat) : REnv := fun x =>
  if x < np then some (β x + 1, κ x) else none

/-- 调用处的入口：参数住在实际区域 `θ (β x)` 里，类型里的区域换成实际区域。 -/
def entryC (np : Nat) (θ β : Nat → Nat) (κ : Nat → List Nat) : REnv := fun x =>
  if x < np then some (θ (β x) + 1, (κ x).map (ren m d0 θ)) else none

theorem inv_entry {np : Nat} {β : Nat → Nat} {κ : Nat → List Nat} (hmono : Mono m θ) (hb : Below m d0 θ)
    (hβ : ∀ x, x < np → β x < m) :
    Inv m d0 θ m d0 (entryA np β κ) (entryC (m := m) (d0 := d0) np θ β κ) := by
  refine ⟨Nat.le_refl m, by omega, ?_⟩
  intro x
  by_cases hx : x < np
  · have hβx := hβ x hx
    right
    refine ⟨β x + 1, κ x, θ (β x) + 1, by simp [entryA, hx], by simp [entryC, hx], ?_, ?_⟩
    · intro k hk
      have hkm : k < m := by omega
      have hle := hmono k (β x) (by omega) hβx
      unfold ren
      simp only [hkm, ↓reduceIte]
      omega
    · left
      have := hb (β x) hβx
      omega
  · left
    exact ⟨by simp [entryA, hx], by simp [entryC, hx]⟩

/-- **`Regions.DataGeneric` 主定理（一）。** 函数体在定义处（区域参数抽象成 `0 … m-1`）检查通过，
调用处的实际区域保持 outlives 顺序且都活着，则实例在调用处检查通过。值里可以有一组引用。 -/
theorem instance_accepted (hb : Below m d0 θ) (p : P) {σa σa' σc : REnv}
    (hI : Inv m d0 θ m d0 σa σc) (h : check p m σa = some σa') :
    ∃ σc', check (renP m d0 θ p) d0 σc = some σc' := by
  obtain ⟨σc', hc, _⟩ := sim hb p hI h
  exact ⟨σc', hc⟩

/-- **`Regions.DataGeneric` 主定理（二）。** 再加上调用时的运行状态满足 `Regions.Data` 的不变式，
实例执行不出错（每次读取时，值里每个引用的区域都活着），之后仍满足不变式。 -/
theorem instance_safe (hb : Below m d0 θ) (p : P) {σa σa' σc : REnv} {s : St}
    (hI : Inv m d0 θ m d0 σa σc) (h : check p m σa = some σa') (hg : Good d0 σc s) :
    ∃ s' σc', exec (renP m d0 θ p) s = some s' ∧ Good d0 σc' s' := by
  obtain ⟨σc', hc⟩ := instance_accepted hb p hI h
  obtain ⟨s', he, hg'⟩ := sound (renP m d0 θ p) hc hg
  exact ⟨s', σc', he, hg'⟩

/-- 从函数入口出发的版本。 -/
theorem entry_safe {np : Nat} {β : Nat → Nat} {κ : Nat → List Nat} (hmono : Mono m θ) (hb : Below m d0 θ)
    (hβ : ∀ x, x < np → β x < m) (p : P) {σa' : REnv} {s : St}
    (h : check p m (entryA np β κ) = some σa') (hg : Good d0 (entryC (m := m) (d0 := d0) np θ β κ) s) :
    ∃ s' σc', exec (renP m d0 θ p) s = some s' ∧ Good d0 σc' s' :=
  instance_safe hb p (inv_entry hmono hb hβ) h hg

end

/-! ## 例子：一个区域参数 `r`（0）；参数 0 是迭代器（类型里有 `r`），参数 1 是结果（住在 `r` 里） -/

def β1 : Nat → Nat := fun _ => 0
def κ1 : Nat → List Nat := fun x => if x = 0 then [0] else []

/-- `next`：读迭代器，把它里面的借用复制给结果：定义处接受。 -/
def next : P := .seq (.cmd (.read 0)) (.cmd (.copy 0 1))
example : (check next 1 (entryA 2 β1 κ1)).isSome = true := rfl

/-- 实例化：`r` ↦ 调用者的区域 1（调用者深度 3）：接受。 -/
def θ1 : Nat → Nat := fun _ => 1
example : (check (renP 1 3 θ1 next) 3 (entryC (m := 1) (d0 := 3) 2 θ1 β1 κ1)).isSome = true := rfl

/-- 函数体里本地块的引用装进结果：定义处拒绝（本地区域比 `r` 先结束）。 -/
def leak : P := .block (Core.Regions.Data.seqL [.cmd (.decl 2), .cmd (.ralloc 2 1), .cmd (.pack 1 [2])])
example : (check leak 1 (entryA 2 β1 κ1)).isNone = true := rfl

/-- 结果是 `.None`，类型里带着 `r`：接受；换名后列表跟着换。 -/
def none1 : P := .cmd (.empty 1 [0])
example : (check none1 1 (entryA 2 β1 κ1)).isSome = true := rfl
example : (check (renP 1 3 θ1 none1) 3 (entryC (m := 1) (d0 := 3) 2 θ1 β1 κ1)).isSome = true := rfl

end Core.Regions.DataGeneric
