import Core.Regions.Model

/-!
# 区域参数与泛型实例化

**问题**：泛型函数可以带区域参数（`fn f<'a, 'b>(…)`，类型实参可以是 `&T in a`），在定义处检查一次，
之后对每个调用处的实际区域实例化。需要保证：定义处检查通过，并且调用处给的实际区域满足声明的
outlives 顺序，则实例在调用处的具体区域下也检查通过，从而由 `Regions.Model` 的 `sound` 得到实例执行不出错。

**做法**：函数体是 `Regions.Model` 的程序。定义处把 `m` 个区域参数当作抽象深度 `0 … m-1`（编号小的活得久，
即声明的 outlives 顺序），函数体从深度 `m` 开始，本地的块（arena）在它上面依次往下。
参数变量 `x` 住在区域参数 `β x` 里，作用域深度是 `β x + 1`，所以它只能存放区域 `≤ β x`（不比它短命）
的引用。调用处给出实际区域 `θ`（在调用者的深度 `d0` 之下），实例把程序里的区域编号按
`ren k = if k < m then θ k else k - m + d0` 换掉：参数区域换成实际区域，本地区域整体平移。

**条件**：`θ` 保持 outlives 顺序（`i ≤ j → θ i ≤ θ j`，可以把两个参数实例化成同一个区域），
并且实际区域都在调用者的深度之下（`θ i < d0`）。

**主定理**：
- `instance_accepted`：定义处接受 ⇒ 实例在调用处接受；
- `instance_safe`：再加上调用处的运行状态满足 `Regions.Model` 的不变式，实例执行不出错。

证明是一个模拟（`Inv`）：每个变量在两边的作用域深度对应——参数变量都住在函数体之外
（抽象 `≤ m`、实际 `≤ d0`），本地变量的深度正好平移 `d0 - m`；并且抽象上能存的区域，
换名后实际上也能存（`k < dx → ren k < dx'`）。离开块时两边去掉的变量正好对应。

**例子**：把 `'a` 的引用存进住在 `'b` 里的参数（`'a` 比 `'b` 活得久）：定义处接受；
按顺序实例化接受；把两个区域反过来实例化（不满足条件）被拒绝；反方向存放在定义处就被拒绝。
-/

namespace Core.Regions.Generic
open Core.Regions.Model (Cmd5 P REnv check1 check restrict exec Good sound St5)

/-! ## 实例化：区域换名 -/

/-- 区域编号换名：参数区域换成实际区域，本地区域平移到调用者的深度之上。 -/
def ren (m d0 : Nat) (θ : Nat → Nat) (k : Nat) : Nat := if k < m then θ k else k - m + d0

def renC (m d0 : Nat) (θ : Nat → Nat) : Cmd5 → Cmd5
  | .decl x     => .decl x
  | .ralloc x k => .ralloc x (ren m d0 θ k)
  | .copy x y   => .copy x y
  | .read x     => .read x

def renP (m d0 : Nat) (θ : Nat → Nat) : P → P
  | .skip    => .skip
  | .cmd c   => .cmd (renC m d0 θ c)
  | .seq p q => .seq (renP m d0 θ p) (renP m d0 θ q)
  | .block p => .block (renP m d0 θ p)

/-- 调用处给的实际区域保持声明的 outlives 顺序。 -/
def Mono (m : Nat) (θ : Nat → Nat) : Prop := ∀ i j, i ≤ j → j < m → θ i ≤ θ j

/-- 实际区域都在调用者的深度之下（调用时活着）。 -/
def Below (m d0 : Nat) (θ : Nat → Nat) : Prop := ∀ i, i < m → θ i < d0

/-! ## 模拟关系 -/

/-- 变量 `x` 在两边的静态信息对应。 -/
def Rel (m d0 : Nat) (θ : Nat → Nat) (σa σc : REnv) (x : Nat) : Prop :=
  (σa x = none ∧ σc x = none) ∨
  ∃ dx o dx', σa x = some (dx, o) ∧ σc x = some (dx', o.map (ren m d0 θ)) ∧
    (∀ k, k < dx → ren m d0 θ k < dx') ∧
    ((dx ≤ m ∧ dx' ≤ d0) ∨ (m ≤ dx ∧ dx' = dx - m + d0))

structure Inv (m d0 : Nat) (θ : Nat → Nat) (d d' : Nat) (σa σc : REnv) : Prop where
  hm  : m ≤ d
  hd  : d' = d - m + d0
  rel : ∀ x, Rel m d0 θ σa σc x

section
variable {m d0 : Nat} {θ : Nat → Nat}

theorem ren_lt (hb : Below m d0 θ) {k d : Nat} (hmd : m ≤ d) (hk : k < d) :
    ren m d0 θ k < d - m + d0 := by
  unfold ren
  split
  · rename_i hkm
    have := hb k hkm
    omega
  · omega

theorem rel_upd {σa σc : REnv} {x : Nat} {a c : Option (Nat × Option Nat)}
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

/-- 一条命令：抽象上接受 ⇒ 换名后接受，关系保持。 -/
theorem step (hb : Below m d0 θ) {d d' : Nat} {σa σa' σc : REnv} {c : Cmd5}
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
      refine ⟨upd σc x (some (d', none)), by simp [renC, check1, hcx], ⟨hI.hm, hI.hd, ?_⟩⟩
      apply rel_upd hI.rel
      refine Or.inr ⟨d, none, d', by simp, by simp, ?_, Or.inr ⟨hI.hm, hI.hd⟩⟩
      intro k hk
      rw [hI.hd]
      exact ren_lt hb hI.hm hk
    · contradiction
  | ralloc x k =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨dx, o, dx', ha, hc, hP, hcat⟩
    · simp [check1, ha] at h
    · simp only [check1, ha] at h
      by_cases hk : k < dx
      · simp only [ite_eq_left hk, Option.some.injEq] at h
        subst h
        refine ⟨upd σc x (some (dx', some (ren m d0 θ k))),
          by simp [renC, check1, hc, hP k hk], ⟨hI.hm, hI.hd, ?_⟩⟩
        apply rel_upd hI.rel
        exact Or.inr ⟨dx, some k, dx', by simp, by simp, hP, hcat⟩
      · simp [ite_eq_right hk] at h
  | copy x y =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨_, o, _, ha, hc, _, _⟩
    · simp [check1, ha] at h
    · cases o with
      | none => simp [check1, ha] at h
      | some k =>
        rcases hI.rel y with ⟨hay, _⟩ | ⟨dy, _, dy', hay, hcy, hPy, hcaty⟩
        · simp [check1, ha, hay] at h
        · simp only [check1, ha, hay] at h
          by_cases hk : k < dy
          · simp only [ite_eq_left hk, Option.some.injEq] at h
            subst h
            refine ⟨upd σc y (some (dy', some (ren m d0 θ k))), ?_, ⟨hI.hm, hI.hd, ?_⟩⟩
            · simp at hc
              simp [renC, check1, hc, hcy, hPy k hk]
            · apply rel_upd hI.rel
              exact Or.inr ⟨dy, some k, dy', by simp, by simp, hPy, hcaty⟩
          · simp [ite_eq_right hk] at h
  | read x =>
    rcases hI.rel x with ⟨ha, _⟩ | ⟨_, o, _, ha, hc, _, _⟩
    · simp [check1, ha] at h
    · cases o with
      | none => simp [check1, ha] at h
      | some k =>
        simp only [check1, ha, Option.some.injEq] at h
        subst h
        refine ⟨σc, ?_, hI⟩
        simp at hc
        simp [renC, check1, hc]

/-- 离开块：两边去掉的变量正好对应。 -/
theorem rel_restrict {d d' : Nat} {σa σc : REnv} (hmd : m ≤ d) (hd : d' = d - m + d0)
    (hrel : ∀ x, Rel m d0 θ σa σc x) : ∀ x, Rel m d0 θ (restrict d σa) (restrict d' σc) x := by
  intro x
  rcases hrel x with ⟨ha, hc⟩ | ⟨dx, o, dx', ha, hc, hP, hcat⟩
  · left
    exact ⟨by simp [restrict, ha], by simp [restrict, hc]⟩
  · have key : dx ≤ d ↔ dx' ≤ d' := by
      rcases hcat with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    by_cases hdx : dx ≤ d
    · have hdx' : dx' ≤ d' := key.mp hdx
      right
      exact ⟨dx, o, dx', by simp [restrict, ha, hdx], by simp [restrict, hc, hdx'], hP, hcat⟩
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

/-- 定义处的入口：前 `np` 个变量是参数，参数 `x` 住在区域参数 `β x` 里。 -/
def entryA (np : Nat) (β : Nat → Nat) : REnv := fun x =>
  if x < np then some (β x + 1, none) else none

/-- 调用处的入口：参数住在实际区域 `θ (β x)` 里。 -/
def entryC (np : Nat) (θ β : Nat → Nat) : REnv := fun x =>
  if x < np then some (θ (β x) + 1, none) else none

theorem inv_entry {np : Nat} {β : Nat → Nat} (hmono : Mono m θ) (hb : Below m d0 θ)
    (hβ : ∀ x, x < np → β x < m) : Inv m d0 θ m d0 (entryA np β) (entryC np θ β) := by
  refine ⟨Nat.le_refl m, by omega, ?_⟩
  intro x
  by_cases hx : x < np
  · have hβx := hβ x hx
    right
    refine ⟨β x + 1, none, θ (β x) + 1, by simp [entryA, hx], by simp [entryC, hx], ?_, ?_⟩
    · intro k hk
      have hkm : k < m := by omega
      have hle := hmono k (β x) (by omega) hβx
      unfold ren
      rw [ite_eq_left hkm]
      omega
    · left
      have := hb (β x) hβx
      omega
  · left
    exact ⟨by simp [entryA, hx], by simp [entryC, hx]⟩

/-- **`Regions.Generic` 主定理（一）。** 函数体在定义处（区域参数抽象成 `0 … m-1`）检查通过，
调用处的实际区域保持 outlives 顺序且都活着，则实例在调用处检查通过。 -/
theorem instance_accepted (hb : Below m d0 θ) (p : P) {σa σa' σc : REnv}
    (hI : Inv m d0 θ m d0 σa σc) (h : check p m σa = some σa') :
    ∃ σc', check (renP m d0 θ p) d0 σc = some σc' := by
  obtain ⟨σc', hc, _⟩ := sim hb p hI h
  exact ⟨σc', hc⟩

/-- **`Regions.Generic` 主定理（二）。** 再加上调用时的运行状态满足 `Regions.Model` 的不变式，实例执行不出错
（每次分配、读取时区域都活着），之后仍满足不变式。 -/
theorem instance_safe (hb : Below m d0 θ) (p : P) {σa σa' σc : REnv} {s : St5}
    (hI : Inv m d0 θ m d0 σa σc) (h : check p m σa = some σa') (hg : Good d0 σc s) :
    ∃ s' σc', exec (renP m d0 θ p) s = some s' ∧ Good d0 σc' s' := by
  obtain ⟨σc', hc⟩ := instance_accepted hb p hI h
  obtain ⟨s', he, hg'⟩ := sound (renP m d0 θ p) hc hg
  exact ⟨s', σc', he, hg'⟩

/-- 从函数入口出发的版本。 -/
theorem entry_safe {np : Nat} {β : Nat → Nat} (hmono : Mono m θ) (hb : Below m d0 θ)
    (hβ : ∀ x, x < np → β x < m) (p : P) {σa' : REnv} {s : St5}
    (h : check p m (entryA np β) = some σa') (hg : Good d0 (entryC np θ β) s) :
    ∃ s' σc', exec (renP m d0 θ p) s = some s' ∧ Good d0 σc' s' :=
  instance_safe hb p (inv_entry hmono hb hβ) h hg

end

/-! ## 例子：两个区域参数 `'a`（0，活得久）、`'b`（1）；参数 0 住在 `'a`，参数 1 住在 `'b` -/

def idβ : Nat → Nat := fun x => x

/-- 在 `'a` 里分配，存进住在 `'b` 里的参数 1：`'a` 比 `'b` 活得久，定义处接受。 -/
def store : P := .cmd (.ralloc 1 0)
example : (check store 2 (entryA 2 idβ)).isSome = true := rfl

/-- 反过来，把 `'b` 的引用存进住在 `'a` 里的参数 0：定义处拒绝。 -/
def storeBad : P := .cmd (.ralloc 0 1)
example : (check storeBad 2 (entryA 2 idβ)).isNone = true := rfl

/-- 按顺序实例化（`'a` ↦ 区域 0，`'b` ↦ 区域 1，调用者深度 3）：接受。 -/
def θok : Nat → Nat := fun i => i
example : (check (renP 2 3 θok store) 3 (entryC 2 θok idβ)).isSome = true := rfl

/-- 两个参数实例化成同一个区域：也满足条件，接受。 -/
def θsame : Nat → Nat := fun _ => 1
example : (check (renP 2 3 θsame store) 3 (entryC 2 θsame idβ)).isSome = true := rfl

/-- 反过来实例化（`'a` ↦ 区域 1，`'b` ↦ 区域 0）：不满足顺序条件，实例被拒绝
（`'a` 的区域比住着参数 1 的区域先结束）。 -/
def θrev : Nat → Nat := fun i => 1 - i
example : ¬ (θrev 0 ≤ θrev 1) := by decide
example : (check (renP 2 3 θrev store) 3 (entryC 2 θrev idβ)).isNone = true := rfl

/-- 函数体里的本地块：本地区域平移到调用者之上，按顺序实例化后照常接受。 -/
def local1 : P := .block (Core.Regions.Model.seqL [.cmd (.decl 2), .cmd (.ralloc 2 2), .cmd (.read 2)])
example : (check local1 2 (entryA 2 idβ)).isSome = true := rfl
example : (check (renP 2 3 θok local1) 3 (entryC 2 θok idβ)).isSome = true := rfl

end Core.Regions.Generic
