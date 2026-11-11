import Core.Regions.Generic

/-!
# 闭包捕获引用

`Closures.Param` 的闭包不能用含引用的变量。现在放开：闭包可以用类型里有区域的变量（`&T in a`、`Vec<&T in a>`、区域 `a` 本身）。

**做法**：闭包提升出的函数（和带闭包的特化）里，捕获的变量的类型里的区域换成区域参数 `'c00`、`'c01`…，
编号按闭包所在位置的嵌套顺序（外层在前）；声明的先后关系只取那里真实成立的
（外层的 arena 比内层的活得久，函数自己的区域参数之间没有顺序，D3）。函数体在定义处按这些区域参数检查；
调用时区域参数实例化成调用者的真实区域 `θ`。这正是 `Regions.Generic` 的实例化，需要两个条件：

- `Mono`：`θ` 保持声明的顺序——编号就是按调用者那里的嵌套顺序排的（`capture_mono`）；
- `Below`：实际区域在调用时都活着。这是新的推理：被捕获的变量就在调用者的作用域里，
  `Regions.Model` 的不变式 `Good` 说变量指向的区域比变量的作用域更外层、作用域又不超过当前深度，所以区域活着（`capture_below`）。

**结论** `capture_safe`：提升出的函数在定义处检查通过，则调用时的实例执行不出错（`Regions.Generic` 的 `entry_safe`）。
**反例**：区域已经结束（编号等于当前深度）时 `Below` 不成立——闭包不能逃逸，所以这种实例化不会出现（`Closures.Param`）。
-/

namespace Core.Closures.CapRef
open Core.Regions.Model (REnv Good St5 P check exec)
open Core.Regions.Generic (Mono Below entryA entryC entry_safe renP)

/-- 被捕获的变量 `xs i` 在调用者的作用域里（深度 `dx i`），指向区域 `θ i`：这些区域在调用时都活着。 -/
theorem capture_below {m d0 : Nat} {σ : REnv} {s : St5} (hg : Good d0 σ s)
    {xs dx θ : Nat → Nat} (hx : ∀ i, i < m → σ (xs i) = some (dx i, some (θ i))) : Below m d0 θ := by
  intro i hi
  have h1 := (hg.ptrs (xs i) (dx i) (θ i) (hx i hi)).1
  have h2 := hg.scope (xs i) (dx i) (some (θ i)) (hx i hi)
  omega

/-- 区域参数按调用者那里的嵌套顺序编号（外层在前），实例化保持顺序。 -/
theorem capture_mono {m : Nat} {θ : Nat → Nat} (hord : ∀ i j, i < j → j < m → θ i ≤ θ j) : Mono m θ := by
  intro i j hij hj
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact hord i j h hj
  · subst h; exact Nat.le_refl _

/-- **结论**：提升出的函数（`m` 个区域参数，前 `np` 个变量是参数，参数 `x` 住在区域参数 `β x` 里）在定义处检查通过；
    调用者满足 `Regions.Model` 的不变式、捕获的变量指向区域 `θ`（按嵌套顺序编号），则调用时的实例执行不出错。 -/
theorem capture_safe {m d0 np : Nat} {θ β xs dx : Nat → Nat} {σ : REnv} {s0 s : St5}
    (hg0 : Good d0 σ s0) (hx : ∀ i, i < m → σ (xs i) = some (dx i, some (θ i)))
    (hord : ∀ i j, i < j → j < m → θ i ≤ θ j)
    (hβ : ∀ x, x < np → β x < m) (p : P) {σa' : REnv}
    (h : check p m (entryA np β) = some σa') (hg : Good d0 (entryC np θ β) s) :
    ∃ s' σc', exec (renP m d0 θ p) s = some s' ∧ Good d0 σc' s' :=
  entry_safe (capture_mono hord) (capture_below hg0 hx) hβ p h hg

/-- 反例：深度为 1 时区域 1 已经结束（或还没开始），把区域参数实例化成它不满足 `Below`。 -/
example : ¬ Below 1 1 (fun _ => 1) := by
  intro h
  have := h 0 (by decide)
  simp at this

end Core.Closures.CapRef
