import Core.Closures.Param
import Core.Traits.ImplSearch

/-!
# 可以存起来的闭包 `Fn(T) -> U` 和 trait 对象 `dyn Tr`

`Closures.Param` 的闭包只能当实参传。这里加上两种可以存进变量、字段、Vec，也可以返回的值：
- `Fn(T) -> U`：闭包 `|x| …` 写在别的位置（或者传给 `Fn` 类型的参数）时，用到的外面的变量**按值**拿进来
  （`Box`、`Vec`、`Str` 这类会移动，数之类会复制），存在堆上的环境里，所以闭包自己拥有环境；
- `dyn Tr`：任何实现了 `Tr` 的值，连同 `Tr` 的方法表（vtable）一起放到堆上，调用方法时按方法表派发。

两种值的表示一样：堆上的环境（或值）加一张函数表；`Fn(T) -> U` 就是内建 trait `Call` 的 trait 对象，
它只有一个方法 `call(inout self, x: T) -> U`。闭包可以改自己的环境，所以**调用时闭包按 `inout`**：
它要在 `var` 变量或 `inout` 位置里。创建就是用捕获造一个结构体（捕获的移动和普通的移动一样检查），
析构就是析构这个结构体（方法表里有它的析构函数）；这两件事不需要新的证明。需要新证明的是下面三件事。

## 一、不会悬空
可以存、可以返回的值不能指向栈帧：环境里不能有 `Closures.Param` 的那种闭包（它们引用创建它的栈帧），
第一版也不能有引用（`&T in a`，`Fn` 的类型里没有区域）。`Storable`（`ok`）递归地检查这一点。
在 `Closures.Param` 的栈模型里加上 `pack`，允许把满足 `ok` 的值赋给变量、作返回值：`good_reach` 仍然成立，所以
`clo_live`、`pop_clean` 照旧成立；反例：如果环境里可以有 `Closures.Param` 的闭包，返回之后就悬空了。

## 二、排他性：调用 `f(x)` 时 `f` 按 `inout`
调用 `f(a₁, …)` 当作 `f` 按 `inout`、`aᵢ` 按各自约定的调用检查（`Calls.NArgs` 的规则）。闭包体访问的位置要么来自实参
（`aᵢ` 里面），要么在环境里（`f` 里面）。`env_disjoint`：前者和后者从不重叠——所以闭包体可以当作以环境
（`inout`）和实参为参数的普通函数检查。反例：`fs[0](fs)` 这种把闭包所在的位置又当实参的调用被拒绝。

## 三、动态派发
- **对象安全**：`dyn Tr` 要求 `Tr` 的每个方法的接收者是 `self`（`let` 或 `inout`），其余参数和返回类型里都没有 `Self`，
  也没有方法自己的类型参数。`sig_indep`：这时把 `Self` 换成任何类型，方法的其余签名都一样——
  所以调用者不知道里面是什么类型也能检查调用。反例：`fn eq(self, other: Self)` 换成不同的类型签名就不同。
- **方法表**：把类型 `t` 的值转成 `dyn Tr` 时要查到 `t: Tr`（`Traits.ImplSearch` 的 `solve`），查到的 impl 是唯一的（`impl_unique`），
  方法表就用它的方法。`vtable_found`：有推导就查得到；`dispatch_eq`：经过方法表的调用和直接调用这个 impl 的方法结果一样。
-/

namespace Core.Closures.Stored

/-! ## 一、不会悬空 -/

/-- 值：数（代表所有不含引用、不含闭包的值）、`Closures.Param` 的闭包（记着它的栈帧）、`Fn` 或 `dyn` 的值（环境按值拥有）。 -/
inductive Val
  | num (n : Nat)
  | clo (frame : Nat)
  | pack (env : List Val)

mutual
/-- 可以存、可以返回：里面任何地方都没有 `Closures.Param` 的闭包。 -/
def ok : Val → Bool
  | .num _ => true
  | .clo _ => false
  | .pack env => okL env

def okL : List Val → Bool
  | [] => true
  | v :: vs => ok v && okL vs
end

/-- 在有 `n` 个帧的栈上，这个值引用的帧都在下面：`Closures.Param` 的闭包引用编号小于 `n` 的帧，`pack` 里什么都不引用。 -/
def refOk (n : Nat) : Val → Bool
  | .num _ => true
  | .clo j => decide (j < n)
  | .pack env => okL env

theorem refOk_of_ok {n : Nat} : ∀ {v : Val}, ok v = true → refOk n v = true
  | .num _, _ => rfl
  | .clo _, h => by simp [ok] at h
  | .pack _, h => by simpa [ok, refOk] using h

theorem refOk_mono {n m : Nat} (hm : n ≤ m) : ∀ {v : Val}, refOk n v = true → refOk m v = true
  | .num _, _ => rfl
  | .clo _, h => by simp [refOk] at h ⊢; omega
  | .pack _, h => by simpa [refOk] using h

abbrev Stack := List (List Val)

def Good : Stack → Prop
  | [] => True
  | f :: rest => (∀ v ∈ f, refOk rest.length v = true) ∧ Good rest

/-- 调用：实参引用的帧都在栈上（当前帧新建的 `Closures.Param` 闭包、`pack`、数）。
    赋值：存满足 `ok` 的值（包括新建的 `pack`）。返回：返回满足 `ok` 的值，放进调用者的帧。 -/
inductive Step : Stack → Stack → Prop
  | call (s : Stack) (args : List Val) : (∀ v ∈ args, refOk s.length v = true) → Step s (args :: s)
  | store (f : List Val) (rest : Stack) (v : Val) : ok v = true → Step (f :: rest) ((f ++ [v]) :: rest)
  | ret (top f : List Val) (rest : Stack) (v : Val) : ok v = true → Step (top :: f :: rest) ((f ++ [v]) :: rest)

inductive Reach : Stack → Prop
  | start : Reach [[]]
  | step {s t : Stack} : Reach s → Step s t → Reach t

theorem step_good {s t : Stack} (hs : Good s) (st : Step s t) : Good t := by
  cases st with
  | call _ args h => exact ⟨h, hs⟩
  | store f rest v hv =>
    refine ⟨fun w hw => ?_, hs.2⟩
    rcases List.mem_append.1 hw with hw | hw
    · exact hs.1 w hw
    · simp at hw; subst hw; exact refOk_of_ok hv
  | ret top f rest v hv =>
    obtain ⟨_, hf, hr⟩ := hs
    refine ⟨fun w hw => ?_, hr⟩
    rcases List.mem_append.1 hw with hw | hw
    · exact hf w hw
    · simp at hw; subst hw; exact refOk_of_ok hv

theorem good_reach {s : Stack} (h : Reach s) : Good s := by
  induction h with
  | start => exact ⟨fun v hv => by simp at hv, trivial⟩
  | step _ st ih => exact step_good ih st

theorem below : ∀ {rest : Stack}, Good rest → ∀ f ∈ rest, ∀ v ∈ f, refOk rest.length v = true
  | [], _, f, hf, _, _ => by simp at hf
  | g :: r, ⟨hg, hr⟩, f, hf, v, hv => by
    rcases List.mem_cons.1 hf with e | e
    · subst e
      exact refOk_mono (by simp) (hg v hv)
    · exact refOk_mono (by simp) (below hr f e v hv)

/-- 调用 `Closures.Param` 的闭包时，它的帧还在栈上。 -/
theorem clo_live {top : List Val} {rest : Stack} (h : Reach (top :: rest)) {j : Nat}
    (hj : Val.clo j ∈ top) : j < rest.length := by
  have := (good_reach h).1 _ hj
  simpa [refOk] using this

/-- 栈顶的帧返回之后，剩下的帧里没有引用它的闭包（`pack` 里也没有）。 -/
theorem pop_clean {top : List Val} {rest : Stack} (h : Reach (top :: rest)) :
    ∀ f ∈ rest, Val.clo rest.length ∉ f := by
  intro f hf hc
  have := below (good_reach h).2 f hf _ hc
  simp [refOk] at this

/-- 存起来的 `Fn`、`dyn` 值里从来没有 `Closures.Param` 的闭包。 -/
theorem pack_clean {s : Stack} (h : Reach s) : ∀ f ∈ s, ∀ env, Val.pack env ∈ f → okL env = true := by
  intro f hf env he
  have g := good_reach h
  cases s with
  | nil => simp at hf
  | cons top rest =>
    rcases List.mem_cons.1 hf with e | e
    · subst e; simpa [refOk] using g.1 _ he
    · simpa [refOk] using below g.2 f e _ he

/-! ### 反例：环境里放 `Closures.Param` 的闭包，返回之后就悬空了 -/

-- 帧 1 把引用自己的闭包放进 `pack` 返回给帧 0
example : ok (.pack [.clo 1]) = false := by decide
example : ¬ Good [[.pack [.clo 1]]] := by
  intro h
  have := h.1 (.pack [.clo 1]) (List.mem_singleton.2 rfl)
  exact absurd this (by decide)

/-! ## 二、排他性 -/

section
open Core.Closures.Param (Places Arg Mode Compat Ok)
variable {P : Type} (S : Places P)

/-- 调用 `f(args)` 按 `args ++ [f 按 inout]` 检查通过时，闭包体从实参里访问的位置 `y`
    和环境里（`f` 里面）的位置 `e` 不重叠。 -/
theorem env_disjoint {args : List (Arg P)} {f : P} (h : Ok S (args ++ [⟨f, .inout⟩]))
    {a : Arg P} (ha : a ∈ args) {y e : P} (hy : S.sub y a.loc) (he : S.sub e f) : ¬ S.ov y e := by
  intro hov
  have h1 : S.ov y f := S.sub_ov e f y he hov
  have h2 : S.ov f a.loc := S.sub_ov y a.loc f hy (S.symm _ _ h1)
  unfold Ok at h
  rw [List.pairwise_append] at h
  have := h.2.2 a ha ⟨f, .inout⟩ (by simp) (S.symm _ _ h2)
  cases this.2

end

section
open Core.Closures.Param (Ok names)

-- counter(x)：闭包 counter 是变量 0，按 inout；x 是变量 1，接受
example : Ok names [⟨1, .let_⟩, ⟨0, .inout⟩] := by unfold Ok; decide
-- fs[0](fs)：闭包在 fs（变量 0）里面，fs 又当实参，拒绝
example : ¬ Ok names [⟨0, .let_⟩, ⟨0, .inout⟩] := by unfold Ok; decide

end

/-! ## 三、动态派发 -/

section
open Core.Traits.ImplSearch (Ty ap fv sz Impl Derives solve WF Coherent impl_unique solve_complete)

/-- `Self` 是类型参数 0：把它换成 `t`，别的类型参数照 `σ`。 -/
def upd (σ : Nat → Ty) (t : Ty) : Nat → Ty := fun n => if n = 0 then t else σ n

theorem ap_indep (σ : Nat → Ty) (t t' : Ty) : ∀ p : Ty, 0 ∉ fv p → ap (upd σ t) p = ap (upd σ t') p
  | .var n, h => by
    have : n ≠ 0 := by intro e; subst e; simp [fv] at h
    simp [ap, upd, this]
  | .con _, _ => rfl
  | .app f a, h => by
    simp only [fv, List.mem_append, not_or] at h
    simp only [ap]
    rw [ap_indep σ t t' f h.1, ap_indep σ t t' a h.2]

theorem map_eq {f g : Ty → Ty} : ∀ l : List Ty, (∀ a ∈ l, f a = g a) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons]
    rw [h a (by simp), map_eq l (fun b hb => h b (by simp [hb]))]

/-- 方法的签名：接收者 `self` 之外的参数，和返回类型。 -/
structure Sig where
  params : List Ty
  ret : Ty

/-- 对象安全：除了接收者，签名里没有 `Self`。 -/
def ObjSafe (s : Sig) : Prop := (∀ p ∈ s.params, 0 ∉ fv p) ∧ 0 ∉ fv s.ret

/-- 实现类型是 `t` 时调用者看到的签名。 -/
def inst (σ : Nat → Ty) (t : Ty) (s : Sig) : List Ty × Ty := (s.params.map (ap (upd σ t)), ap (upd σ t) s.ret)

/-- 对象安全的方法，签名和里面是什么类型无关。 -/
theorem sig_indep {s : Sig} (h : ObjSafe s) (σ : Nat → Ty) (t t' : Ty) : inst σ t s = inst σ t' s := by
  unfold inst
  rw [ap_indep σ t t' s.ret h.2, map_eq s.params (fun p hp => ap_indep σ t t' p (h.1 p hp))]

-- `Call` 的 `call(inout self, x: T) -> U`（T、U 是类型参数 1、2）是对象安全的
example : ObjSafe ⟨[.var 1], .var 2⟩ := by unfold ObjSafe; decide
-- 反例：`fn eq(self, other: Self) -> Bool`，实现类型是 I64（0）和 Str（2）时签名不同
example : inst (fun n => .var n) (.con 0) ⟨[.var 0], .con 3⟩ ≠ inst (fun n => .var n) (.con 2) ⟨[.var 0], .con 3⟩ := by
  decide

/-- 转成 `dyn tr` 时查得到 impl（方法表造得出来）。 -/
theorem vtable_found {I : List Impl} (hw : ∀ a ∈ I, WF a) (hc : Coherent I) {tr : Nat} {t : Ty}
    (hd : Derives I [] tr t) : solve I [] (sz t + 1) tr t = true :=
  solve_complete hw hc hd _ (by omega)

/-- `dyn` 值：转换时选定的 impl 和里面的值。方法的实现是 `body a m`（impl `a` 的第 `m` 个方法）。 -/
structure Dyn (V : Type) where
  impl : Impl
  val : V

def call {V : Type} (body : Impl → Nat → V → V) (d : Dyn V) (m : Nat) : V := body d.impl m d.val

/-- 经过方法表的调用，等于对里面的类型直接调用它的 impl 的方法（impl 是唯一的）。 -/
theorem dispatch_eq {V : Type} {I : List Impl} (hc : Coherent I) (body : Impl → Nat → V → V)
    {tr : Nat} {t : Ty} {σ τ : Nat → Ty} (d : Dyn V)
    (h1 : d.impl ∈ I) (h2 : d.impl.tr = tr) (h3 : ap σ d.impl.head = t)
    {b : Impl} (hb : b ∈ I) (hbt : b.tr = tr) (hbh : ap τ b.head = t) (m : Nat) :
    call body d m = body b m d.val := by
  have : d.impl = b := impl_unique hc h1 hb (h2.trans hbt.symm) h3 hbh
  simp [call, this]

end

end Core.Closures.Stored
