import Core.M9

/-!
# M10（一）：trait 约束与静态派发

**问题**：泛型代码通过约束 `T: Eq` 调用 trait 的方法；单态化时每个调用换成实例类型的 `impl` 里的方法。
需要保证：定义处检查通过，并且实例满足约束（每个约束都有 `impl`，`impl` 的方法签名和 trait 一致），
则实例检查通过，安全与无泄漏仍由 M7（一）得到。

**方法调用在调用处的效果**只由签名决定（M7（二）的调用规则）：`let` 参数读一次（`use`），
`sink` 参数交出去（`give`），返回值是一个新值（`new`）。所以带方法调用的泛型程序 `TG`
按“查到的签名”展开成 M9 的 `G`：定义处查 trait 里声明的签名，实例查 `impl` 里的签名。
`impl` 的方法体本身是普通的具体函数，按 M7（二）单独检查，这里不再重复。

**主定理** `instance_accepted_T`：两种展开得到同一个 `G`（签名一致只需要参数约定一致），
然后用 M9 的 `instance_accepted`。

**例子**说明：没写约束就不能调用方法；实例缺 `impl` 被拒绝；
`impl` 把 `let` 参数改成 `sink` 会让泛型代码读到已交出的值——所以签名一致的检查是必要的。
-/

namespace Core.M10
open Core.M9

inductive Mode | rd | sink
  deriving DecidableEq, Repr

/-- 方法签名里的类型：`Self`，或者一个具体类别。 -/
inductive STy
  | self
  | k (k : Kind)
  deriving DecidableEq, Repr

structure MSig where
  params : List (Mode × STy)
  ret    : Option STy
  deriving DecidableEq, Repr

/-- trait：按下标排列的方法签名。 -/
abbrev Trait := List MSig

def modes (s : MSig) : List Mode := s.params.map Prod.fst

/-! ## 带方法调用的泛型程序 -/

inductive TG
  | skip
  | g      (c : GC)
  /-- 第 `i` 个类型参数的 trait `t` 的第 `m` 个方法，实参 `xs`，返回值放进 `r`。 -/
  | mcall  (i t m : Nat) (xs : List Var) (r : Option Var)
  | seq    (p q : TG)
  | branch (p q : TG)
  | loop   (b : TG)

def argG : Mode → Var → G
  | .rd,   x => .cmd (.use x)
  | .sink, x => .cmd (.give x)

/-- 调用处的效果：实参依次按约定传入，然后得到返回值。 -/
def callG : List Mode → List Var → Option Var → G
  | m :: ms, x :: xs, r => .seq (argG m x) (callG ms xs r)
  | _, _, some y        => .cmd (.new y)
  | _, _, none          => .skip

/-- 按签名查找 `L` 展开方法调用；查不到就失败。 -/
def expand (L : Nat → Nat → Nat → Option MSig) : TG → Option G
  | .skip => some .skip
  | .g c => some (.cmd c)
  | .mcall i t m xs r =>
    match L i t m with
    | some s => some (callG (modes s) xs r)
    | none   => none
  | .seq p q =>
    match expand L p, expand L q with
    | some a, some b => some (.seq a b)
    | _, _           => none
  | .branch p q =>
    match expand L p, expand L q with
    | some a, some b => some (.branch a b)
    | _, _           => none
  | .loop b =>
    match expand L b with
    | some a => some (.loop a)
    | none   => none

/-- 定义处：只能调用写了约束的 trait 的方法，签名取 trait 的声明。 -/
def absLook (traits : Nat → Trait) (tb : Nat → List Nat) (i t m : Nat) : Option MSig :=
  if t ∈ tb i then (traits t)[m]? else none

/-- 实例：签名取实例类型的 `impl`（`impls i t`：第 `i` 个类型实参对 trait `t` 的 `impl`）。 -/
def instLook (impls : Nat → Nat → Option Trait) (i t m : Nat) : Option MSig :=
  match impls i t with
  | some ms => ms[m]?
  | none    => none

def styTy (i : Nat) : STy → Ty
  | .self => .par i
  | .k k  => .k k

/-- 实参和返回值的类型与签名一致（`Self` 换成第 `i` 个类型参数）。 -/
def tgOk (Γ : Var → Ty) (L : Nat → Nat → Nat → Option MSig) : TG → Bool
  | .skip => true
  | .g _ => true
  | .mcall i t m xs r =>
    match L i t m with
    | some s =>
      decide (xs.map Γ = s.params.map (fun p => styTy i p.2)) &&
      (match r, s.ret with
       | some y, some st => decide (Γ y = styTy i st)
       | none, none      => true
       | _, _            => false)
    | none => false
  | .seq p q => tgOk Γ L p && tgOk Γ L q
  | .branch p q => tgOk Γ L p && tgOk Γ L q
  | .loop b => tgOk Γ L b

def genericOkT (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (traits : Nat → Trait)
    (tb : Nat → List Nat) (g : TG) : Bool :=
  match expand (absLook traits tb) g with
  | some h => tgOk Γ (absLook traits tb) g && genericOk N Γ bnd h
  | none   => false

def instanceOkT (N : Nat) (Γ : Var → Ty) (θ : Nat → Kind) (impls : Nat → Nat → Option Trait)
    (g : TG) : Bool :=
  match expand (instLook impls) g with
  | some h => instanceOk N Γ θ h
  | none   => false

/-- `impl` 和 trait 一致：方法一样多，每个方法的参数约定相同。 -/
def Conforms (tr ms : Trait) : Prop := ms.map modes = tr.map modes

/-- 实例满足约束：M9 的类别约束，加上每个约束都有一致的 `impl`。 -/
def RespectsT (bnd : Nat → Bool) (θ : Nat → Kind) (traits : Nat → Trait) (tb : Nat → List Nat)
    (impls : Nat → Nat → Option Trait) : Prop :=
  Respects bnd θ ∧ ∀ i t, t ∈ tb i → ∃ ms, impls i t = some ms ∧ Conforms (traits t) ms

/-! ## 证明 -/

/-- 定义处查到的签名，实例也查得到，而且参数约定相同。 -/
theorem look_conf {traits : Nat → Trait} {tb : Nat → List Nat} {impls : Nat → Nat → Option Trait}
    (hr : ∀ i t, t ∈ tb i → ∃ ms, impls i t = some ms ∧ Conforms (traits t) ms) :
    ∀ i t m s, absLook traits tb i t m = some s →
      ∃ s', instLook impls i t m = some s' ∧ modes s' = modes s := by
  intro i t m s h
  by_cases ht : t ∈ tb i
  · simp [absLook, ht] at h
    obtain ⟨ms, hi, hc⟩ := hr i t ht
    cases hm : ms[m]? with
    | none =>
      have e : (ms.map modes)[m]? = none := by simp [hm]
      rw [hc] at e
      simp [h] at e
    | some s' =>
      have e : (ms.map modes)[m]? = some (modes s') := by simp [hm]
      rw [hc] at e
      simp [h] at e
      exact ⟨s', by simp [instLook, hi, hm], e.symm⟩
  · simp [absLook, ht] at h

/-- 签名查找换成参数约定相同的另一个，展开结果不变。 -/
theorem expand_eq (A I : Nat → Nat → Nat → Option MSig)
    (hc : ∀ i t m s, A i t m = some s → ∃ s', I i t m = some s' ∧ modes s' = modes s) :
    ∀ (g : TG) (h : G), expand A g = some h → expand I g = some h
  | .skip, _, e => by simpa [expand] using e
  | .g _, _, e => by simpa [expand] using e
  | .mcall i t m xs r, h, e => by
    simp only [expand] at e ⊢
    cases hA : A i t m with
    | none => simp [hA] at e
    | some s =>
      obtain ⟨s', hI, hm⟩ := hc i t m s hA
      simp [hA] at e
      subst e
      simp [hI, hm]
  | .seq p q, h, e => by
    simp only [expand] at e ⊢
    cases hp : expand A p with
    | none => simp [hp] at e
    | some a =>
      cases hq : expand A q with
      | none => simp [hp, hq] at e
      | some b =>
        simp [hp, hq] at e
        subst e
        simp [expand_eq A I hc p a hp, expand_eq A I hc q b hq]
  | .branch p q, h, e => by
    simp only [expand] at e ⊢
    cases hp : expand A p with
    | none => simp [hp] at e
    | some a =>
      cases hq : expand A q with
      | none => simp [hp, hq] at e
      | some b =>
        simp [hp, hq] at e
        subst e
        simp [expand_eq A I hc p a hp, expand_eq A I hc q b hq]
  | .loop b, h, e => by
    simp only [expand] at e ⊢
    cases hb : expand A b with
    | none => simp [hb] at e
    | some a =>
      simp [hb] at e
      subst e
      simp [expand_eq A I hc b a hb]

/-- **主定理**：定义处检查通过、实例满足约束，则实例检查通过。 -/
theorem instance_accepted_T (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (θ : Nat → Kind)
    (traits : Nat → Trait) (tb : Nat → List Nat) (impls : Nat → Nat → Option Trait) (g : TG)
    (hg : genericOkT N Γ bnd traits tb g = true) (hr : RespectsT bnd θ traits tb impls) :
    instanceOkT N Γ θ impls g = true := by
  unfold genericOkT at hg
  cases he : expand (absLook traits tb) g with
  | none => simp [he] at hg
  | some h =>
    simp only [he, Bool.and_eq_true] at hg
    have hi := expand_eq _ _ (look_conf hr.2) g h he
    simp only [instanceOkT, hi]
    exact instance_accepted N Γ bnd θ h hg.2 hr.1

/-- 实例的安全与无泄漏：由 M7（一）的主定理得到。 -/
theorem instance_safe_T (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (θ : Nat → Kind)
    (traits : Nat → Trait) (tb : Nat → List Nat) (impls : Nat → Nat → Option Trait) (g : TG)
    (hg : genericOkT N Γ bnd traits tb g = true) (hr : RespectsT bnd θ traits tb impls) :
    ∃ h, expand (instLook impls) g = some h ∧ Core.M7.accepts N (tr (fun x => instK θ (Γ x)) h) = true := by
  have hi := instance_accepted_T N Γ bnd θ traits tb impls g hg hr
  unfold instanceOkT at hi
  cases he : expand (instLook impls) g with
  | none => simp [he] at hi
  | some h =>
    simp only [he] at hi
    exact ⟨h, rfl, hi⟩

/-! ## 例子

trait 0 是 `Show { fn show(self) -> I64 }`：一个 `let` 参数，返回可复制的值。
变量 0 的类型是参数 `T`，其余变量是可复制的。 -/

def showT : Trait := [⟨[(.rd, .self)], some (.k .copy)⟩]
def traitsx : Nat → Trait := fun _ => showT
def Γe : Var → Ty := fun x => if x = 0 then .par 0 else .k .copy
def plainB : Nat → Bool := fun _ => false
def θown : Nat → Kind := fun _ => .own
def bShow : Nat → List Nat := fun _ => [0]
def bNone : Nat → List Nat := fun _ => []

/-- `fn twice<T: Show>(sink x: T) { show(x); show(x) }`，`x` 在作用域结束时析构。 -/
def twice : TG :=
  .seq (.g (.new 0)) (.seq (.mcall 0 0 0 [0] (some 1)) (.mcall 0 0 0 [0] (some 2)))

example : genericOkT 3 Γe plainB traitsx bShow twice = true := rfl
/-- 没写 `T: Show` 就不能调用 `show`。 -/
example : genericOkT 3 Γe plainB traitsx bNone twice = false := rfl

/-- 实例类型有一致的 `impl`（例如 `Box<I64>`）：接受。 -/
def implOk : Nat → Nat → Option Trait := fun _ _ => some showT
example : instanceOkT 3 Γe θown implOk twice = true := rfl

/-- 实例类型没有 `impl`：拒绝。 -/
def implNone : Nat → Nat → Option Trait := fun _ _ => none
example : instanceOkT 3 Γe θown implNone twice = false := rfl

/-- `impl` 把参数改成 `sink`：第一次调用交出了 `x`，第二次读到已交出的值，实例被拒绝——
    所以要检查 `impl` 的签名和 trait 一致。 -/
def implBad : Nat → Nat → Option Trait := fun _ _ => some [⟨[(.sink, .self)], some (.k .copy)⟩]
example : instanceOkT 3 Γe θown implBad twice = false := rfl
example : ¬ Conforms showT [⟨[(.sink, .self)], some (.k .copy)⟩] := by
  unfold Conforms; decide

end Core.M10
