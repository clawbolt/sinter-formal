import Core.FlowGraph.Lower

/-!
# `panic`——中止程序

**语义**：`panic(msg)` 打印说明后立刻结束进程（退出码 101），**不析构任何值**、不执行 `errdefer`、
不要求线性值已被消费：进程结束时操作系统收回全部内存。`option.unwrap` 这类函数在 `.None` 时就是 `panic`。
`panic` 的类型是 `Never`（和 `return` 一样），后面的代码走不到。

这是一条明确的取舍：线性值的保证（“必须被消费”）只对正常返回和出错返回（`Err`）成立；
`panic` 是“程序本身出了错，放弃一切”，不是普通的出错路径。需要清理的出错情况应当用 `Result`。

**模型**：在 `FlowGraph.Region` 的 CFG 上加一种节点 `halt`（`NodeP.halt = true`），执行到它就以 `.halt` 结束。
**编码**：导出给 Lean 时，`halt` 节点写成一个**指向自己的空节点**（`nop`，后继是自己）。
它有后继，所以不是出口，检查器不要求线性值已消费、深度为 0；执行时它原地打转直到燃料用完（`.oof`，不是错误）。
于是现有的检查器 `cfgOk`（以及编译器用的 `acceptsF`）一字不改就能检查含 `panic` 的程序。

**结论** `panic_safe`：编码后的 CFG 被接受，则真实语义（遇到 `halt` 就停）下执行不出错；
从正常出口或出错出口离开时，和 `FlowGraph.Region` 一样没有泄漏、线性值都已消费、没有区域残留。
证明是一个模拟（`sim`）：在走到 `halt` 之前，两种语义一步一步完全相同。
-/

namespace Core.FlowGraph.Panic
open Core.Unified.RegionDefs (St Res Clean)
open Core.FlowGraph.Region (Op Node CFG stepOp run cfgOk)
open Core.FlowGraph.Check (pick)

/-- 节点：普通的 `FlowGraph.Region` 节点，或者 `halt`（`panic`）。 -/
structure NodeP where
  nd   : Node
  halt : Bool

inductive ResP
  | ok  (s : St) (cs : List Bool)
  | exn (s : St) (cs : List Bool)
  | err
  | oof
  | halt

/-- 真实语义：走到 `halt` 节点就停（进程退出），之后什么都不做。 -/
def runP (g : List NodeP) : Nat → Nat → St → List Bool → ResP
  | 0,     _,  _, _  => .oof
  | n + 1, pc, s, cs =>
    match g[pc]? with
    | none    => .err
    | some nd =>
      if nd.halt = true then .halt
      else
        match stepOp s nd.nd.op with
        | none    => .err
        | some s' =>
          match pick nd.nd.succ cs with
          | none =>
            match nd.nd.raise with
            | true  => .exn s' cs
            | false => .ok s' cs
          | some (t, cs') => runP g n t s' cs'

/-- 编码：`halt` 节点换成指向自己的空节点。 -/
def encAt (g : List NodeP) (pc : Nat) : Option Node :=
  (g[pc]?).map (fun nd => if nd.halt = true then ⟨.nop, [pc], false⟩ else nd.nd)

/-- `g'` 是 `g` 的编码（编译器导出的就是 `g'`）。 -/
def Enc (g : List NodeP) (g' : CFG) : Prop := ∀ pc, g'[pc]? = encAt g pc

def lift : ResP → Res
  | .ok s cs  => .ok s cs
  | .exn s cs => .exn s cs
  | .err      => .err
  | .oof      => .oof
  | .halt     => .oof

/-- **模拟**：没有走到 `halt` 时，编码后的 CFG 的执行结果和真实语义完全相同。 -/
theorem sim {g : List NodeP} {g' : CFG} (he : Enc g g') :
    ∀ (n pc : Nat) (s : St) (cs : List Bool), runP g n pc s cs ≠ .halt →
      run g' n pc s cs = lift (runP g n pc s cs)
  | 0, pc, s, cs, _ => by simp [runP, run, lift]
  | n + 1, pc, s, cs, hn => by
    have e := he pc
    cases hg : g[pc]? with
    | none =>
      have e' : g'[pc]? = none := by simpa [encAt, hg] using e
      simp [runP, run, hg, e', lift]
    | some nd =>
      by_cases hh : nd.halt = true
      · exfalso
        apply hn
        simp [runP, hg, hh]
      · have e' : g'[pc]? = some nd.nd := by simpa [encAt, hg, hh] using e
        cases hs : stepOp s nd.nd.op with
        | none => simp [runP, run, hg, hh, e', hs, lift]
        | some s' =>
          cases hp : pick nd.nd.succ cs with
          | none =>
            cases hrs : nd.nd.raise <;> simp [runP, run, hg, hh, e', hs, hp, hrs, lift]
          | some tc =>
            obtain ⟨t, cs'⟩ := tc
            have hn' : runP g n t s' cs' ≠ .halt := by
              intro c
              apply hn
              simp [runP, hg, hh, hs, hp, c]
            have ih := sim he n t s' cs' hn'
            simp [runP, run, hg, hh, e', hs, hp, ih]

/-- **结论**：编码后的 CFG 通过验证，则含 `panic` 的程序执行不出错；正常或出错离开时干净。
    走到 `panic`（`.halt`）时进程直接结束，不作要求。 -/
theorem panic_safe (N : Nat) {g : List NodeP} {g' : CFG} (he : Enc g g')
    (A : Nat → Option (Nat × Core.Unified.RegionDefs.S4)) (h : cfgOk N g' A = true) (fuel : Nat) (cs : List Bool) :
    runP g fuel 0 St.empty cs ≠ .err ∧
    (∀ st cs', runP g fuel 0 St.empty cs = .ok st cs' → Clean N st) ∧
    (∀ st cs', runP g fuel 0 St.empty cs = .exn st cs' → Clean N st) := by
  obtain ⟨h1, h2, h3⟩ := Core.FlowGraph.Region.safety_and_no_leak N g' A h fuel cs
  refine ⟨fun e => ?_, fun st cs' e => ?_, fun st cs' e => ?_⟩
  · have := sim he fuel 0 St.empty cs (by rw [e]; exact fun c => ResP.noConfusion c)
    rw [e] at this
    exact h1 this
  · have := sim he fuel 0 St.empty cs (by rw [e]; exact fun c => ResP.noConfusion c)
    rw [e] at this
    exact h2 st cs' this
  · have := sim he fuel 0 St.empty cs (by rw [e]; exact fun c => ResP.noConfusion c)
    rw [e] at this
    exact h3 st cs' this

/-! ## 例子（线性值用 1）

`let t = new()` 之后直接正常结束：线性值没有被消费，拒绝。
`let t = new()` 之后 `panic`：编码成指向自己的空节点，接受——panic 不要求消费线性值。 -/

def leakEx : CFG := [⟨Core.FlowGraph.Region.lnew 1, [1], false⟩, ⟨.nop, [], false⟩]
def panicEx : CFG := [⟨Core.FlowGraph.Region.lnew 1, [1], false⟩, ⟨.nop, [1], false⟩]

#eval (Core.FlowGraph.Lower.acceptsF 2 leakEx, Core.FlowGraph.Lower.acceptsF 2 panicEx)

end Core.FlowGraph.Panic
