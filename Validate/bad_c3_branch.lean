-- 由 sinterc --emit=core 生成，不要手工修改。
import Core.C5
set_option maxRecDepth 100000
open Core.M7h

/-- begin -/
def f0 : CFG := [
  ⟨.nop, [1, 4], false⟩,
  ⟨.cmd (.base (.lin (.lnew 0))), [2], false⟩,
  ⟨.cmd (.base (.lin (.consume 0))), [3], false⟩,
  ⟨.nop, [], true⟩,
  ⟨.nop, [5], false⟩,
  ⟨.cmd (.base (.lin (.lnew 1))), [6], false⟩,
  ⟨.cmd (.base (.lin (.consume 1))), [7], false⟩,
  ⟨.cmd (.base (.lin (.lnew 2))), [8], false⟩,
  ⟨.cmd (.base (.lin (.lmove 2 3))), [9], false⟩,
  ⟨.cmd (.base (.lin (.consume 3))), [10], false⟩,
  ⟨.nop, [], false⟩]

/-- check -/
def f1 : CFG := [
  ⟨.nop, [1, 2], false⟩,
  ⟨.nop, [], true⟩,
  ⟨.nop, [3], false⟩,
  ⟨.nop, [], false⟩]

/-- commit -/
def f2 : CFG := [
  ⟨.cmd (.base (.lin (.lnew 0))), [1], false⟩,
  ⟨.cmd (.base (.lin (.consume 0))), [2], false⟩,
  ⟨.nop, [], false⟩]

/-- rollback -/
def f3 : CFG := [
  ⟨.cmd (.base (.lin (.lnew 0))), [1], false⟩,
  ⟨.cmd (.base (.lin (.consume 0))), [2], false⟩,
  ⟨.nop, [], false⟩]

/-- main -/
def f4 : CFG := [
  ⟨.nop, [], false⟩]

/-- f -/
def f5 : CFG := [
  ⟨.cmd (.base (.lin (.lnew 0))), [1], false⟩,
  ⟨.cmd (.base (.lin (.lmove 0 1))), [2], false⟩,
  ⟨.nop, [3, 5], false⟩,
  ⟨.cmd (.base (.lin (.consume 1))), [4], false⟩,
  ⟨.nop, [6], false⟩,
  ⟨.nop, [6], false⟩,
  ⟨.nop, [], false⟩]

#eval Core.C5.report [("begin", 4, f0), ("check", 1, f1), ("commit", 1, f2), ("rollback", 1, f3), ("main", 1, f4), ("f", 2, f5)] false
