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
  ⟨.cmd (.base (.own (.c (.base (.alloc 1))))), [6], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 1))))), [7], false⟩,
  ⟨.cmd (.base (.lin (.lnew 2))), [8], false⟩,
  ⟨.cmd (.base (.lin (.consume 2))), [9], false⟩,
  ⟨.cmd (.base (.lin (.lnew 3))), [10], false⟩,
  ⟨.cmd (.base (.lin (.lmove 3 4))), [11], false⟩,
  ⟨.cmd (.base (.lin (.consume 4))), [12], false⟩,
  ⟨.nop, [], false⟩]

/-- exec -/
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

/-- transfer -/
def f4 : CFG := [
  ⟨.cmd (.base (.lin (.lnew 0))), [1], false⟩,
  ⟨.nop, [2, 6], false⟩,
  ⟨.cmd (.base (.lin (.consume 0))), [3], false⟩,
  ⟨.cmd (.base (.lin (.lnew 1))), [4], false⟩,
  ⟨.cmd (.base (.lin (.lmove 1 2))), [5], false⟩,
  ⟨.nop, [8, 10], false⟩,
  ⟨.cmd (.base (.lin (.consume 0))), [7], false⟩,
  ⟨.nop, [], true⟩,
  ⟨.cmd (.base (.lin (.consume 2))), [9], false⟩,
  ⟨.nop, [], false⟩,
  ⟨.cmd (.base (.lin (.consume 2))), [11], false⟩,
  ⟨.nop, [], true⟩]

/-- report -/
def f5 : CFG := [
  ⟨.nop, [1, 4], false⟩,
  ⟨.nop, [3], false⟩,
  ⟨.nop, [3], false⟩,
  ⟨.nop, [], false⟩,
  ⟨.nop, [2], false⟩]

/-- main -/
def f6 : CFG := [
  ⟨.cmd (.base (.own (.c (.base (.alloc 0))))), [1], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 0))))), [2], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 1))))), [3], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.move 1 2))))), [4], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 2))))), [5], false⟩,
  ⟨.nop, [6, 14], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 2))))), [7], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.alloc 3))))), [8], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.use 3))))), [9], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 3))))), [10], false⟩,
  ⟨.nop, [13], false⟩,
  ⟨.cmd (.base (.own (.c (.base (.free 2))))), [12], false⟩,
  ⟨.nop, [13], false⟩,
  ⟨.nop, [], false⟩,
  ⟨.nop, [11], false⟩]

#eval Core.C5.report [("begin", 5, f0), ("exec", 1, f1), ("commit", 1, f2), ("rollback", 1, f3), ("transfer", 3, f4), ("report", 1, f5), ("main", 4, f6)] true
