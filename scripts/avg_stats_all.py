import os
import sys
import subprocess

###########################

if not os.path.exists("../results/logs"): os.makedirs("../results/logs")

print("---------------------------------------------- CHC solvers (LIA-lin)")
subprocess.run(["python3", "avg_stats_chc_solver.py", "LIA-lin"])
print("---------------------------------------------- CHC solvers (LIA-nonlin)")
subprocess.run(["python3", "avg_stats_chc_solver.py", "LIA-nonlin"])
print("---------------------------------------------- CHC solvers (LIA-Arrays-lin)")
subprocess.run(["python3", "avg_stats_chc_solver.py", "LIA-Arrays-lin"])
print("---------------------------------------------- CHC solvers (LIA-Arrays-nonlin)")
subprocess.run(["python3", "avg_stats_chc_solver.py", "LIA-Arrays-nonlin"])

print("---------------------------------------------- SMT solvers (LIA-lin)")
subprocess.run(["python3", "avg_stats_smt_solver.py", "LIA-lin"])
print("---------------------------------------------- SMT solvers (LIA-nonlin)")
subprocess.run(["python3", "avg_stats_smt_solver.py", "LIA-nonlin"])
print("---------------------------------------------- SMT solvers (LIA-Arrays-lin)")
subprocess.run(["python3", "avg_stats_smt_solver.py", "LIA-Arrays-lin"])
print("---------------------------------------------- SMT solvers (LIA-Arrays-nonlin)")
subprocess.run(["python3", "avg_stats_smt_solver.py", "LIA-Arrays-nonlin"])

print("---------------------------------------------- SMT checkers (LIA-lin)")
subprocess.run(["python3", "avg_stats_smt_checker.py", "LIA-lin"])
print("---------------------------------------------- SMT checkers (LIA-nonlin)")
subprocess.run(["python3", "avg_stats_smt_checker.py", "LIA-nonlin"])
print("---------------------------------------------- SMT checkers (LIA-Arrays-lin)")
subprocess.run(["python3", "avg_stats_smt_checker.py", "LIA-Arrays-lin"])
print("---------------------------------------------- SMT checkers (LIA-Arrays-nonlin)")
subprocess.run(["python3", "avg_stats_smt_checker.py", "LIA-Arrays-nonlin"])
