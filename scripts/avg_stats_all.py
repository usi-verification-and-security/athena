import os
import sys
import subprocess

###########################

specificTarget = sys.argv[1]

if not os.path.exists("../results/logs"): os.makedirs("../results/logs")

print("---------------------------------------------- CHC solvers")
subprocess.run(["python3", "avg_stats_chc_solver.py", specificTarget])
print("---------------------------------------------- SMT solvers")
subprocess.run(["python3", "avg_stats_smt_solver.py", specificTarget])
print("---------------------------------------------- SMT checkers")
subprocess.run(["python3", "avg_stats_smt_checker.py", specificTarget])