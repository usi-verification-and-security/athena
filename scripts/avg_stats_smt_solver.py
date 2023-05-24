import os
import sys

###########################

def get_avg(stat, smt_mode, smt_solver, chc_solver, target):
    inputFileName="_" + stat + "_"+ smt_solver + "_" + smt_mode + "_" + target + "_" + chc_solver + ".dataPoints"
    path = "../results/result_" + smt_solver + "_" + smt_mode + "_" + target + "_" + chc_solver + "/" + inputFileName

    if os.path.exists(path):
        logFile = open("../results/logs/" + inputFileName, mode="w+") # open file in write mode
        statFile = open(path,"r") # open file in read mode

        statSum = 0
        statNum = 0

        dataPoints = []

        for line in statFile.readlines():
            line_split = line.split()

            for i in range(0,len(line_split)):
                if i < 1:
                    continue
                if i == 1:
                    res = line_split[i]
                elif i == 2:
                    if res == "sat" or res == "unsat":
                        val = line_split[i]
                        if stat == "runtime":
                            statSum = statSum + float(val.split("+")[0]) + float(val.split("+")[1])
                            dataPoints.append(float(val.split("+")[0]) + float(val.split("+")[1]))
                        else:
                            statSum = statSum + float(val)
                            dataPoints.append(float(val))
                        statNum = statNum + 1
                elif i > 2:
                    sys.exit("Error: invalid format.")

        dataPoints.sort()
        pointCounter = 0
        for point in dataPoints:
            pointCounter = pointCounter + 1
            logFile.write(str(pointCounter) + " " + str(point) + "\n")

        if statNum > 0:
            print("Avg " + stat + " for " + smt_solver + " " + smt_mode + " " + target + " " + chc_solver + ": " + str(statSum) + " / " + str(statNum) + " = " + str(statSum/statNum))
        else:
            print("Avg " + stat + " for " + smt_solver + " " + smt_mode + " " + target + " " + chc_solver + ": " + str(statSum) + " / " + str(statNum) + " = " + "0")

        statFile.close()
    else:
        print("No " + stat + " for " + smt_solver + " " + smt_mode + " " + target + " " + chc_solver)

def set_target(stat, smt_mode, smt_solver, chc_solver):
    if specificTarget != "":
        get_avg(stat, smt_mode, smt_solver, chc_solver, specificTarget)
    else:
        get_avg(stat, smt_mode, smt_solver, chc_solver, "LIA-lin")
        get_avg(stat, smt_mode, smt_solver, chc_solver, "LIA-nonlin")

def set_chc_solver(stat, smt_mode, smt_solver):
    set_target(stat, smt_mode, smt_solver, "golem")
    set_target(stat, smt_mode, smt_solver, "eldarica")
    set_target(stat, smt_mode, smt_solver, "spacer")

def set_smt_solver(stat, smt_mode):
    set_chc_solver(stat, smt_mode, "opensmt")
    set_chc_solver(stat, smt_mode, "z3")
    set_chc_solver(stat, smt_mode, "verit")
    set_chc_solver(stat, smt_mode, "smtinterpol")
    if smt_mode == "proof":
        set_chc_solver(stat, smt_mode, "cvc5-lfsc")
        set_chc_solver(stat, smt_mode, "cvc5-alethe")
    else:
        set_chc_solver(stat, smt_mode, "cvc5")

def set_smt_mode(stat):
    if stat != "proof-size":
        set_smt_solver(stat, "proof")
        set_smt_solver(stat, "noProof")
    else:
        set_smt_solver(stat, "proof")

def set_stat():
    print("--------------- runtime (s)")
    set_smt_mode("runtime")
    print("------------ memory-use (KB)")
    set_smt_mode("memory-use")
    print("------------ proof-size (B)")
    set_smt_mode("proof-size")


def avg_all():
    set_stat()

###########################

specificTarget = sys.argv[1]

avg_all()