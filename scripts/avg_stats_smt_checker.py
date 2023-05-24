import os
import sys

###########################

def get_avg(stat, smt_checker, smt_solver, chc_solver, target):
    inputFileName="_" + stat + "_"+ smt_checker + "_" + target + "_" + smt_solver + "_" + chc_solver + ".dataPoints"
    path = "../results/result_" + smt_checker + "_" + target + "_" + smt_solver + "_" + chc_solver + "/" + inputFileName

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
                    if res == "verified":
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
            print("Avg " + stat + " for " + smt_checker + "_" + target + "_" + smt_solver + "_" + chc_solver + ": " + str(statSum) + " / " + str(statNum) + " = " + str(statSum/statNum))
        else:
            print("Avg " + stat + " for " + smt_checker + "_" + target + "_" + smt_solver + "_" + chc_solver + ": " + str(statSum) + " / " + str(statNum) + " = " + "0")

        statFile.close()
    else:
        print("No " + stat + " for " + smt_checker + "_" + target + "_" + smt_solver + "_" + chc_solver)

def set_target(stat, smt_checker, smt_solver, chc_solver):
    if specificTarget != "":
        get_avg(stat, smt_checker, smt_solver, chc_solver, specificTarget)
    else:
        get_avg(stat, smt_checker, smt_solver, chc_solver, "LIA-lin")
        get_avg(stat, smt_checker, smt_solver, chc_solver, "LIA-nonlin")

def set_chc_solver(stat, smt_checker, smt_solver):
    set_target(stat, smt_checker, smt_solver, "golem")
    set_target(stat, smt_checker, smt_solver, "eldarica")
    set_target(stat, smt_checker, smt_solver, "spacer")

def set_smt_solver(stat, smt_checker):
    if smt_checker == "tswc":
        set_chc_solver(stat, smt_checker, "opensmt")
    elif smt_checker == "lfsc":
        set_chc_solver(stat, smt_checker, "cvc5-lfsc")
    elif smt_checker == "carcara":
        set_chc_solver(stat, smt_checker, "cvc5-alethe")
    elif smt_checker == "smtinterpol-checker":
        set_chc_solver(stat, smt_checker, "smtinterpol")

def set_smt_checker(stat):
    set_smt_solver(stat, "tswc")
    set_smt_solver(stat, "lfsc")
    set_smt_solver(stat, "carcara")
    set_smt_solver(stat, "smtinterpol-checker")

def set_stat():
    print("--------------- runtime (s)")
    set_smt_checker("runtime")
    print("------------ memory-use (KB)")
    set_smt_checker("memory-use")

def avg_all():
    set_stat()

###########################

specificTarget = sys.argv[1]

avg_all()