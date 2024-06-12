import os
import sys

###########################

def get_avg(stat, chc_solver, target):
    inputFileName="_" + stat + "_"+ chc_solver + "_" + target + ".dataPoints"
    path = "../results/witnesses_" + chc_solver + "_" + target + "/" + inputFileName

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
            print("Avg " + stat + " for " + chc_solver + " " + target + ": " + str(statSum) + " / " + str(statNum) + " = " + str(statSum/statNum))
        else:
            print("Avg " + stat + " for " + chc_solver + " " + target + ": " + str(statSum) + " / " + str(statNum) + " = " + "0")

        statFile.close()
    else:
        print("No " + stat + " for " + chc_solver + " " + target)

def set_target(stat, chc_solver):
    if specificTarget != "":
        get_avg(stat, chc_solver, specificTarget)
    else:
        get_avg(stat, chc_solver, "LIA-lin")
        get_avg(stat, chc_solver, "LIA-nonlin")
        get_avg(stat, chc_solver, "LIA-Arrays-lin")
        get_avg(stat, chc_solver, "LIA-Arrays-nonlin")

def set_chc_solver(stat):
    set_target(stat, "eldarica")
    set_target(stat, "golem")
    set_target(stat, "spacer")

def set_stat():
    print("----------------- runtime (s)")
    set_chc_solver("runtime")
    print("-------------- memory-use (KB)")
    set_chc_solver("memory-use")
    print("------------ witness-size (B)")
    set_chc_solver("witness-size")

def avg_all():
    set_stat()

###########################

specificTarget = sys.argv[1]

avg_all()
