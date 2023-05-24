import os
import sys

#########################

def extract_filename(path):
    ex_fn = os.path.basename(path)
    return os.path.splitext(ex_fn)[0]

def fellas(text, substring): # finds empty lines after substring
    i = text.find(substring)
    empty_line_index = text.find('\n', i)

    if empty_line_index != -1:
        return empty_line_index + 1

    return -1

def replace_impl_with_not(text):
    impl = '=>'
    i = text.find(impl)
    while i != -1:
        open_branch = text.find('(', i)
        br_cnt = 1
        while br_cnt > 0:
            open_branch += 1
            if text[open_branch] == ')':
                br_cnt -= 1
            elif text[open_branch] == '(':
                br_cnt += 1

        open_branch += 1
        begining = text.find('(', open_branch + 1)
        begining_open_branch = open_branch + 1
        hd_cnt = 1
        while hd_cnt > 0:
            open_branch += 1
            if text[open_branch] == ')':
                hd_cnt -= 1
            elif text[open_branch] == '(':
                hd_cnt += 1
        end = text.find('\n', open_branch + 1)
        if begining >= end:
            begining = begining_open_branch
            end = text.find('\n', begining + 1)
            begining += 6
        else:
            end -= 6

        text = text[:begining] + '(not ' + text[begining:end] + ')' + text[end:]
        text = text[:i] + 'and' + text[i + 2:]
        i = text.find(impl)
    return text

def remove_unary_conjuctions(text):
    i = text.find('(and', 0)
    while i != -1:
        termNum = 0
        termPos = 0
        br_cnt = 0
        j = i+4
        while text[j] != ')' or br_cnt > 0:
            if (not text[j].isspace()) and br_cnt == 0:
                termNum += 1
                termPos = j
                if not text[j] == '(':
                    j = text.find(' ', j)

            if text[j] == '(':
                br_cnt += 1
            elif text[j] == ')':
                br_cnt -= 1

            j += 1

        if termNum == 1:
            next = text.find('(', j)
            text = text[:i] + text[termPos:j] + text[next:]

        i = text.find('(and', i+1)

    return text

def add_variables(bm, fun_def, theory):
    free_variables = set()
    free_variables_types = dict()
    fl = "forall"
    i = first_srt
    while i != -1:
        i = bm.find(fl, i)
        if i != -1:
            is_variable = 0
            variable = ""
            while bm[i] != '\n':
                i += 1
                if bm[i] != '\n' and bm[i] != '(' and bm[i] != ')' and bm[i] != ' ':
                    if is_variable == 1:
                        variable += bm[i]
                elif bm[i] == '(':
                    is_variable = 1
                else:
                    is_variable = 0
                    if variable != "":
                        free_variables.add(variable)
                        closed_br = bm.find(")", i)
                        var_type = bm[i:closed_br]
                        free_variables_types[variable] = var_type
                        variable = ""
            i += 1

    bench_with_all_defs = bm[:position] + "\n" + fun_def + "\n"

    for variable in free_variables:
        v_type = free_variables_types[variable]
        bench_with_all_defs += f"(declare-fun " + variable + " () " + v_type + ")\n"

    bench_with_all_defs += bm[first_srt:]
    buff_b = bench_with_all_defs.replace("(set-logic HORN)", "(set-logic " + theory + ")")

    i = buff_b.find(fl, first_srt)

    while i != -1:
        if buff_b[i-3] == ")":
            i = buff_b.find(fl, i+1)
            continue
        opn = i - 1
        count = 1
        while count > 0:
            opn += 1
            if buff_b[opn] == ')':
                count -= 1
            elif buff_b[opn] == '(':
                count += 1
        next_index = buff_b.find('\n', i)
        buff_b = buff_b[:i-4] + buff_b[next_index:opn-3] + buff_b[opn + 1:]
        i = buff_b.find(fl, i)

    return buff_b

#########################

chc_file_path = sys.argv[1]
chc_out_file_path = sys.argv[2]
smt_theory = sys.argv[3]

chc_file = open(chc_out_file_path, mode='r')
chc_file_string = chc_file.read()
chc_file.close()

chc_solver_result_lines = chc_file_string.splitlines()[1:]
chc_interpretation_definition = "\n".join(chc_solver_result_lines)

with open(chc_file_path, 'r') as f:
    buff_bench = f.read()

position = fellas(buff_bench, "set-logic HORN")
assert (position != -1)

buff_bench = replace_impl_with_not(buff_bench)
buff_bench = remove_unary_conjuctions(buff_bench)

srt = "(assert"
num_of_srt = 0
index = buff_bench.find(srt)
first_srt = index - 2

while index != -1:
    cnt = 1
    op = index
    while cnt > 0:
        op += 1
        if buff_bench[op] == ')':
            cnt -= 1
        elif buff_bench[op] == '(':
            cnt += 1

    cur_bench = buff_bench[:first_srt] + "\n" + buff_bench[index - 1:op + 1] + "\n(check-sat)\n(exit)\n"
    cur_bench = add_variables(cur_bench, chc_interpretation_definition, smt_theory)

    file_folder = extract_filename(chc_file_path)

    witness = f"new_bench_" + str(num_of_srt) + ".smt2"

    with open(witness, 'w') as nb:
        nb.write(cur_bench)

    index = buff_bench.find(srt, index + 1)
    num_of_srt += 1