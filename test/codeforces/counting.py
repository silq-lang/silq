import os
import pprint
import re
from numpy import array, zeros, delete, savetxt

def counting(s):
    s = s.strip()
    if 'namespace ' in s:
        return -1
    if 'open Microsoft.' in s:
        return 0
    if s[:2] == '//':
        return 0
    if s == '':
        return 0
    else:
        return 1



# path = './summer18/contest/'
# path = './top10submissions/winter19/'
path = './top10submissions/summer18/'

kind = {'Q#':'.qs', 'HQL':'.hql'}['Q#']

# Load function names:

# if kind == '.qs':
func_names_file = open('func_names.txt', 'r')
func_names = [line.strip() for line in func_names_file if line.strip()!='']
func_names_file.close()

func_names = list(dict.fromkeys(func_names))
func_names.sort()

# for line in func_names_file:
#     if line.strip() != '':
#         func_names.append(line.strip())

white_list_file = open('white_list.txt', 'r')
white_list = [line.strip() for line in white_list_file if line.strip() != '']
white_list_file.close()

functor_names = ['Adjoint', 'Controlled', 'adjoint self',
                 'adjoint auto', 'controlled auto', 'controlled adjoint auto']

for directorie in os.listdir(path):
    print(directorie)
    num_func_submissions = []
    keepers = [False] * len(func_names)

    files = os.listdir(os.path.join(path,directorie))
    files = [int(file[:-len(kind)]) for file in files if file.endswith(kind)]
    files.sort()
    file_names = [str(file) for file in files]
    files = [file_name+kind for file_name in file_names]

    result_numbers = zeros([len(func_names), len(files)], dtype=int)

    result_numbers_functors = zeros([len(functor_names), len(files)], dtype=int)

    line_numbers = [0] * len(files)

    for file_idx, file in enumerate(files):
        print(file)
        code_submission = open(os.path.join(path,directorie,file), 'r')

        for line in code_submission:
            line_numbers[file_idx] += counting(line)
            line_no_comment = re.split('//', line)[0]

            for idx in range(0, len(func_names)):
                pattern = f'(^|[\W]){func_names[idx]}([\W]|$)'
                occurences = len(re.findall(pattern, line_no_comment))
                if occurences:
                    result_numbers[idx, file_idx] += occurences
                    keepers[idx] = True


            for idx in range(0, len(functor_names)):
                pattern = f'(^|[\W]){functor_names[idx]}([\W]|$)'
                occurences = len(re.findall(pattern, line_no_comment))
                if occurences:
                    result_numbers_functors[idx, file_idx] += occurences


    for white_listed in white_list:
        keepers[func_names.index(white_listed)] = False

    keep = [k for k, b in enumerate(keepers) if b]
    result_numbers = result_numbers[keep,:]
    result_names = array(func_names)[keep]

    output_file = open(os.path.join(path,'evals', f'{directorie}_eval.tex'),'w')
    output_file.write(' && ' + ' && '.join(file_names) + '\n')
    for k in range(0, len(result_names)):
        output_file.write('\code{'+result_names[k] + '} && ' + ' && '.join([str(x) for x in result_numbers[k,:]]) + '\n')
    output_file.write('\hline \n')
    for k in range(0, len(functor_names)):
        output_file.write('\code{' + functor_names[k] + '} &&' + ' && '.join([str(x) for x in result_numbers_functors[k,:]]) + '\n')
    output_file.write('\hline \n')
    output_file.write('\code{Line numbers} &&' + ' && '.join([str(x) for x in line_numbers]))
    output_file.close()







