import os
import pprint
import re
from numpy import array, zeros, delete, savetxt, amax, sum, all, str, count_nonzero, vstack
from statistics import mean
from natsort import natsorted
import argparse

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

def writer(file, entries):
    file.write(' & '.join([str(entrie) if entrie != 0 else '' for entrie in entries]))
    file.write(' \\\\  \n')


def table_writer(file, top_row, left_column, list_of_matrices, func_last):
    file.write('\\centering \n')
    file.write('\\begin{adjustbox}{width=\\columnwidth,center} \n')
    alignment = ' c'
    file.write('\\begin{tabular}' + '{@{}' + f'{ alignment*len(top_row) }' + '@{}}' + '\n')

    writer(file, top_row)
    file.write('\hline \n')

    offset = 0
    for matrix_idx, matrix in enumerate(list_of_matrices):
        if matrix.size:
            if matrix.shape[0] == matrix.size:
                writer(file, [left_column[offset]] + list(matrix) + [func_last(1.*matrix)])
                offset += 1

            else:
                for k in range(matrix.shape[0]):
                    writer(file, [left_column[offset + k]] + list(matrix[k, :]) + [func_last(1.*matrix[k, :])])
                offset += matrix.shape[0]

            if matrix_idx < len(list_of_matrices):
                file.write('\hline \n')

    file.write('\\end{tabular} \n')
    file.write('\\end{adjustbox} \n')


def count_all(code_submission, column, result_numbers, result_numbers_functors, line_numbers):
    for line in code_submission:
        line_numbers[column] += counting(line)
        line_no_comment = re.split('//', line)[0]

        if not line_no_comment.strip():
            continue

        for idx in range(len(func_names)):
            pattern1 = f'(^|[\W]){func_names[idx]}([\W]|$)'
            result_numbers[idx, column] += len(re.findall(pattern1, line_no_comment))

        for idx in range(len(functor_names)):
            pattern2 = f'(^|[\W]){functor_names[idx]}([\W]|$)'
            result_numbers_functors[idx, column] += len(re.findall(pattern2, line_no_comment))

def remove_zeros(names, numbers):
    keep = ~all(numbers==0, axis=len(numbers.shape)-1)
    names = names[keep]
    numbers = numbers[keep]
    return names, numbers


# path = '../summer18/contest/'
# path = '../winter19/contest/'
# path = './top10submissions/winter19/'
# path = './top10submissions/summer18/'
# path = './temp/'

parser = argparse.ArgumentParser()
parser.add_argument('-path', type=str, required=True)

args = parser.parse_args()
print(args.path)
assert(args.path in ['../summer18/contest/',
                     '../winter19/contest/', 
                     './top10submissions/winter19/',
                     './top10submissions/summer18/'])

path = args.path

kind = {'Q#':'.qs', 'Silq':'.slq'}['Q#']

func_names = []
if kind == '.qs':
    with open('func_names.txt', 'r') as file:
        func_names = [line.strip() for line in file if line.strip() != '']

    with open('white_list.txt', 'r') as file:
        white_list = [line.strip() for line in file if line.strip() != '']

    func_names = list(set(func_names).difference(set(white_list)))
    func_names.sort()
    # func_names = func_names[260:280]
    func_names = array(func_names)

    functor_names = array(['Adjoint', 'Controlled', 'adjoint self',
                    'adjoint auto', 'controlled auto', 'controlled adjoint auto'])

elif kind == '.slq':
    func_names = array(['dup', 'forget', 'H', 'measure', 'phase', 'reverse', 'rotX', 'rotY', 'rotZ', 'X', 'Y', 'Z'])
    functor_names = array(['mfree', 'qfree', 'lifted'])


# Standard quantum gates
classical_gates_list = ['CCNOT', 'CNOT', 'H', 'R1', 'Rx', 'Ry', 'Rz', 'S', 'SWAP', 'T', 'X', 'Y', 'Z'] + ['rotX', 'rotY', 'rotZ']

if path == './top10submissions/summer18/' or path == './top10submissions/winter19/':
    directory = list(set(os.listdir(path)).difference({'evals'}))[0]
    contestants = len([file for file in os.listdir(os.path.join(path, directory)) if file.endswith(kind)])

    result_numbers_comm = zeros([func_names.size, contestants], dtype=int)
    result_numbers_functors_comm = zeros([functor_names.size, contestants], dtype=int)
    line_numbers_comm = zeros(contestants, dtype=int)


    for directory in os.listdir(path):
        print(directory)

        files = natsorted([file for file in os.listdir(os.path.join(path,directory)) if file.endswith(kind)])

        if len(files) == 0:
            continue

        result_numbers = zeros([func_names.size, len(files)], dtype=int)
        result_numbers_functors = zeros([functor_names.size, len(files)], dtype=int)
        line_numbers = zeros(len(files), dtype=int)

        for column_idx, file_name in enumerate(files):
            print(file_name)
            with open(os.path.join(path,directory,file_name), 'r') as code_submission:
                count_all(code_submission, column_idx, result_numbers, result_numbers_functors, line_numbers)

        result_numbers_comm += result_numbers
        result_numbers_functors_comm += result_numbers_functors
        line_numbers_comm += line_numbers


        result_names, result_numbers = remove_zeros(func_names, result_numbers)
        result_name_functors, result_numbers_functors = remove_zeros(functor_names, result_numbers_functors)

        with open(os.path.join(path, 'evals', f'{directory}_eval.tex'), 'w') as output_file:
            table_writer(file = output_file,
                        top_row = [''] + [file[:-len(kind)] for file in files] + ['average'],
                        left_column = ['\code{'+rn+'}' for rn in list(result_names)] + 
                                      ['\code{'+rnf+'}' for rnf in list(result_name_functors)] + 
                                      ['Lines of code'],
                        list_of_matrices = [result_numbers, result_numbers_functors, line_numbers],
                        func_last = mean)


    result_names_comm, result_numbers_comm = remove_zeros(func_names, result_numbers_comm)
    result_name_functors_comm, result_numbers_functors_comm = remove_zeros(functor_names, result_numbers_functors_comm)
    
    classical_gates_list = list(set(result_names_comm).intersection(set(classical_gates_list)))
    classical_gates_idxs = [list(result_names_comm).index(classical_gate) for classical_gate in classical_gates_list]

    with open(os.path.join(path, 'evals', 'all_eval.tex'), 'w') as output_file:
        table_writer(file=output_file,
                    top_row=[''] + [k for k in range(1,1+contestants)] + ['average'],
                    left_column=['\code{' + rn + '}' for rn in list(result_names_comm)] +
                                ['\code{' + rnf + '}' for rnf in list(result_name_functors_comm)] +
                                ['Primitives', 'Functors', 'Standard quantum gates', 'Lines of code'],
                    list_of_matrices=[result_numbers_comm,
                                    result_numbers_functors_comm,
                                    vstack([count_nonzero(result_numbers_comm, axis=0), # 'Primitives'
                                            count_nonzero(result_numbers_functors_comm,axis=0), # 'Functors'
                                            sum(result_numbers_comm[classical_gates_idxs], axis=0), # 'Standard quantum gates'
                                            line_numbers_comm])], # 'Lines of Code'
                    func_last=mean)
else:
    files = natsorted([file for file in os.listdir(os.path.join(path)) if file.endswith(kind)])

    result_numbers = zeros([func_names.size, len(files)], dtype=int)
    result_numbers_functors = zeros([functor_names.size, len(files)], dtype=int)
    line_numbers = zeros(len(files), dtype=int)


    for column_idx, file_name in enumerate(files):
        print(file_name)
        with open(os.path.join(path,file_name), 'r') as code_submission:
            count_all(code_submission, column_idx, result_numbers, result_numbers_functors, line_numbers)

    result_names, result_numbers = remove_zeros(func_names, result_numbers)
    result_name_functors, result_numbers_functors = remove_zeros(functor_names, result_numbers_functors)

    classical_gates_list = list(set(result_names).intersection(set(classical_gates_list)))
    classical_gates_idxs = [list(result_names).index(classical_gate) for classical_gate in classical_gates_list]

    with open(os.path.join(path, 'eval.tex'), 'w') as output_file:
            table_writer(file = output_file,
                        top_row = [''] + [file[:-len(kind)] for file in files] + ['Sum'],
                        left_column = ['\code{'+rn+'}' for rn in list(result_names)] + 
                                      ['\code{'+rnf+'}' for rnf in list(result_name_functors)] + 
                                      ['Standard quantum gates', 'Lines of code'],
                        list_of_matrices = [result_numbers,
                                            result_numbers_functors, # 'Functors'
                                            vstack([sum(result_numbers[classical_gates_idxs], axis=0), # 'Standard quantum gates'
                                                    line_numbers])], # 'Lines of Code'
                        func_last = sum)