import os


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
        # print(s)
        return 1


#path = './summer18/contest/'
path = './winter19/contest/'

files = []
# r=root, d=directories, f = files
for r, d, f in os.walk(path):
    for file in f:
        if file[-3:]=='.qs':
            files.append(os.path.join(r, file))

# for file in files:
#     print(file)

names = [file[2:-3] for file in files]
names.sort()
# print(names)

num_lines = {}

for name in names:
    file = open(f'{name}.qs', 'r')

    counter = 0
    for line in file:
        counter += counting(line)

    num_lines.update({name:counter})

print(num_lines)