import requests
from bs4 import BeautifulSoup


path = 'https://docs.microsoft.com/en-us/qsharp/api/qsharp/microsoft.quantum.'

topics = ['bitwise', 'convert', 'core', 'diagnostics', 'environment',
          'extensions.bitwise', 'extensions.convert', 'extensions.diagnostics'
          'extensions.math', 'extensions.testing', 'intrinsic', 'math', 'primitive',
          'AmplitudeAmplification', 'Arithmetic', 'Arrays', 'canon', 'characterization'
          'correction', 'measurement', 'oracles', 'preparation', 'simulation', 'chemistry'
          'chemistry.jordanwigner', 'chemistry.jordanwigner.vqe', 'research.chemistry',
          'research.randomwalkphaseestimation']


file = open("func_names.txt", "w")


for topic in topics:
    url = f'{path}{topic}?view=qsharp-preview'
    page = requests.get(url)
    soup = BeautifulSoup(page.text, 'lxml')

    for table in soup.find_all('table'):
        for row in table.find_all('tr'):
            file.write(row.td.a.string + '\n')

        file.write('\n')
    file.write('\n')
file.close()

