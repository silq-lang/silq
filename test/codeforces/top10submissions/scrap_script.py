import requests
import os, shutil
from bs4 import BeautifulSoup


contestID = 1002
startrank = 1
endrank = 10
competition_name = {1002 : "summer18", 1116 : "winter19"}[contestID]

url_overview = 'https://codeforces.com/api/contest.standings?' \
               f'contestId={contestID}&from={startrank}&count={endrank}'

data = requests.get(url_overview).json()

assert(data['status'] == 'OK')
assert(data['result']['contest']['id'] == contestID)



problems = [problem['index'] for problem in data['result']['problems']]

rows = data['result']['rows']

participants = [row['party']['members'][0]['handle'] for row in rows]

try:
    os.mkdir(f'{competition_name}')
except:
    shutil.rmtree(f'{competition_name}')
    os.mkdir(f'{competition_name}')

for problem in problems:
    os.mkdir(f'{competition_name}/{problem}')

for rank, name in enumerate(participants):
    url_submissions = 'https://codeforces.com/api/contest.status?' \
                      f'contestId={contestID}&handle=%22{name}%22'

    submissions = requests.get(url_submissions).json()
    assert(submissions['status'] == 'OK')

    ids = {}
    for submission in submissions['result']:
        if not (submission['problem']['index'] in ids) and submission['verdict'] == 'OK':
            ids.update({submission['problem']['index'] : submission['id']})


    # os.mkdir(f'{competition_name}/{rank+1}')
    for problem in problems:
        url_id = 'https://codeforces.com/contest/' \
                 f'{contestID}/submission/{ids[problem]}'

        # print(url_id)

        page = requests.get(url_id)
        soup = BeautifulSoup(page.text, "lxml")

        # print(page.text)

        extract = str(soup.pre.string)

        file = open(f'{competition_name}/{problem}/{rank+1}.qs', "w+")
        file.write(extract)
        file.close()
