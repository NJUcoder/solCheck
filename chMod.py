import os
import json

list = json.load(open('solc/list.json'))

for v in list["builds"]:
    solcPath = 'solc/' + v["path"]
    cmd = 'chmod +x ' + solcPath
    print(cmd)
    os.system(cmd)