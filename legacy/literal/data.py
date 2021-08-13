import json
output_dir = "data"

def fcontent(f):
    tmp = open(f, "r")
    content = tmp.read()
    tmp.close()
    return content

c = fcontent("GDP4.json")
j = json.loads(c)

for i in range(2,len(j),20):
# for i in range(2,10,2):
    print(i)
    f = open(output_dir+"/"+str(i)+".json", "w")
    content = json.dumps(j[:i])
    f.write(content)
    f.close()
