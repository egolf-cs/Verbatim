from os import listdir
from statistics import mean, stdev
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
import numpy as np
import json
import math
input_dir = "results"

def fcontent(f):
    tmp = open(f, "r")
    content = tmp.read()
    tmp.close()
    return content

def poly_eq(coeffs):
    return lambda x: sum([coeffs[i]*(x**i) for i in range(0,len(coeffs))])


fs = listdir(input_dir)
fs.sort(key = lambda x: int(x[:x.find(".")]))
print(fs)
fs = [input_dir+"/"+f for f in fs]
# [:int(len(fs)/2)]
cs = [fcontent(f) for f in fs]
js = [json.loads(c) for c in cs]

for j in js:
    if j["rest_len"] != 0:
        print("WARNING: {} was not processed entirely".format(j["fname"]))

xs = [j["input_len"] for j in js]
ys = [mean(j["times"]) for j in js]
#e = [stdev(j["times"]) for j in js]
e = [0 for j in js]
for x in xs:
    print(x)
print("---")
for y in ys:
    print(y)

# for p in list(zip(xs,ys)):
#     print("{} {}".format(p[0], p[1]))

zs = np.polyfit(xs,ys,1)
f = poly_eq(zs[::-1])
# f = nlogn
fxs = np.arange(0,max(xs),100)
fys = [f(x) for x in fxs]

fig = plt.figure(figsize=(6,3))
axis = fig.add_subplot(1, 1, 1)

axis.plot(fxs,fys)
axis.errorbar(xs, ys, yerr=e, fmt='ro', ms=4)

axis.legend(["linear fit"])
axis.set_xlabel("# Characters")
axis.set_ylabel("Processing Time (s)")

plt.tight_layout()
plt.show()
