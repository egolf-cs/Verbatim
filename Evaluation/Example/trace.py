from os import listdir
from statistics import mean, stdev
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
import numpy as np
import json
import math

def fcontent(f):
    tmp = open(f, "r")
    content = tmp.read()
    tmp.close()
    return content

input_dir = "data"
fs = listdir(input_dir)
fs.sort(key = lambda x: int(x[:x.find(".")]))
print(fs)
fs = [input_dir+"/"+f for f in fs]
cs = [fcontent(f) for f in fs]

xs = [len(c) for c in cs]

input_dir = "trace/use"
fs = listdir(input_dir)
fs.sort(key = lambda x: int(x[:x.find(".")]))
print(fs)
fs = [input_dir+"/"+f for f in fs]
cs = [fcontent(f) for f in fs]

ys = [c.count("\n") for c in cs]

fig = plt.figure(figsize=(6,3))
axis = fig.add_subplot(1, 1, 1)

axis.scatter(xs,ys)
print(list(zip(xs,ys)))

axis.set_xlabel("# Characters")
axis.set_ylabel("Traced Operations")

plt.tight_layout()
plt.show()
