import re
import sys

RESULT_RE=re.compile("\s([a-z0-9_-]+\.c):([0-9]+):([0-9]+)")

input0=open(sys.argv[1], "r")
input1=open(sys.argv[2], "r")

results0=set()
results1=set()

for l0 in input0.readlines():
    res0=RESULT_RE.search(l0)
    if res0 is not None:
        results0.add((res0.group(1), int(res0.group(2))))
for l1 in input1.readlines():
    res1=RESULT_RE.search(l1)
    if res1 is not None:
        results1.add((res1.group(1), int(res1.group(2))))
print("results0-results1 (%d)" % (len(results0-results1)))
print(repr(results0-results1))

print("results1-results0 (%d) " % (len(results1-results0)))
print(repr(results1-results0))
