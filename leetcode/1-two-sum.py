# brute force solution
# def twoSum(ms, n):
#     return [(i, j) for i in range(0,   len(ms))
#                    for j in range(i+1, len(ms))
#                    if ms[i] + ms[j] == n]

def twoSum(ms, n):
    d = {}

    for i, m in enumerate(ms):
        complement = n - m

        if complement in d:
            return (d[complement], i)
        else:
            d[m] = i

    return []
