def threeSum(ns):
    if len(ns) < 3:
        return []

    ns.sort()

    result = []

    for i in range(len(ns) - 2):
        if i > 0 and ns[i] == ns[i-1]: continue

        l, r = i+1, len(ns)-1
        while l < r:
            sum = ns[i] + ns[l] + ns[r]
            if sum == 0:
                result.append((ns[i], ns[l], ns[r]))
                l, r = l+1, r-1
                while l < r and ns[l] == ns[l-1]: l = l+1
                while l < r and ns[r] == ns[r+1]: r = r-1
            elif sum < 0:
                l = l+1
            else:
                r = r-1

    return result
