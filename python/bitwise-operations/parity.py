# compute the parity of a non-negative integer
# returns 1 if the number of 1s is odd; otherwise returns 0

def parity_brute_force(n):
    result = 0

    while (n > 0):
        result = result ^ (n & 1)
        n   = n >> 1

    return result

def parity_erase_lowest_set_bit(n):
    result = 0

    while (n > 0):
        result = result ^ 1
        n      = n & (n - 1)

    return result

MASK_SIZE          = 16
BIT_MASK           = 0xFFFF
PRECOMPUTED_PARITY = []

def populate_cache():
    for i in range(0, 2 ** MASK_SIZE):
        PRECOMPUTED_PARITY.append(parity_erase_lowest_set_bit(i))

    return

populate_cache()

def parity_cached_result(n):
    return (PRECOMPUTED_PARITY[ n >> (3 * MASK_SIZE)            ] ^
            PRECOMPUTED_PARITY[(n >> (2 * MASK_SIZE)) & BIT_MASK] ^
            PRECOMPUTED_PARITY[(n >>      MASK_SIZE)  & BIT_MASK] ^
            PRECOMPUTED_PARITY[ n                     & BIT_MASK])

def parity_xor(n):
    n = n ^ (n >> 32)
    n = n ^ (n >> 16)
    n = n ^ (n >> 8)
    n = n ^ (n >> 4)
    n = n ^ (n >> 2)
    n = n ^ (n >> 1)
    return n & 1
