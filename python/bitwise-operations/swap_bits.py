def swap_bits(n, i, j):
    if (n >> i) & 1 != (n >> j) & 1:
        bit_mask = (1 << i) | (i << j)
        return n ^ bit_mask
    else:
        return n
