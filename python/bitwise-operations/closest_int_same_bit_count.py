# A little math leads to the correct approach. Suppose we flip the bit at
# index k1 and flip the bit at index k2, k1 > k2. Then the absolute value of
# the difference between the original integer and the new one is 2^k1 - 2^k2.
# To minimize this, we should make k1 as small as possible and k2 as close to
# k1.

# Since we must preserve the weight, the bit at index k1 has to be different
# from the bit in k2, otherwise the flips lead to an integer with different
# weight. This means the smallest k1 is the rightmost bit that's different from
# the LSB, and k2 must be the very next bit. In summary, the correct approach
# is to swap the two rightmost consecutive bits that differ.
def closest_int_same_bit_count(n):
    NUM_UNSIGNED_BITS = 64
    for i in range(0, NUM_UNSIGNED_BITS):
        if (n >> i) & 1 != (n >> (i + 1)) & 1:
            bit_mask = (1 << i) | (1 << (i + 1))
            return n ^ bit_mask

    raise ValueError('All bits are 0 or 1')
