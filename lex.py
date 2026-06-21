def lex_smaller_eq(enc, vpool, seq1, seq2, maxcomparisons=None):
    """Ensure that seq1 is lexicographically smaller or equal than seq2"""
    assert len(seq1) == len(seq2)
    all_previous_equal = vpool.id()
    enc.append([+all_previous_equal])
    rcnt = 0
    for i in range(len(seq1)):
        if seq1[i] == seq2[i]:
            continue
        rcnt += 1
        enc.append([-all_previous_equal, -seq1[i], +seq2[i]])  # all previous equal implies seq1[i] <= seq2[i]
        all_previous_equal_new = vpool.id()
        enc.append([-all_previous_equal, -seq1[i], +all_previous_equal_new])
        enc.append([-all_previous_equal, +seq2[i], +all_previous_equal_new])
        all_previous_equal = all_previous_equal_new
        if maxcomparisons is not None and rcnt > maxcomparisons:
            break
    return enc


def lex_smaller_eq_guarded(enc, vpool, guard, seq1, seq2, maxcomparisons=None):
    """Ensure guard OR (seq1 is lexicographically smaller or equal than seq2)."""
    assert len(seq1) == len(seq2)
    guard = list(guard)
    all_previous_equal = vpool.id()
    enc.append(guard + [+all_previous_equal])
    rcnt = 0
    for i in range(len(seq1)):
        if seq1[i] == seq2[i]:
            continue
        rcnt += 1
        enc.append(guard + [-all_previous_equal, -seq1[i], +seq2[i]])
        all_previous_equal_new = vpool.id()
        enc.append(guard + [-all_previous_equal, -seq1[i], +all_previous_equal_new])
        enc.append(guard + [-all_previous_equal, +seq2[i], +all_previous_equal_new])
        all_previous_equal = all_previous_equal_new
        if maxcomparisons is not None and rcnt > maxcomparisons:
            break
    return enc
