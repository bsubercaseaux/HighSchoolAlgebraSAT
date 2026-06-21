import itertools  
   
def at_most_one_pairwise(lits):
    clauses = []
    for l1, l2 in itertools.combinations(lits, 2):
        clauses.append([-l1, -l2])
    return clauses

def exactly_one_pairwise(lits):
    return at_most_one_pairwise(lits) + [lits]
   
def at_most_one_recursive(lits, idpool, cut=4, auxiliary_placement='start'):
    if len(lits) <= cut:
        return at_most_one_pairwise(lits)
    new_var = idpool.id(f"aux_{idpool.top + 1}")
    clauses = at_most_one_recursive(lits[:cut-1] + [-new_var], idpool, cut, auxiliary_placement)
    if auxiliary_placement == 'end':
        clauses.extend(at_most_one_recursive(lits[cut-1:] + [new_var], idpool, cut, auxiliary_placement))
    else:
        clauses.extend(at_most_one_recursive([new_var] + lits[cut-1:], idpool, cut, auxiliary_placement))
    return clauses

def exactly_one_recursive(lits, idpool, cut=4, auxiliary_placement = 'start'):
    if len(lits) <= cut:
        return [lits] + at_most_one_pairwise(lits)
    else:
        new_var = idpool.id(f"aux_{idpool.top + 1}")
        clauses = exactly_one_recursive(lits[:cut-1] + [-new_var], idpool, cut, auxiliary_placement)
        if auxiliary_placement == 'end':
            clauses.extend(exactly_one_recursive(lits[cut-1:] + [new_var], idpool, cut, auxiliary_placement))
        else:
            clauses.extend(exactly_one_recursive([new_var] + lits[cut-1:], idpool, cut, auxiliary_placement))
    return clauses
