import amo_encoder
import itertools
import argparse
import lex
from pysat.formula import CNF, IDPool


# create variables once for encoding/decoding
def operation_accessors(n, idpool):
    add = lambda i, j, k: idpool.id(f"add_{i}_{j}_{k}")
    mul = lambda i, j, k: idpool.id(f"mul_{i}_{j}_{k}")
    exp = lambda i, j, k: idpool.id(f"exp_{i}_{j}_{k}")

    symmetric_combs = [] # (i, j) with i <= j
    for i in range(1,n+1):
        symmetric_combs.extend([(i, j) for j in range(i, n+1)])

    # access add then mul then exp, to force variable ordering
    for i, j in symmetric_combs:
        for k in range(1, n+1):
            add(i, j, k)
    for i, j in symmetric_combs:
        for k in range(1, n+1):
            mul(i, j, k)
    for i, j in itertools.product(range(1,n+1), repeat=2):
        for k in range(1, n+1):
            exp(i, j, k)

    # commutativity of addition and multiplication is encoded by considering unordered pairs
    add_ = lambda i, j, k: add(min(i, j), max(i, j), k)
    mul_ = lambda i, j, k: mul(min(i, j), max(i, j), k)

    return add_, mul_, exp, symmetric_combs


def encode(n, force_exp_2_4_5=False):
    cnf = CNF()
    idpool = IDPool()
    add_, mul_, exp, symmetric_combs = operation_accessors(n, idpool)


    for i, j in symmetric_combs: 
        # tried recursive but it was worse than pairwise
        cnf.extend(amo_encoder.exactly_one_pairwise([add_(i, j, k) for k in range(1, n+1)]))
    for i, j in symmetric_combs:
        cnf.extend(amo_encoder.exactly_one_pairwise([mul_(i, j, k) for k in range(1, n+1)]))
    for i, j in itertools.product(range(1,n+1), repeat=2):
        cnf.extend(amo_encoder.exactly_one_pairwise([exp(i, j, k) for k in range(1, n+1)]))


    # x * 1 = x (HSI 3)
    for x in range(1,n+1):
        cnf.append([mul_(x, 1, x)])

    # 1^x = 1 (HSI 7)
    for x in range(1,n+1):
        cnf.append([exp(1, x, 1)])


    # x^1 = x (HSI 8)
    for x in range(1,n+1):
        cnf.append([exp(x, 1, x)])


    # associativity of addition (HSI 2)
    # add_2(i, j, k, l) := i+(j+k) = (i+j)+k = l
    add_2 = lambda i, j, k, l: idpool.id(f"add_2_{i}_{j}_{k}_{l}")
    for i, k in symmetric_combs:
        for j in range(1,n+1):
            cnf.extend(amo_encoder.at_most_one_pairwise([add_2(i, j, k, l) for l in range(1,n+1)]))
            for l, m in itertools.product(range(1,n+1), repeat=2):
                cnf.append([-add_(j, k, m), -add_(i, m, l), add_2(i, j, k, l)])
                cnf.append([-add_(i, j, m), -add_(m, k, l), add_2(i, j, k, l)])

    # associativity of multiplication (HSI 5)
    # mul_2(i, j, k, l) := i*(j*k) = (i*j)*k = l
    mul_2 = lambda i, j, k, l: idpool.id(f"mul_2_{i}_{j}_{k}_{l}")
    for i, k in symmetric_combs:
        for j in range(1,n+1):
            cnf.extend(amo_encoder.at_most_one_pairwise([mul_2(i, j, k, l) for l in range(1,n+1)]))
            for l, m in itertools.product(range(1,n+1), repeat=2):
                cnf.append([-mul_(j, k, m), -mul_(i, m, l), mul_2(i, j, k, l)])
                cnf.append([-mul_(i, j, m), -mul_(m, k, l), mul_2(i, j, k, l)])

    # distributivity of multiplication over addition (HSI 6)
    # x * (y+z) = x*y + x*z
    dist = lambda x, y, z, l: idpool.id(f"dist_{x}_{y}_{z}_{l}")
    for x in range(1,n+1):
        for y, z in symmetric_combs:
            cnf.extend(amo_encoder.at_most_one_pairwise([dist(x, y, z, l) for l in range(1,n+1)]))
            for l, m in itertools.product(range(1,n+1), repeat=2):
                cnf.append([-add_(y, z, m), -mul_(x, m, l), dist(x, y, z, l)])
            for l, m1, m2 in itertools.product(range(1,n+1), repeat=3):
                cnf.append([-mul_(x, y, m1), -mul_(x, z, m2), -add_(m1, m2, l), dist(x, y, z, l)])

    # HSI 9
    # x^(y+z) = x^y * x^z
    exp_add = lambda x, y, z, l: idpool.id(f"exp_add_{x}_{y}_{z}_{l}")
    for x in range(1,n+1):
        for y, z in symmetric_combs:
            cnf.extend(amo_encoder.at_most_one_pairwise([exp_add(x, y, z, l) for l in range(1,n+1)]))
            for l, m in itertools.product(range(1,n+1), repeat=2):
                cnf.append([-add_(y, z, m), -exp(x, m, l), exp_add(x, y, z, l)])
            for l, m1, m2 in itertools.product(range(1,n+1), repeat=3):
                cnf.append([-exp(x, y, m1), -exp(x, z, m2), -mul_(m1, m2, l), exp_add(x, y, z, l)])

    # exponent distributes over multiplication in the base (HSI 10)
    # (x*y)^z = x^z * y^z
    exp_mul = lambda x, y, z, l: idpool.id(f"exp_mul_{x}_{y}_{z}_{l}")
    for x, y in symmetric_combs:
        for z in range(1,n+1):
            cnf.extend(amo_encoder.at_most_one_pairwise([exp_mul(x, y, z, l) for l in range(1, n+1)]))
            for l, m in itertools.product(range(1, n+1), repeat=2):
                cnf.append([-mul_(x, y, m), -exp(m, z, l), exp_mul(x, y, z, l)])
            for l, m1, m2 in itertools.product(range(1, n+1), repeat=3):
                cnf.append([-exp(x, z, m1), -exp(y, z, m2), -mul_(m1, m2, l), exp_mul(x, y, z, l)])

    # exponent associativity (HSI 11)
    # (x^y)^z = x^(y*z)
    exp_2 = lambda x, y, z, l: idpool.id(f"exp_2_{x}_{y}_{z}_{l}")
    for x, y, z in itertools.product(range(1, n+1), repeat=3):
        cnf.extend(amo_encoder.at_most_one_pairwise([exp_2(x, y, z, l) for l in range(1, n+1)]))
        for l, m in itertools.product(range(1, n+1), repeat=2):
            cnf.append([-exp(x, y, m), -exp(m, z, l), exp_2(x, y, z, l)])
            cnf.append([-mul_(y, z, m), -exp(x, m, l), exp_2(x, y, z, l)])

   
    # Negation of Wilkies Identity:
    x = 4
    y = 5
    terms = [
        ('1+x', '+', 1, x),
        ('(1+x)^y', '^', '1+x', y),
        ('(1+x)^x', '^', '1+x', x),
        ('x^2', '*', x, x),
        ('1+x+x^2', '+', '1+x', 'x^2'),
        ('(1+x+x^2)^x', '^', '1+x+x^2', x),
        ('(1+x+x^2)^y', '^', '1+x+x^2', y),
        ('x^3', '*', 'x^2', x),
        ('1+x^3', '+', 1, 'x^3'),
        ('(1+x^3)^x', '^', '1+x^3', x),
        ('(1+x^3)^y', '^', '1+x^3', y),
        ('x^4', '*', 'x^3', x),
        ('1+x^2', '+', 1, 'x^2'),
        ('1+x^2+x^4', '+', '1+x^2', 'x^4'),
        ('(1+x^2+x^4)^x', '^', '1+x^2+x^4', x),
        ('(1+x^2+x^4)^y', '^', '1+x^2+x^4', y),
        ('(1+x)^y + (1+x+x^2)^y', '+', '(1+x)^y', '(1+x+x^2)^y'),
        ('(1+x)^x + (1+x+x^2)^x', '+', '(1+x)^x', '(1+x+x^2)^x'),
        ('((1+x)^x + (1+x+x^2)^x)^y', '^', '(1+x)^x + (1+x+x^2)^x', y),
        ('((1+x)^y + (1+x+x^2)^y)^x', '^', '(1+x)^y + (1+x+x^2)^y', x),
        ('(1+x^3)^x + (1+x^2+x^4)^x', '+', '(1+x^3)^x', '(1+x^2+x^4)^x'),
        ('(1+x^3)^y + (1+x^2+x^4)^y', '+', '(1+x^3)^y', '(1+x^2+x^4)^y'),
        ('((1+x^3)^x + (1+x^2+x^4)^x)^y', '^', '(1+x^3)^x + (1+x^2+x^4)^x', y),
        ('((1+x^3)^y + (1+x^2+x^4)^y)^x', '^', '(1+x^3)^y + (1+x^2+x^4)^y', x),
        ('LHS', '*', '((1+x)^y + (1+x+x^2)^y)^x', '((1+x^3)^x + (1+x^2+x^4)^x)^y'),
        ('RHS', '*', '((1+x)^x + (1+x+x^2)^x)^y', '((1+x^3)^y + (1+x^2+x^4)^y)^x')     
    ]
    ops = {'+': add_, '*': mul_, '^': exp}
    tv = lambda name, val: idpool.id(f"{name}_eqs_{val}")
    for term in terms:
        name, op, left, right = term
        cnf.extend(amo_encoder.exactly_one_pairwise([tv(name, v) for v in range(1, n+1)]))
        if isinstance(left, int) and isinstance(right, int):
            for v in range(1, n+1):
                cnf.append([-ops[op](left, right, v), tv(name,v)]) 
        elif isinstance(left, int):
            for u, v in itertools.product(range(1,n+1), repeat=2):
                cnf.append([-ops[op](left, u, v), -tv(right,u), tv(name,v)])
        elif isinstance(right, int):
            for u, v in itertools.product(range(1,n+1), repeat=2):
                cnf.append([-ops[op](u, right, v), -tv(left,u), tv(name,v)])
        else:
            for u, v, w in itertools.product(range(1,n+1), repeat=3):
                cnf.append([-ops[op](u, v, w), -tv(left,u), -tv(right,v), tv(name,w)])
        
    for v in range(1,n+1):
        cnf.append([-tv("LHS",v), -tv("RHS",v)])

    def add_table_lex_leader(left, right):
        current = []
        image = []
        def swap(value, left, right):
            if value == left:
                return right
            if value == right:
                return left
            return value
        for op in [add_, mul_, exp]:
            pairs = None
            if op == add_ or op == mul_:
                pairs = itertools.combinations(range(1, n+1), 2)
            else:
                pairs = itertools.product(range(1, n+1), repeat=2)
            for x, y in pairs:
                for value in range(1, n+1):
                    current.append(op(x, y, value))
                    image.append(
                    op(swap(x, left, right), swap(y, left, right), swap(value, left, right))
                    )
        lex.lex_smaller_eq(cnf, idpool, current, image, maxcomparisons=None)

    def add_table_transposition_lex_leaders(protected=(1,2,3,4,5)):
        protected = set(value for value in protected if value <= n)
        labels = [value for value in range(1, n+1) if value not in protected]

        # all transpositions
        for left, right in itertools.combinations(labels, 2):
            add_table_lex_leader(left, right)

    add_table_transposition_lex_leaders()

    # Zhang Sec. 3 normalization and Burris-Lee M lemmas.
    cnf.append([add_(1, 1, 2)]) # 2 = 1 + 1
    cnf.append([add_(2, 1, 3)]) # 3 = 2 + 1
    cnf.append([-add_(1, x, 1)]) # M01: 1 + x != 1
    cnf.append([-add_(2, x, 1)]) # M02: 2 + x != 1
    cnf.append([-add_(x, x, 1)]) # M03: x + x != 1
    cnf.append([-mul_(x, x, 1)]) # M04: x * x != 1
    cnf.append([-add_(x, x, x)]) # M09: x + x != x
    cnf.append([-mul_(x, x, x)]) # M10: x * x != x
    cnf.append([-add_(1, x, x)]) # M07: 1 + x != x
    cnf.append([-add_(2, x, x)]) # M08: 2 + x != x

    X2 = lambda v: tv('x^2', v)
    X3 = lambda v: tv('x^3', v)
    one_X2 = lambda v: tv('1+x^2', v)
    P_term = lambda v: tv('1+x', v)

    # Remaining Burris-Lee M lemmas from Zhang M05-M17.
    cnf.append([-one_X2(1)]) # M05: 1 + x*x != 1
    cnf.append([-X3(1)]) # M06: x*x*x != 1
    cnf.append([-one_X2(x)]) # M11: 1 + x*x != x
    for value in range(1, n+1):
        cnf.append([-add_(2, x, value), -P_term(value)]) # M12: 2 + x != 1 + x
        cnf.append([-mul_(x, x, value), -P_term(value)]) # M13: x*x != 1 + x
        cnf.append([-X3(value), -P_term(value)]) # M14: x*x*x != 1 + x
        cnf.append([-mul_(x, x, value), -add_(2, x, value)]) # M15: x*x != 2 + x
        cnf.append([-mul_(x, x, value), -add_(x, x, value)]) # M16: x*x != x + x
        cnf.append([-one_X2(value), -mul_(x, x, value)]) # M17: 1 + x*x != x*x

    # Lee: y != x*v for every v.
    for v in range(1, n+1):
        cnf.append([-mul_(x, v, y)])

    # Jackson linear-core fragment: y != i + j*x for i,j in {1,2,3}.
    for j in [1,2,3]:
            for z in range(1, n+1):
                for i in [1,2,3]:
                    cnf.append([-add_(i, z, y), -mul_(j, x, z)])

    # Jackson quadratic-core fragment: y != i + j*x + k*x^2.
    for i, j, k in itertools.product([1, 2, 3], repeat=3):
        for x2_value, jx_value, kx2_value, tail_value in itertools.product(range(1, n+1), repeat=4):
            cnf.append([
                -X2(x2_value),
                -mul_(j, x, jx_value),
                -mul_(k, x2_value, kx2_value),
                -add_(jx_value, kx2_value, tail_value),
                -add_(i, tail_value, y),
            ])

    # Zhang/Lee L2-L5: Q != P*v, P != Q*v, S != R*v, R != S*v.
    P = lambda i: tv('1+x',i)
    Q = lambda i: tv('1+x+x^2',i)
    R = lambda i: tv('1+x^3',i)
    S = lambda i: tv('1+x^2+x^4',i)
    
    for v in range(1,n+1):
        for i, l in itertools.product(range(1,n+1), repeat=2):
            cnf.append([-P(i), -Q(l), -mul_(i, v, l)])  # Q != P*x
            cnf.append([-Q(i), -P(l), -mul_(i, v, l)])  # P != Q*x
            cnf.append([-R(i), -S(l), -mul_(i, v, l)])  # S != R*x
            cnf.append([-S(i), -R(l), -mul_(i, v, l)])  # R != S*x

    if force_exp_2_4_5:
        cnf.append([exp(2, 4, 5)])

    print("nb clauses ", len(cnf.clauses))
    print("nb vars ", idpool.top)
    filename = f"w_{n}.cnf"
    cnf.to_file(filename)
    
    print(f"formula serialized as {filename}")
    return idpool

def decode(n, idpool, filename):
    assignment = {}
    for line in open(filename):
        tokens = line.split() 
        if len(tokens) > 0:
            if tokens[0] == "v":
                for token in tokens[1:]:
                    lit = int(token)
                    assignment[abs(lit)] = (lit > 0)

    ops = {'add', 'mul', 'exp' }
    tables = {op: [] for op in ops}

    for op in ops:
        tables[op] = [[-1 for j in range(n)] for i in range(n)]
        for i, j, k in itertools.product(range(1, n+1), repeat=3):
            if op in ['add', 'mul']:
                id_val = idpool.id(f"{op}_{min(i, j)}_{max(i, j)}_{k}")
            else:
                id_val = idpool.id(f"{op}_{i}_{j}_{k}")

            if assignment[id_val]:
                tables[op][i-1][j-1] = k
    
    for op in ops:
        print(f"{op} table:\\\\")

        print(rf"\begin{{array}}{{r|{'r'*n}}}")
        print(" & " + " & ".join([rf"\ov{{{j+1}}}" for j in range(n)]) + r" \\ ")
        print(r"\hline")
        for i in range(n):
            print(rf"\ov{{{i+1}}} & " + " & ".join([rf"\ov{{{tables[op][i][j]}}}" for j in range(n)]) + r" \\ ")
        print(rf"\end{{array}}")

        
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-n", "--n", type=int, required=True, help="number of variables")
    parser.add_argument("--exp-2-4-5", action="store_true", help="force exp(2,4)=5")
    parser.add_argument("--decode-file", type=str, help="decode the formula")
    args = parser.parse_args()
    idpool = encode(args.n, args.exp_2_4_5) 
    if args.decode_file:
        decode(args.n, idpool, args.decode_file)
