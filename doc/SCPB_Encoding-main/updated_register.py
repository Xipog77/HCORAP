from typing import List
from pysat.formula import CNF
from pysat.solvers import Glucose3

id_variable = 0
sat_solver = Glucose3()

def pos_i(i, k, weight):
    if i == 0:
        return 0
    if i < k:
        sum_w = sum(weight[1:i+1])
        return min(k, sum_w)
    else:
        return k

def plus_clause(clause):
    sat_solver.add_clause(clause)

def exactly_k(vars: List[int], weight: List[int], k):
    n = len(vars) - 1
    global id_variable
    id_variable = n

    # Create map_register to hold the auxiliary variables
    map_register = [[0 for _ in range(k + 1)] for _ in range(n + 1)]

    for i in range(1, n):
        n_bits = pos_i(i, k, weight)
        for j in range(1, n_bits + 1):
            id_variable += 1
            map_register[i][j] = id_variable

    print("Map register:")
    print(map_register)

    # (1) X_i -> R_i,j for j = 1 to w_i
    for i in range(1, n):
        for j in range(1, weight[i] + 1):
            if j <= k:
                plus_clause([-vars[i], map_register[i][j]])

    # (2) R_{i-1,j} -> R_i,j for j = 1 to pos_{i-1}
    for i in range(2, n):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            plus_clause([-map_register[i - 1][j], map_register[i][j]])

    # (3) X_i ^ R_{i-1,j} -> R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(2, n):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            if j + weight[i] <= k and j + weight[i] <= pos_i(i, k, weight):
                plus_clause([-vars[i], -map_register[i - 1][j], map_register[i][j + weight[i]]])

    # (4) ¬X_i ^ ¬R_{i-1,j} -> ¬R_i,j for j = 1 to pos_{i-1}
    for i in range(2, n):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            plus_clause([vars[i], map_register[i - 1][j], -map_register[i][j]])

    # (5) ¬X_i -> ¬R_i,j for j = 1 + pos_{i-1} to pos_i
    for i in range(1, n):
        if pos_i(i - 1, k, weight) < k:
            for j in range(1 + pos_i(i - 1, k, weight), pos_i(i, k, weight) + 1):
                plus_clause([vars[i], -map_register[i][j]])

    # (6) ¬R_{i-1,j} -> ¬R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(2, n):
        # if pos_i(i - 1, k, weight) < k:
            for j in range(1, pos_i(i - 1, k, weight) + 1):
                if j + weight[i] <= k and j + weight[i] <= pos_i(i, k, weight):
                    plus_clause([map_register[i - 1][j], -map_register[i][j + weight[i]]])
    # (7)
    plus_clause([map_register[n - 1][k], vars[n]])
    plus_clause([map_register[n - 1][k], map_register[n - 1][k - weight[n]]])

    # # (7) R_{n-1,k} v (X_n ^ R_{n-1,k-w_n})
    # print(f"n: {n}, k: {k}, weight: {weight[n]}")
    # if k > pos_i(n - 1, k, weight):
    #     plus_clause([vars[n]])
    #     plus_clause([map_register[n - 1][k - weight[n]]])
    # else:
    #     plus_clause([map_register[n - 1][k], vars[n]])
    #     if k - weight[n] > 0 and k - weight[n] <= pos_i(n - 1, k, weight):
    #         plus_clause([map_register[n - 1][k], map_register[n - 1][k - weight[n]]])

    #  (8) At Most K: X_i -> ¬R_{i-1,k+1-w_i} for i = 2 to n 
    for i in range(2, n + 1):
        if k + 1 - weight[i] > 0 and k + 1 - weight[i] <= pos_i(i - 1, k, weight):
            # print(f"i: {i}, k: {k}, weight: {weight[i]}")
            plus_clause([-vars[i], -map_register[i - 1][k + 1 - weight[i]]])

    # (9): Xi = True for i = 1 to n
    # for i in range(1, n):
    #     plus_clause([-vars[i]])

    return n

def atLeast_k(vars: List[int], weight: List[int], k):
    n = len(vars) - 1
    id_variable = n

    # Create map_register to hold the auxiliary variables
    map_register = [[0 for _ in range(k + 1)] for _ in range(n + 1)]

    for i in range(1, n):
        n_bits = pos_i(i, k, weight)
        for j in range(1, n_bits + 1):
            id_variable += 1
            map_register[i][j] = id_variable

    print("Map register:")
    print(map_register)


    # (1) X_i -> R_i,j for j = 1 to w_i
    for i in range(1, n):
        for j in range(1, weight[i] + 1):
            if j <= pos_i(i, k, weight):
                plus_clause([-vars[i], map_register[i][j]])

    # (2) R_{i-1,j} -> R_i,j for j = 1 to pos_{i-1}
    for i in range(2, n):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            plus_clause([-map_register[i - 1][j], map_register[i][j]])

    # (3) X_i ^ R_{i-1,j} -> R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(2, n):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            if j + weight[i] <= k and j + weight[i] <= pos_i(i, k, weight):
                plus_clause([-vars[i], -map_register[i - 1][j], map_register[i][j + weight[i]]])

    # (4) ¬X_i ^ ¬R_{i-1,j} -> ¬R_i,j for j = 1 to pos_{i-1}
    for i in range(2, n):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            plus_clause([vars[i], map_register[i - 1][j], -map_register[i][j]])

    # (5) ¬X_i -> ¬R_i,j for j = 1 + pos_{i-1} to pos_i
    for i in range(1, n):
        # if pos_i(i - 1, k, weight) < k:
            for j in range(1 + pos_i(i - 1, k, weight), pos_i(i, k, weight) + 1):
                plus_clause([vars[i], -map_register[i][j]])

    # (6) ¬R_{i-1,j} -> ¬R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(2, n):
        # if pos_i(i - 1, k, weight) < k:
            for j in range(1, pos_i(i - 1, k, weight) + 1):
                if j + weight[i] <= k and j + weight[i] <= pos_i(i, k, weight):
                    plus_clause([map_register[i - 1][j], -map_register[i][j + weight[i]]])

    # (7) R_{n-1,k} v (X_n ^ R_{n-1,k-w_n})
    print(f"n: {n}, k: {k}, weight: {weight[n]}")
    if k > pos_i(n - 1, k, weight):
        plus_clause([vars[n]])
        plus_clause([map_register[n - 1][k - weight[n]]])
    else:
        plus_clause([map_register[n - 1][k], vars[n]])
        if k - weight[n] > 0 and k - weight[n] <= pos_i(n - 1, k, weight):
            plus_clause([map_register[n - 1][k], map_register[n - 1][k - weight[n]]])

    print(id_variable)
    return id_variable


def atMost_k(vars: List[int], weight: List[int], k, max_var):
    n = len(vars) - 1
    id_variable = max_var

    # Create map_register to hold the auxiliary variables
    map_register = [[0 for _ in range(k + 1)] for _ in range(n + n + 2)]
    print(map_register)

    for i in range(n+2, n+n+1):
        n_bits = pos_i(i-n-1, k, weight)
        for j in range(1, n_bits + 1):
            id_variable += 1
            map_register[i][j] = id_variable

    print("Map register:")
    print(map_register)

    # (1) X_i -> R_i,j for j = 1 to w_i
    for i in range(n+2, n+n+1):
        for j in range(1, weight[i-n-1] + 1):
            if j <= pos_i(i-n, k, weight):
                plus_clause([-vars[i-n-1], map_register[i][j]])

    # (2) R_{i-1,j} -> R_i,j for j = 1 to pos_{i-1}
    for i in range(n+3, 2*n+1):
        for j in range(1, pos_i(i - 1 - n - 1, k, weight) + 1):
            plus_clause([-map_register[i][j], map_register[i][j]])

    # (3) X_i ^ R_{i-1,j} -> R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(n+3, 2*n+1):
        for j in range(1, pos_i(i - 1 - n - 1, k, weight) + 1):
            if j + weight[i-n-1] <= k and j + weight[i-n-1] <= pos_i(i-n-1, k, weight):
                plus_clause([-vars[i-n-1], -map_register[i - 1][j], map_register[i][j + weight[i-n-1]]])

    # (8) At Most K: X_i -> ¬R_{i-1,k+1-w_i} for i = 2 to n 
    for i in range(n+3, 2*n + 1):
        if k + 1 - weight[i-n-1] > 0 and k + 1 - weight[i-n-1] <= pos_i(i - 1-n-1, k, weight):
            plus_clause([-vars[i-n-1], -map_register[i - 1][k + 1 - weight[i-n-1]]])

    return n

def print_solution(n):
    print(f"Number of clauses: {sat_solver.nof_vars()}")
    print(f"Number of clauses: {sat_solver.nof_clauses()}")

    sat_status = sat_solver.solve_limited(expect_interrupt = True)

    if sat_status is False:
        print("No solutions found")
    else:
        solution = sat_solver.get_model()
        if solution is None:
            print("Time out")
        else:
            print(f"Solution found: {solution}")
            for i, val in enumerate(solution, start=1):
                if i <= n:
                    print(f"X{i} = {int(val > 0)}") 

# Example usage
# the first element of the list is not used



# 10X1 + 2X2 + 6X3 + 11X4 + 21X5 + 4X6 + 8X7 + 3X8 + 8X9 + 10X10 >= 30
# max_var = atLeast_k([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [0, 10, 2, 6, 11, 21, 4, 8, 3, 8, 10], 30)

result = atLeast_k([0, 1, 2, 3, 4, 5], [0, 30, 30, 30, 30, 30], 60)


# 10X1 + 2X2 + 6X3 + 11X4 + 21X5 + 4X6 + 8X7 + 3X8 + 8X9 + 10X10 <= 20
n = atMost_k([0, 1, 2, 3, 4, 5], [0, 10, 5, 30, 40, 50], 30, result)


print_solution(5)
