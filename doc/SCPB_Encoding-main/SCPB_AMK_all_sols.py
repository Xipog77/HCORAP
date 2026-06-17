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

def atMost_k(vars: List[int], weight: List[int], k):
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

    # (0) if weight[i] > k => x[i] False
    for i in range(1, n + 1):
        if weight[i] > k:
             plus_clause([-vars[i]])

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

    # (8) At Most K: X_i -> ¬R_{i-1,k+1-w_i} for i = 2 to n 
    for i in range(2, n + 1):
        if k + 1 - weight[i] > 0 and k + 1 - weight[i] <= pos_i(i - 1, k, weight):
            plus_clause([-vars[i], -map_register[i - 1][k + 1 - weight[i]]])

    #  Find all solutions of At Most K Encoding
    while True:
        if not sat_solver.solve():
            break

        solution = sat_solver.get_model()
        print("Solution is: ", solution)

        # Array to store index's item of solution[i], add to set solutions
        temp = []
        for i in range (0, n):
            if (solution[i] > 0):
                temp.append(solution[i])

        # Block the current solution
        blocking_clause = [-lit for lit in  solution[0:n]]
        sat_solver.add_clause(blocking_clause)

        print_solution(n)

    return n

def print_solution(n):
    print(f"Number of clauses: {sat_solver.nof_vars()}")
    print(f"Number of clauses: {sat_solver.nof_clauses()}")
    sat_status = sat_solver.solve()

    if not sat_status:
        print("UNSAT")
    else:
        solution = sat_solver.get_model()
        print(f"Solution found: {solution}")
        for i, val in enumerate(solution, start=1):
            if i <= n:
                print(f"X{i} = {int(val > 0)}")

# Example usage
# the first element of the list is not used

# 10X1 + 2X2 + 6X3 + 11X4 + 21X5 + 4X6 + 8X7 + 3X8 + 8X9 + 10X10 <= 20
n = atMost_k([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [0, 10, 2, 6, 11, 21, 4, 8, 3, 8, 10], 20)
