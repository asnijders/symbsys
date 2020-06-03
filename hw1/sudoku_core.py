from pprint import pprint
# from sudoku import pretty_repr
import sys
import numpy as np
from pysat.formula import CNF
from pysat.solvers import MinisatGH

### Propagation function to be used in the recursive sudoku solver
def propagate(sudoku_possible_values,k):
    """
    easy3.sudoku: 0.00 seconds
    easy4.sudoku: 3.32 seconds
    easy5.sudoku: seemingly endless
    hard3.sudoku: 0.00 seconds
    hard4.sudoku: 0.12 seconds
    hard5.sudoku: seemingly endless
    """
    # Instantiate a counter to track # of cells with len == 1; if no such cells are found, matrix is empty
    counter = 0

    #iterate over rows
    for i in range(len(sudoku_possible_values)):
        #iterate over cells
        for j in range(len(sudoku_possible_values)):

            #check for invalid domains of len == 0
            if len(sudoku_possible_values[i][j]) == 0:
                return None
            #skip cells where the domain consists of a single value already
            if len(sudoku_possible_values[i][j]) == 1:
                counter += 1
                continue
            #only look at uncertain cells
            elif len(sudoku_possible_values[i][j]) > 1:
                #specify the domain D of the current cell
                allowed_values = sudoku_possible_values[i][j]
                """
                for a given cell in the sudoku with a domain D with |D| > 1:
                1. Find k*k square to which cell belongs;
                   for all certain cells in that square, except the current cell:
                   check if their value is in D
                   if so, delete value from D
                
                2. for all certain cells in row i, except the current cell:
                   check if their value is in D:
                   if so, delete their value from D
                   
                3. for all certain cells in column j, except the current cell:
                   check if their value is in D:
                   if so, delete their value from D
                """
                # 1
                # find square to which cell i,j belongs
                col = j // k
                row = i // k
                rows = sudoku_possible_values[(row * k):(row * k + k)]
                box = [x[(col * k):(col * k + k)] for x in rows]

                # iterate over values in square, delete from domain if applicable
                for v in range(k):
                    for w in range(k):
                        cell = box[v][w]
                        if len(cell) == 1:
                            value = cell[0]
                            # check whether that value is in D, and make sure we're not looking at cell i,j
                            if value in allowed_values and (row * k + v, col * k + w) != (i, j):
                                allowed_values.remove(value)
                            if len(allowed_values) == 0:
                                break

                # 2
                # iterative over cells in row i, delete certain values from D if applicable
                for g in range(len(sudoku_possible_values)):
                    cell = sudoku_possible_values[i][g]
                    # find values of cells that were assigned a value already
                    if len(cell) == 1:
                        value = cell[0]
                        # check whether that value is in D, and make sure we're not looking at cell i,j
                        if value in allowed_values and (i,g) != (i,j):
                            allowed_values.remove(value)
                        if len(allowed_values) == 0:
                            break

                # 3
                # iterate over cells in column j, delete certain values from D if applicable
                for c in range(len(sudoku_possible_values)):
                    cell = sudoku_possible_values[c][j]
                    # print(cell)
                    if len(cell) == 1:
                        value = cell[0]
                        # check whether that value is in D, and make sure we're not looking at cell i,j
                        if value in allowed_values and (c,j) != (i,j):
                            # print('deleting {}'.format(value))
                            allowed_values.remove(value)
                        if len(allowed_values) == 0:
                            break


    if counter == 0:
        entry = [1,]
        row = [entry] * (k**2)
        matrix = [row] * (k**2)
        return matrix



    return sudoku_possible_values

###
### Solver that uses SAT encoding
###
def solve_sudoku_SAT(sudoku,k):



    # First we create a list containing all the edges for a given vertice i,j
    length = len(sudoku)
    num_vertices = length**2
    matrix = np.arange(num_vertices).reshape(length, length)
    edges = []

    sudoku = np.array(sudoku).reshape(length*length)

    # The loop below fills the edges list with all edges in the sudoku
    for i in range(length):
        for j in range(length):

            # specify the current value i,j as the left-hand value for the edge tuple
            left = int(matrix[i][j] + 1)

            # iterate over values in the square
            col = j // k
            row = i // k
            rows = matrix[(row * k):(row * k + k)]
            box = [x[(col * k):(col * k + k)] for x in rows]
            for v in range(k):
                for w in range(k):
                    right = int(box[v][w] + 1)

                    # make sure that we're not assigning the current value as the right-hand vertix
                    if (row * k + v, col * k + w) != (i, j):
                        if (left, right) not in edges:
                            edges.append((left, right))

            # iterative over cells in row i,
            for g in range(length):
                right = int(matrix[i][g] + 1)
                if (i, g) != (i, j):
                    if (left,right) not in edges:
                        edges.append((left, right))

            # iterate over cells in column j,
            for c in range(length):
                right = int(matrix[c][j] + 1)
                if (c, j) != (i, j):
                    if (left,right) not in edges:
                        edges.append((left, right))

    # specify the range of values which can be assigned to empty cells
    num_values = k**2
    formula = CNF()

    # this function will asign a positive integer for each propositional variable
    def var_number(i, c):
        return ((i - 1) * num_values) + c

    # we then add a clause which states that for each vertex in the graph, there must be at least one value v,
    # for which p__i,v is true
    for i in range(1, num_vertices + 1):
        clause = []

        # if the given sudoku has a 0 at that index, we assign all possible values from num_values
        if int(sudoku[i-1]) == 0:
            for c in range(1, num_values + 1):
                clause.append(var_number(i, c))
                formula.append(clause)
        # if the given sudoku already has an assigned value for that index, we only add a single clause
        else:
            clause.append(var_number(i, int(sudoku[i-1])))
            formula.append(clause)

    # at most one value for which p__i,v is true
    for i in range(1, num_vertices + 1):
        for c1 in range(1, num_values + 1):
            for c2 in range(c1 + 1, num_values + 1):
                clause = [-1 * var_number(i, c1), -1 * var_number(i, c2)]
                formula.append(clause)

    # ensure that values are assigned "properly"
    for (i1, i2) in edges:
        for c in range(1, num_values + 1):
            clause = [-1 * var_number(i1, c), -1 * var_number(i2, c)]
            formula.append(clause)

    solver = MinisatGH()
    solver.append_formula(formula)
    answer = solver.solve()

    # reshape the resulting matrix so that we can index it with a single value
    matrix = matrix.reshape(length**2)

    if answer == True:
        print("The sudoku is solved.")
        model = solver.get_model()
        for i in range(1, num_vertices + 1):
            for c in range(1, num_values + 1):
                if var_number(i, c) in model:
                    matrix[i-1] = c
        return matrix.reshape(length, length).tolist()
    else:
        print("The sudoku has no solution.")
        return None


###
### Solver that uses CSP encoding
###
def solve_sudoku_CSP(sudoku,k):
    return None;

###
### Solver that uses ASP encoding
###
def solve_sudoku_ASP(sudoku,k):
    return None;

###
### Solver that uses ILP encoding
###
def solve_sudoku_ILP(sudoku,k):
    return None;
