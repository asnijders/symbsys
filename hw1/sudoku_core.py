from pprint import pprint
# from sudoku import pretty_repr
import sys

# from pysat.formula import CNF
# from pysat.solvers import MinisatGH

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
    return None;

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
