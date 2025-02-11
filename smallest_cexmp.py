from z3 import Solver, Bool, And, Or, Not, sat
import sqlite3
import random


class SPJUDSolver:
    def __init__(self, conn, correct_query, test_query):
        self.conn = conn
        self.correct_query = correct_query
        self.test_query = test_query

    def execute_query(self, query):
        cursor = self.conn.cursor()
        cursor.execute(query)
        return cursor.fetchall()

    def get_differentiating_tuples(self):
        """ Finds tuples present in Q1 but not in Q2, and vice versa."""
        q1_results = set(self.execute_query(self.correct_query))
        q2_results = set(self.execute_query(self.test_query))

        diff_tuples = q1_results.symmetric_difference(q2_results)
        return list(diff_tuples)

    def compute_provenance(self, diff_tuple):
        """ Generates a boolean formula representing how-provenance for diff_tuple."""
        provenance_expr = []
        for i, value in enumerate(diff_tuple):
            provenance_expr.append(f"t{i + 1}")
        prv_t = Or(*[Bool(p) for p in provenance_expr])
        print(f"Prv(t) for {diff_tuple}: {prv_t}")
        return prv_t

    def solve_min_witness(self, prv_expr):
        """ Uses SMT solver to find the smallest witness."""
        solver = Solver()
        solver.add(prv_expr)
        solver.push()
        min_witness = None

        for _ in range(10):  # Run multiple times for different solutions
            if solver.check() == sat:
                model = solver.model()
                witness_set = [str(v) for v in model if model[v]]
                print(f"Found witness: {witness_set}")
                if min_witness is None or len(witness_set) < len(min_witness):
                    min_witness = witness_set
                solver.add(Not(And(*[Bool(v) for v in witness_set])))
            else:
                break

        return min_witness

    def find_smallest_counterexample(self):
        """ Optimized approach for finding the smallest counterexample."""
        diff_tuples = self.get_differentiating_tuples()
        print(f"Differentiating tuples: {diff_tuples}")

        min_counterexample = None
        for diff_tuple in diff_tuples:
            prv_expr = self.compute_provenance(diff_tuple)
            witness = self.solve_min_witness(prv_expr)

            if witness and (min_counterexample is None or len(witness) < len(min_counterexample)):
                min_counterexample = witness

        print(f"Smallest Counterexample: {min_counterexample}")
        return min_counterexample


def create_another_dataset():
    conn = sqlite3.connect(":memory:")  # Use in-memory DB for testing
    cursor = conn.cursor()

    # Create tables
    cursor.execute("""CREATE TABLE Employee (
                        emp_id INTEGER PRIMARY KEY,
                        name TEXT,
                        department TEXT);""")

    cursor.execute("""CREATE TABLE Salary (
                        emp_id INTEGER,
                        amount INTEGER,
                        year INTEGER,
                        FOREIGN KEY(emp_id) REFERENCES Employee(emp_id));""")

    # Insert data into Employee table
    employees = [
        (1, 'Alice', 'HR'),
        (2, 'Bob', 'Finance'),
        (3, 'Charlie', 'Engineering')
    ]
    cursor.executemany("INSERT INTO Employee (emp_id, name, department) VALUES (?, ?, ?);", employees)

    # Insert data into Salary table
    salaries = [
        (1, 60000, 2022),
        (2, 75000, 2022),
        (3, 80000, 2022),
        (1, 65000, 2023),
        (2, 78000, 2023),
        (3, 85000, 2023)
    ]
    cursor.executemany("INSERT INTO Salary (emp_id, amount, year) VALUES (?, ?, ?);", salaries)

    conn.commit()
    return conn


def create_toy_database():
    conn = sqlite3.connect(":memory:")  # Use in-memory DB for testing
    cursor = conn.cursor()

    # Create tables
    cursor.execute("""CREATE TABLE Student (
                        name TEXT PRIMARY KEY,
                        major TEXT);""")

    cursor.execute("""CREATE TABLE Registration (
                        name TEXT,
                        course TEXT,
                        dept TEXT,
                        grade INTEGER,
                        FOREIGN KEY(name) REFERENCES Student(name));""")

    # Insert data into Student table
    students = [
        ('Mary', 'CS'),
        ('John', 'ECON'),
        ('Jesse', 'CS')
    ]
    cursor.executemany("INSERT INTO Student (name, major) VALUES (?, ?);", students)

    # Insert data into Registration table
    registrations = [
        ('Mary', '216', 'CS', 100),
        ('Mary', '230', 'CS', 75),
        ('Mary', '208D', 'ECON', 95),
        ('John', '316', 'CS', 90),
        ('John', '208D', 'ECON', 88),
        ('Jesse', '216', 'CS', 95),
        ('Jesse', '316', 'CS', 90),
        ('Jesse', '330', 'CS', 85),
    ]
    cursor.executemany("INSERT INTO Registration (name, course, dept, grade) VALUES (?, ?, ?, ?);", registrations)

    conn.commit()
    return conn


def init_student_queries():
    conn = create_toy_database()
    student_correct_query = """
        SELECT s.name, s.major
        FROM Student s, Registration r
        WHERE s.name = r.name AND r.dept = 'CS'
        EXCEPT
        SELECT s.name, s.major
        FROM Student s, Registration r1, Registration r2
        WHERE s.name = r1.name AND s.name = r2.name
        AND r1.course <> r2.course
        AND r1.dept = 'CS' AND r2.dept = 'CS';
    """
    student_test_query = """
        SELECT s.name, s.major
        FROM Student s, Registration r
        WHERE s.name = r.name AND r.dept = 'CS';
    """
    return conn, student_correct_query, student_test_query

def init_employee_queries():
    conn = create_another_dataset()
    correct_query = """
        SELECT e.name, e.department 
        FROM Employee e, Salary s
        WHERE e.emp_id = s.emp_id AND s.year = 2023
        EXCEPT
        SELECT e.name, e.department
        FROM Employee e, Salary s1, Salary s2
        WHERE e.emp_id = s1.emp_id AND e.emp_id = s2.emp_id 
        AND s1.year = 2022 AND s2.year = 2023 AND s1.amount < s2.amount;
    """
    test_query = """
        SELECT e.name, e.department 
        FROM Employee e, Salary s
        WHERE e.emp_id = s.emp_id AND s.year = 2023;
    """
    return conn, correct_query, test_query

if __name__ == "__main__":
    print("Example 1: Student Toy DataSet")
    conn, correct_query, test_query = init_student_queries()
    solver = SPJUDSolver(conn, correct_query, test_query)
    solver.find_smallest_counterexample()

    print("Example 2: Employee Toy DataSet")

    conn, correct_query, test_query = init_employee_queries()
    solver = SPJUDSolver(conn, correct_query, test_query)
    solver.find_smallest_counterexample()

    print("Example 3: Student Random DataSet")



