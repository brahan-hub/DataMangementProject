# import sqlite3
# import random
# import networkx as nx
# import matplotlib.pyplot as plt
# from z3 import Solver, Bool, Or, sat
#
#
# def create_toy_database():
#     conn = sqlite3.connect(":memory:")  # Use in-memory DB for testing
#     cursor = conn.cursor()
#
#     # Create tables
#     cursor.execute("""CREATE TABLE Student (
#                         name TEXT PRIMARY KEY,
#                         major TEXT);""")
#
#     cursor.execute("""CREATE TABLE Registration (
#                         name TEXT,
#                         course TEXT,
#                         dept TEXT,
#                         grade INTEGER,
#                         FOREIGN KEY(name) REFERENCES Student(name));""")
#
#     # Insert data into Student table
#     students = [
#         ('Mary', 'CS'),
#         ('John', 'ECON'),
#         ('Jesse', 'CS')
#     ]
#     cursor.executemany("INSERT INTO Student (name, major) VALUES (?, ?);", students)
#
#     # Insert data into Registration table
#     registrations = [
#         ('Mary', '216', 'CS', 100),
#         ('Mary', '230', 'CS', 75),
#         ('Mary', '208D', 'ECON', 95),
#         ('John', '316', 'CS', 90),
#         ('John', '208D', 'ECON', 88),
#         ('Jesse', '216', 'CS', 95),
#         ('Jesse', '316', 'CS', 90),
#         ('Jesse', '330', 'CS', 85),
#     ]
#     cursor.executemany("INSERT INTO Registration (name, course, dept, grade) VALUES (?, ?, ?, ?);", registrations)
#
#     conn.commit()
#     return conn
#
# # Random dataset generator with user input
# def generate_random_toy_database():
#     print("\n📌 Customize Your Dataset:")
#     num_students = int(input("🔹 Enter number of students: "))
#     num_registrations = int(input("🔹 Enter number of registrations: "))
#     save_db = input("🔹 Save dataset to toy_dataset.db? (yes/no): ").strip().lower() == "yes"
#
#     conn = sqlite3.connect(":memory:")  # Use in-memory DB for testing
#     cursor = conn.cursor()
#
#     # Create tables
#     cursor.execute("""CREATE TABLE Student (
#                         name TEXT PRIMARY KEY,
#                         major TEXT);""")
#
#     cursor.execute("""CREATE TABLE Registration (
#                         name TEXT,
#                         course TEXT,
#                         dept TEXT,
#                         grade INTEGER,
#                         FOREIGN KEY(name) REFERENCES Student(name));""")
#
#     # Generate random student names
#     student_names = [f"Student_{i}" for i in range(num_students)]
#     majors = ["CS", "ECON", "MATH", "BIO"]
#
#     # Insert random students
#     students = [(name, random.choice(majors)) for name in student_names]
#     cursor.executemany("INSERT INTO Student (name, major) VALUES (?, ?);", students)
#
#     # Generate random registrations
#     courses = ["101", "202", "303", "404", "216", "230", "316", "330"]
#     depts = ["CS", "ECON", "MATH", "BIO"]
#
#     registrations = []
#     for _ in range(num_registrations):
#         name = random.choice(student_names)
#         course = random.choice(courses)
#         dept = random.choice(depts)
#         grade = random.randint(60, 100)
#         registrations.append((name, course, dept, grade))
#
#     cursor.executemany("INSERT INTO Registration (name, course, dept, grade) VALUES (?, ?, ?, ?);", registrations)
#
#     conn.commit()
#
#     if save_db:
#         with open("toy_dataset.db", "wb") as f:
#             f.write(conn.iterdump())
#
#     return conn
#
#
# # Smallest Counterexample Finder Class
# class SmallestCounterexampleFinder:
#     def __init__(self, conn):
#         self.conn = conn
#         self.cursor = conn.cursor()
#
#     def execute_query(self, query):
#         """Executes a given SQL query and returns the result."""
#         self.cursor.execute(query)
#         return self.cursor.fetchall()
#
#     def compute_how_provenance(self, q1_result, q2_result):
#         """
#         Computes Boolean how-provenance expressions for tuples that differ.
#         Also checks for tuples in Q2(D) that are not in Q1(D).
#         """
#         provenance = {}
#
#         # Check for tuples in Q1(D) that are missing in Q2(D)
#         for row in q1_result:
#             if row not in q2_result:
#                 provenance[row] = Bool(f"p_{hash(row)}")
#
#         # Check for tuples in Q2(D) that are missing in Q1(D)
#         for row in q2_result:
#             if row not in q1_result:
#                 provenance[row] = Bool(f"p_{hash(row)}")
#
#         return provenance
#
#     def encode_constraints(self, provenance):
#         """Encodes how-provenance expressions into Boolean constraints for the SMT solver."""
#         solver = Solver()
#         if provenance:
#             constraint = Or([p for p in provenance.values()])
#             solver.add(constraint)
#         return solver
#
#     def find_smallest_counterexample(self, solver, provenance):
#         """Uses an SMT solver to find the minimal set of tuples that cause Q1 ≠ Q2."""
#         if solver.check() == sat:
#             model = solver.model()
#             smallest_example = [t for t, p in provenance.items() if model[p] == True]
#             return smallest_example
#         return None
#
#     def visualize_provenance(self, provenance):
#         """Creates a visualization of the provenance graph using networkx & matplotlib."""
#         G = nx.DiGraph()
#         for key, value in provenance.items():
#             G.add_node(str(key), label=str(key))
#             G.add_edge("Database", str(key))  # Connect database to the tuples
#
#         plt.figure(figsize=(10, 6))
#         pos = nx.spring_layout(G)
#         labels = nx.get_node_attributes(G, "label")
#         nx.draw(G, pos, with_labels=True, node_size=3000, node_color="skyblue", font_size=10, font_weight="bold")
#         nx.draw_networkx_labels(G, pos, labels)
#         plt.title("Provenance Graph")
#         plt.show()
#
#     def run(self, q1, q2):
#         """Main method to compute the smallest counterexample and visualize provenance."""
#         q1_result = self.execute_query(q1)
#         q2_result = self.execute_query(q2)
#         print("✅ Q1 (Correct Query) Result:", q1_result)
#         print("❌ Q2 (Incorrect Query) Result:", q2_result)
#
#         provenance = self.compute_how_provenance(q1_result, q2_result)
#         if not provenance:
#             print("⚠️ No differences found! Check queries.")
#             return None
#
#         solver = self.encode_constraints(provenance)
#         counterexample = self.find_smallest_counterexample(solver, provenance)
#
#         print("\n🔍 Smallest Counterexample Found:", counterexample)
#         # self.visualize_provenance(provenance)
#
#         return counterexample
#
#
# # Define the queries
# Q1 = """SELECT s.name, s.major
#         FROM Student s, Registration r
#         WHERE s.name = r.name AND r.dept = 'CS'
#         EXCEPT
#         SELECT s.name, s.major
#         FROM Student s, Registration r1, Registration r2
#         WHERE s.name = r1.name AND s.name = r2.name
#         AND r1.course <> r2.course AND r1.dept = 'CS' AND r2.dept = 'CS';"""
#
# Q2 = """SELECT DISTINCT s.name, s.major
#         FROM Student s, Registration r
#         WHERE s.name = r.name AND r.dept = 'CS';"""
#
# # Run the program
# if __name__ == "__main__":
#     flag = input("pick a num")
#     conn = create_toy_database()
#     if flag == "1":
#         conn = generate_random_toy_database(num_students=10, num_registrations=20, save_db=False)
#     finder = SmallestCounterexampleFinder(conn)
#     counterexample = finder.run(Q1, Q2)
# # Run the program
#
import sqlite3
import random
import pandas as pd
from z3 import Solver, Bool, Or, sat


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


def generate_random_toy_database():
    """Generates a random toy dataset based on user input."""
    print("\n📌 Customize Your Dataset:")
    num_students = int(input("🔹 Enter number of students: "))
    num_registrations = int(input("🔹 Enter number of registrations: "))
    save_db = input("🔹 Save dataset to toy_dataset.db? (yes/no): ").strip().lower() == "yes"

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

    # Generate random student names
    student_names = [f"Student_{i}" for i in range(num_students)]
    majors = ["CS", "ECON", "MATH", "BIO"]

    # Insert random students
    students = [(name, random.choice(majors)) for name in student_names]
    cursor.executemany("INSERT INTO Student (name, major) VALUES (?, ?);", students)

    # Generate random registrations
    courses = ["101", "202", "303", "404", "216", "230", "316", "330"]
    depts = ["CS", "ECON", "MATH", "BIO"]

    registrations = []
    for _ in range(num_registrations):
        name = random.choice(student_names)
        course = random.choice(courses)
        dept = random.choice(depts)
        grade = random.randint(60, 100)
        registrations.append((name, course, dept, grade))

    cursor.executemany("INSERT INTO Registration (name, course, dept, grade) VALUES (?, ?, ?, ?);", registrations)

    conn.commit()

    if save_db:
        with open("toy_dataset.db", "wb") as f:
            f.write(conn.iterdump())

    return conn


class SmallestCounterexampleFinder:
    def __init__(self, conn):
        self.conn = conn
        self.cursor = conn.cursor()

    def execute_query(self, query):
        """Executes a given SQL query and returns the result."""
        self.cursor.execute(query)
        return self.cursor.fetchall()

    def compute_how_provenance(self, q1_result, q2_result):
        """
        Computes Boolean how-provenance expressions for tuples that differ.
        Also checks for tuples in Q2(D) that are not in Q1(D).
        """
        provenance = {}

        # Check for tuples in Q1(D) that are missing in Q2(D)
        for row in q1_result:
            if row not in q2_result:
                provenance[row] = Bool(f"p_{hash(row)}")

        # Check for tuples in Q2(D) that are missing in Q1(D)
        for row in q2_result:
            if row not in q1_result:
                provenance[row] = Bool(f"p_{hash(row)}")

        return provenance

    def encode_constraints(self, provenance):
        """Encodes how-provenance expressions into Boolean constraints for the SMT solver."""
        solver = Solver()
        if provenance:
            constraint = Or([p for p in provenance.values()])
            solver.add(constraint)
        return solver

    def find_smallest_counterexample(self, solver, provenance):
        """Uses an SMT solver to find the minimal set of tuples that cause Q1 ≠ Q2."""
        if solver.check() == sat:
            model = solver.model()
            smallest_example = [t for t, p in provenance.items() if model[p] == True]
            return smallest_example
        return None

    def display_provenance_table(self, provenance):
        """Displays provenance in a structured tabular format."""
        if not provenance:
            print("\n⚠️ No provenance information found.")
            return

        # Convert Z3 Boolean expressions to strings
        data = [{"Tuple": str(key), "Provenance Variable": str(value)} for key, value in provenance.items()]
        df = pd.DataFrame(data)

        print("\n📜 How-Provenance Table:")
        print(df.to_string(index=False))  # Alternative to to_markdown()

    def run(self, q1, q2):
        """Main method to compute the smallest counterexample and display provenance."""
        q1_result = self.execute_query(q1)
        q2_result = self.execute_query(q2)
        print("✅ Q1 (Correct Query) Result:", q1_result)
        print("❌ Q2 (Incorrect Query) Result:", q2_result)

        provenance = self.compute_how_provenance(q1_result, q2_result)
        if not provenance:
            print("⚠️ No differences found! Check queries.")
            return None

        solver = self.encode_constraints(provenance)
        counterexample = self.find_smallest_counterexample(solver, provenance)

        print("\n🔍 Smallest Counterexample Found:", counterexample)
        self.display_provenance_table(provenance)

        return counterexample


# Define the queries
Q1 = """SELECT s.name, s.major
        FROM Student s, Registration r
        WHERE s.name = r.name AND r.dept = 'CS'
        EXCEPT
        SELECT s.name, s.major
        FROM Student s, Registration r1, Registration r2
        WHERE s.name = r1.name AND s.name = r2.name
        AND r1.course <> r2.course AND r1.dept = 'CS' AND r2.dept = 'CS';"""

Q2 = """SELECT DISTINCT s.name, s.major
        FROM Student s, Registration r
        WHERE s.name = r.name AND r.dept = 'CS';"""

# Run the program
if __name__ == "__main__":
    flag = input("🔹 Pick dataset type (1: random, 2: toy example): ")

    if flag == "1":
        conn = generate_random_toy_database()
    else:
        conn = create_toy_database()

    finder = SmallestCounterexampleFinder(conn)
    counterexample = finder.run(Q1, Q2)
