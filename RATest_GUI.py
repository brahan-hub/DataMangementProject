#!/usr/bin/env python3
"""
SPJUD Framework with a Tkinter UI in Three Modes:

1. Pre-defined Examples (each with distinct queries)
2. User Entered JSON/SQL
3. File Upload

After computing, the UI displays:
  - The correct query in SQL format (in green)
  - The wrong query in SQL format (in red)
  - The minimal counterexample output

The GUI remains running until the user selects "Exit" from the File menu.
"""

import random
import json
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from tabulate import tabulate
from z3 import Optimize, If, Bool, And, Or, sat, IntVal

GLOBAL_DATABASE = {}  # Used by RATableDynamic

###############################################
# PROVENANCE EXPRESSION CLASSES
###############################################

class ProvExpr:
    """Base class for provenance expressions."""
    pass

class ProvVar(ProvExpr):
    """A base variable (i.e. an input tuple)."""
    def __init__(self, var):
        self.var = var
    def __repr__(self):
        return f"{self.var}"

class ProvAnd(ProvExpr):
    """AND of a list of provenance expressions."""
    def __init__(self, children):
        self.children = children
    def __repr__(self):
        return "(" + " ∧ ".join([str(c) for c in self.children]) + ")"

class ProvOr(ProvExpr):
    """OR of a list of provenance expressions."""
    def __init__(self, children):
        self.children = children
    def __repr__(self):
        return "(" + " ∨ ".join([str(c) for c in self.children]) + ")"

###############################################
# RELATIONAL ALGEBRA OPERATOR CLASSES
###############################################

class RATable:
    """A base table with static data."""
    def __init__(self, table_name, rows, sql_str=None):
        self.table_name = table_name
        self.rows = rows
        self.sql_str = sql_str or f"SELECT * FROM {table_name}"
    def eval(self, base_vars):
        result = []
        for i, row in enumerate(self.rows):
            row_copy = dict(row)
            row_copy['prov'] = ProvVar((self.table_name, i))
            result.append(row_copy)
        return result
    def __repr__(self):
        return f"RATable({self.table_name})"

class RATableDynamic:
    """
    A dynamic RATable that looks up rows from a global database.
    """
    def __init__(self, table_name):
        self.table_name = table_name
        self.sql_str = f"SELECT * FROM {table_name} /* dynamic */"
    def eval(self, base_vars):
        try:
            rows = GLOBAL_DATABASE[self.table_name]
        except Exception as e:
            raise ValueError(f"Table '{self.table_name}' not found in database.")
        result = []
        for i, row in enumerate(rows):
            row_copy = dict(row)
            row_copy['prov'] = ProvVar((self.table_name, i))
            result.append(row_copy)
        return result
    def __repr__(self):
        return f"RATableDynamic({self.table_name})"

class RASelection:
    """Selection operator."""
    def __init__(self, predicate, child, sql_str=None):
        self.predicate = predicate
        self.child = child
        self.sql_str = sql_str or "/* Selection */"
    def eval(self, base_vars):
        child_result = self.child.eval(base_vars)
        return [row for row in child_result if self.predicate(row)]
    def __repr__(self):
        return f"RASelection({self.sql_str})"

class RAProjection:
    """Projection operator."""
    def __init__(self, attributes, child, sql_str=None):
        self.attributes = attributes
        self.child = child
        self.sql_str = sql_str or f"SELECT {', '.join(attributes)}"
    def eval(self, base_vars):
        child_result = self.child.eval(base_vars)
        proj_dict = {}
        for row in child_result:
            key = tuple(row[attr] for attr in self.attributes)
            if key in proj_dict:
                existing = proj_dict[key]
                if isinstance(existing, ProvOr):
                    proj_dict[key] = ProvOr(existing.children + [row['prov']])
                else:
                    proj_dict[key] = ProvOr([existing, row['prov']])
            else:
                proj_dict[key] = row['prov']
        result = []
        for key, prov in proj_dict.items():
            new_row = {attr: value for attr, value in zip(self.attributes, key)}
            new_row['prov'] = prov
            result.append(new_row)
        return result
    def __repr__(self):
        return f"RAProjection({self.attributes})"

class RAJoin:
    """Join operator."""
    def __init__(self, predicate, left, right, sql_str=None):
        self.predicate = predicate
        self.left = left
        self.right = right
        self.sql_str = sql_str or "JOIN ... ON ..."
    def eval(self, base_vars):
        left_result = self.left.eval(base_vars)
        right_result = self.right.eval(base_vars)
        result = []
        for l in left_result:
            for r in right_result:
                if self.predicate(l, r):
                    combined = {**l, **r}
                    combined['prov'] = ProvAnd([l['prov'], r['prov']])
                    result.append(combined)
        return result
    def __repr__(self):
        return f"RAJoin({self.sql_str})"

class RAUnion:
    """Union operator."""
    def __init__(self, left, right, sql_str=None):
        self.left = left
        self.right = right
        self.sql_str = sql_str or "UNION"
    def eval(self, base_vars):
        left_result = self.left.eval(base_vars)
        right_result = self.right.eval(base_vars)
        union_dict = {}
        def row_key(row):
            return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
        for row in left_result:
            key = row_key(row)
            union_dict[key] = dict(row)
        for row in right_result:
            key = row_key(row)
            if key in union_dict:
                existing = union_dict[key]['prov']
                if isinstance(existing, ProvOr):
                    union_dict[key]['prov'] = ProvOr(existing.children + [row['prov']])
                else:
                    union_dict[key]['prov'] = ProvOr([existing, row['prov']])
            else:
                union_dict[key] = dict(row)
        return list(union_dict.values())
    def __repr__(self):
        return f"RAUnion({self.sql_str})"

class RADifference:
    """Difference operator (EXCEPT)."""
    def __init__(self, left, right, sql_str=None):
        self.left = left
        self.right = right
        self.sql_str = sql_str or "EXCEPT"
    def eval(self, base_vars):
        left_result = self.left.eval(base_vars)
        right_result = self.right.eval(base_vars)
        def row_key(row):
            return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
        right_keys = {row_key(r) for r in right_result}
        return [row for row in left_result if row_key(row) not in right_keys]
    def __repr__(self):
        return f"RADifference({self.sql_str})"

class RARename:
    """Rename operator."""
    def __init__(self, rename_map, child, sql_str=None):
        self.rename_map = rename_map
        self.child = child
        self.sql_str = sql_str or f"RENAME {rename_map}"
    def eval(self, base_vars):
        child_result = self.child.eval(base_vars)
        result = []
        for row in child_result:
            new_row = {}
            for k, v in row.items():
                if k == 'prov':
                    continue
                new_key = self.rename_map.get(k, k)
                new_row[new_key] = v
            new_row['prov'] = row['prov']
            result.append(new_row)
        return result
    def __repr__(self):
        return f"RARename({self.rename_map})"

###############################################
# UTILITY: RA OPERATOR TO SQL STRING
###############################################

def ra_to_sql_string(operator):
    if hasattr(operator, "sql_str") and operator.sql_str:
        return operator.sql_str
    return "/* No SQL string available */"

###############################################
# WITNESS PROVENANCE & Z3 CONVERSION
###############################################

def compute_witness_provenance(q1_rows, q2_rows):
    def row_key(row):
        return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
    q1_dict = {}
    for row in q1_rows:
        key = row_key(row)
        if key in q1_dict:
            existing = q1_dict[key]
            if isinstance(existing, ProvOr):
                q1_dict[key] = ProvOr(existing.children + [row['prov']])
            else:
                q1_dict[key] = ProvOr([existing, row['prov']])
        else:
            q1_dict[key] = row['prov']
    q2_dict = {}
    for row in q2_rows:
        key = row_key(row)
        if key in q2_dict:
            existing = q2_dict[key]
            if isinstance(existing, ProvOr):
                q2_dict[key] = ProvOr(existing.children + [row['prov']])
            else:
                q2_dict[key] = ProvOr([existing, row['prov']])
        else:
            q2_dict[key] = row['prov']
    witness_exprs = []
    for key, prov in q1_dict.items():
        if key not in q2_dict:
            witness_exprs.append(prov)
    for key, prov in q2_dict.items():
        if key not in q1_dict:
            witness_exprs.append(prov)
    if not witness_exprs:
        return None
    return witness_exprs[0] if len(witness_exprs) == 1 else ProvOr(witness_exprs)

def prov_to_z3(prov, base_vars):
    if isinstance(prov, ProvVar):
        return base_vars[prov.var]
    elif isinstance(prov, ProvAnd):
        return And([prov_to_z3(child, base_vars) for child in prov.children])
    elif isinstance(prov, ProvOr):
        return Or([prov_to_z3(child, base_vars) for child in prov.children])
    else:
        raise ValueError("Unknown provenance expression type")

def create_base_vars(database):
    base_vars = {}
    for table_name, rows in database.items():
        for i, _ in enumerate(rows):
            base_vars[(table_name, i)] = Bool(f"in_{table_name}_{i}")
    return base_vars

def find_minimal_counterexample(Q1, Q2, database):
    base_vars = create_base_vars(database)
    q1_rows = Q1.eval(base_vars)
    q2_rows = Q2.eval(base_vars)
    witness_prov = compute_witness_provenance(q1_rows, q2_rows)
    if witness_prov is None:
        return None, 0
    witness_z3 = prov_to_z3(witness_prov, base_vars)
    opt = Optimize()
    opt.add(witness_z3)
    cost_expr = sum([If(var, 1, 0) for var in base_vars.values()])
    opt.minimize(cost_expr)
    if opt.check() == sat:
        model = opt.model()
        counterexample = {}
        for (table, idx), var in base_vars.items():
            if model.evaluate(var):
                counterexample.setdefault(table, []).append(database[table][idx])
        total = sum([1 for var in base_vars.values() if model.evaluate(var)])
        return counterexample, total
    else:
        return None, 0

###############################################
# BUILDER FOR USER-ENTERED RA TREE (JSON)
###############################################

def build_ra_tree(obj):
    op = obj.get("operator")
    if op == "RATable":
        return RATableDynamic(obj["table_name"])
    elif op == "RASelection":
        predicate_str = obj["predicate"]
        instance = RASelection(lambda row: eval(predicate_str, {"row": row}), build_ra_tree(obj["child"]),
                               sql_str=f"WHERE {predicate_str}")
        return instance
    elif op == "RAProjection":
        return RAProjection(obj["attributes"], build_ra_tree(obj["child"]),
                            sql_str=f"SELECT {', '.join(obj['attributes'])}")
    elif op == "RAJoin":
        predicate_str = obj["predicate"]
        instance = RAJoin(lambda left, right: eval(predicate_str, {"left": left, "right": right}),
                          build_ra_tree(obj["left"]), build_ra_tree(obj["right"]),
                          sql_str=f"JOIN ... ON {predicate_str}")
        return instance
    elif op == "RADifference":
        return RADifference(build_ra_tree(obj["left"]), build_ra_tree(obj["right"]),
                            sql_str="EXCEPT")
    elif op == "RARename":
        return RARename(obj["rename_map"], build_ra_tree(obj["child"]),
                        sql_str=f"RENAME {obj['rename_map']}")
    else:
        raise ValueError(f"Unknown operator: {op}")

def parse_user_input(json_text):
    data = json.loads(json_text)
    global GLOBAL_DATABASE
    GLOBAL_DATABASE = data["database"]
    correct_tree = build_ra_tree(data["correct_query"])
    wrong_tree = build_ra_tree(data["wrong_query"])
    return GLOBAL_DATABASE, correct_tree, wrong_tree

###############################################
# PREDEFINED EXAMPLES (Mode 1) with Updated Queries
###############################################

def init_toy_student_queries():
    students = [
        {"name": "Mary", "major": "CS"},
        {"name": "John", "major": "ECON"},
        {"name": "Jesse", "major": "CS"}
    ]
    registrations = [
        {"name": "Mary", "course": "216", "dept": "CS", "grade": 100},
        {"name": "Mary", "course": "230", "dept": "CS", "grade": 75},
        {"name": "Mary", "course": "208D", "dept": "ECON", "grade": 95},
        {"name": "John", "course": "316", "dept": "CS", "grade": 90},
        {"name": "John", "course": "208D", "dept": "ECON", "grade": 88},
        {"name": "Jesse", "course": "216", "dept": "CS", "grade": 95},
        {"name": "Jesse", "course": "316", "dept": "CS", "grade": 90},
        {"name": "Jesse", "course": "330", "dept": "CS", "grade": 85},
    ]
    database = {"Student": students, "Registration": registrations}

    wrong_sql = (
        "SELECT s.name, s.major\n"
        "FROM Student s\n"
        "JOIN Registration r ON s.name = r.name\n"
        "WHERE r.dept = 'CS';"
    )
    correct_sql = (
        "SELECT s.name, s.major\n"
        "FROM Student s\n"
        "JOIN Registration r ON s.name = r.name\n"
        "WHERE r.dept = 'CS'\n"
        "EXCEPT\n"
        "SELECT s.name, s.major\n"
        "FROM Student s\n"
        "JOIN Registration r1 ON s.name = r1.name\n"
        "JOIN Registration r2 ON s.name = r2.name\n"
        "WHERE r1.course <> r2.course AND r1.dept = 'CS' AND r2.dept = 'CS';"
    )

    wrong_query = RAProjection(
        ['name','major'],
        RAJoin(
            predicate=lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            left=RATable("Student", students, sql_str="SELECT * FROM Student s"),
            right=RATable("Registration", registrations, sql_str="SELECT * FROM Registration r"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )

    reg1 = RARename({"name": "r1_name", "course": "r1_course"},
                    RATable("Registration", registrations, sql_str="SELECT * FROM Registration r1"),
                    sql_str="/* Rename r1 */")
    join1 = RAJoin(
        predicate=lambda s, r: s['name'] == r['r1_name'],
        left=RATable("Student", students, sql_str="SELECT * FROM Student s2"),
        right=reg1,
        sql_str="JOIN Student s2, Registration r1 ON s2.name = r1.r1_name"
    )
    reg2 = RARename({"name": "r2_name", "course": "r2_course"},
                    RATable("Registration", registrations, sql_str="SELECT * FROM Registration r2"),
                    sql_str="/* Rename r2 */")
    join2 = RAJoin(
        predicate=lambda row, r: row['name'] == r['r2_name'] and row.get('r1_course') != r.get('r2_course'),
        left=join1,
        right=reg2,
        sql_str="JOIN r1, r2 ON (r1_course <> r2_course)"
    )
    multi_course = RAProjection(
        ['name','major'],
        join2,
        sql_str="SELECT s.name, s.major FROM (join1, join2) WHERE student has multiple CS courses"
    )
    correct_query = RADifference(
        left=wrong_query,
        right=multi_course,
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_random_student_queries():
    num_students = 10
    num_registrations = 20
    majors = ["CS", "ECON", "MATH", "BIO"]
    students = [{"name": f"Student_{i}", "major": random.choice(majors)} for i in range(num_students)]
    courses = ["101", "202", "303", "404", "216", "230", "316", "330"]
    depts = ["CS", "ECON", "MATH", "BIO"]
    regs = []
    for _ in range(num_registrations):
        name = random.choice(students)["name"]
        course = random.choice(courses)
        dept = random.choice(depts)
        grade = random.randint(60, 100)
        regs.append({"name": name, "course": course, "dept": dept, "grade": grade})
    database = {"Student": students, "Registration": regs}
    wrong_sql = (
        "SELECT s.name, s.major\n"
        "FROM Student s\n"
        "JOIN Registration r ON s.name = r.name\n"
        "WHERE r.dept = 'CS';"
    )
    wrong_query = RAProjection(
        ['name','major'],
        RAJoin(
            predicate=lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            left=RATable("Student", students, sql_str="SELECT * FROM Student s"),
            right=RATable("Registration", regs, sql_str="SELECT * FROM Registration r"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    correct_sql = (
        "SELECT s.name, s.major\n"
        "FROM Student s\n"
        "JOIN Registration r ON s.name = r.name\n"
        "WHERE r.dept = 'CS'\n"
        "EXCEPT\n"
        "SELECT s.name, s.major\n"
        "FROM Student s\n"
        "JOIN Registration r1 ON s.name = r1.name\n"
        "JOIN Registration r2 ON s.name = r2.name\n"
        "WHERE r1.course <> r2.course AND r1.dept = 'CS' AND r2.dept = 'CS';"
    )
    # For random student queries, use an empty fake subquery to simulate a difference.
    fake = []
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("FakeSubQuery", fake, sql_str="SELECT * FROM StudentsWithMultipleCS"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_employee_queries():
    employees = [
        {"emp_id": 1, "name": "Alice", "department": "Sales"},
        {"emp_id": 2, "name": "Bob", "department": "HR"},
        {"emp_id": 3, "name": "Charlie", "department": "IT"}
    ]
    salaries = [
        {"emp_id": 1, "year": 2022, "amount": 50000},
        {"emp_id": 1, "year": 2023, "amount": 60000},  # Raise for Alice
        {"emp_id": 2, "year": 2023, "amount": 55000},
        {"emp_id": 3, "year": 2022, "amount": 70000},
        {"emp_id": 3, "year": 2023, "amount": 65000}   # Decrease for Charlie
    ]
    database = {"Employee": employees, "Salary": salaries}
    wrong_sql = (
        "SELECT e.name, e.department\n"
        "FROM Employee e\n"
        "JOIN Salary s ON e.emp_id = s.emp_id\n"
        "WHERE s.year = 2023;"
    )
    wrong_query = RAProjection(
        ['name', 'department'],
        RAJoin(
            predicate=lambda e, s: e['emp_id'] == s['emp_id'] and s['year'] == 2023,
            left=RATable("Employee", employees, sql_str="SELECT * FROM Employee e"),
            right=RATable("Salary", salaries, sql_str="SELECT * FROM Salary s"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    # Fake subquery: only include employees with a raise.
    # Make sure to project only the attributes 'name' and 'department'
    raised_fake = [{"name": employees[0]["name"], "department": employees[0]["department"]}]
    correct_sql = (
        "SELECT e.name, e.department\n"
        "FROM Employee e\n"
        "JOIN Salary s ON e.emp_id = s.emp_id\n"
        "WHERE s.year = 2023\n"
        "EXCEPT\n"
        "SELECT e.name, e.department\n"
        "FROM Employee e\n"
        "WHERE e.name IN (SELECT name FROM EmployeesWithRaise);"
    )
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("EmployeesWithRaise", raised_fake, sql_str="SELECT name, department FROM EmployeesWithRaise"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_library_queries():
    books = [
        {"book_id": 1, "title": "1984", "author": "Orwell"},
        {"book_id": 2, "title": "Brave New World", "author": "Huxley"},
        {"book_id": 3, "title": "Fahrenheit 451", "author": "Bradbury"}
    ]
    borrow_records = [
        {"book_id": 1, "member": "Alice", "borrow_date": "2023-01-10"},
        {"book_id": 1, "member": "Bob", "borrow_date": "2023-02-15"},
        {"book_id": 2, "member": "Charlie", "borrow_date": "2023-03-20"},
        {"book_id": 3, "member": "Dave", "borrow_date": "2023-04-25"},
        {"book_id": 3, "member": "Eve", "borrow_date": "2023-05-05"}
    ]
    database = {"Books": books, "BorrowRecords": borrow_records}
    wrong_sql = (
        "SELECT b.title, b.author\n"
        "FROM Books b\n"
        "JOIN BorrowRecords br ON b.book_id = br.book_id;"
    )
    wrong_query = RAProjection(
        ['title', 'author'],
        RAJoin(
            predicate=lambda b, br: b['book_id'] == br['book_id'],
            left=RATable("Books", books, sql_str="SELECT * FROM Books b"),
            right=RATable("BorrowRecords", borrow_records, sql_str="SELECT * FROM BorrowRecords br"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    # Fake subquery: assume "Brave New World" was borrowed only once.
    fake = [{"title": "Brave New World", "author": "Huxley"}]
    correct_sql = (
        "SELECT b.title, b.author\n"
        "FROM Books b\n"
        "JOIN BorrowRecords br1 ON b.book_id = br1.book_id\n"
        "JOIN BorrowRecords br2 ON b.book_id = br2.book_id\n"
        "WHERE br1.member <> br2.member;"
    )
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("BooksBorrowedOnce", fake, sql_str="SELECT title, author FROM BooksBorrowedOnce"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_store_queries():
    products = [
        {"product_id": 1, "product_name": "Laptop", "category": "Electronics"},
        {"product_id": 2, "product_name": "Headphones", "category": "Electronics"},
        {"product_id": 3, "product_name": "Coffee Maker", "category": "Home"}
    ]
    orders = [
        {"order_id": 101, "product_id": 1, "quantity": 5, "order_date": "2023-07-01"},
        {"order_id": 102, "product_id": 1, "quantity": 12, "order_date": "2023-07-02"},
        {"order_id": 103, "product_id": 2, "quantity": 8, "order_date": "2023-07-03"},
        {"order_id": 104, "product_id": 2, "quantity": 9, "order_date": "2023-07-04"},
        {"order_id": 105, "product_id": 3, "quantity": 20, "order_date": "2023-07-05"}
    ]
    database = {"Products": products, "Orders": orders}
    wrong_sql = (
        "SELECT p.product_id, p.product_name\n"
        "FROM Products p\n"
        "JOIN Orders o ON p.product_id = o.product_id\n"
        "WHERE p.category = 'Electronics';"
    )
    wrong_query = RAProjection(
        ['product_id', 'product_name'],
        RAJoin(
            predicate=lambda p, o: p['product_id'] == o['product_id'] and p['category'] == 'Electronics',
            left=RATable("Products", products, sql_str="SELECT * FROM Products p"),
            right=RATable("Orders", orders, sql_str="SELECT * FROM Orders o"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    # Fake subquery: assume only Laptop has orders with quantity >= 10.
    fake = [{"product_id": 1, "product_name": "Laptop"}]
    correct_sql = (
        "SELECT p.product_id, p.product_name\n"
        "FROM Products p\n"
        "JOIN Orders o ON p.product_id = o.product_id\n"
        "WHERE p.category = 'Electronics' AND o.quantity >= 10;"
    )
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("HighQuantityOrders", fake, sql_str="SELECT product_id, product_name FROM HighQuantityOrders"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_social_network_queries():
    users = [
        {"user_id": 1, "name": "Alice"},
        {"user_id": 2, "name": "Bob"},
        {"user_id": 3, "name": "Charlie"}
    ]
    friendships = [
        {"user1": 1, "user2": 2},
        {"user1": 2, "user2": 1},
        {"user1": 2, "user2": 3}
    ]
    database = {"Users": users, "Friendships": friendships}
    # Wrong query: return all users (simply project Users table)
    wrong_sql = "SELECT u.user_id, u.name FROM Users u;"
    wrong_query = RAProjection(
        ['user_id', 'name'],
        RATable("Users", users, sql_str="SELECT * FROM Users u"),
        sql_str=wrong_sql
    )
    # Correct query: return only users with reciprocal friendship.
    correct_sql = (
        "SELECT u.user_id, u.name\n"
        "FROM Users u\n"
        "JOIN Friendships f1 ON u.user_id = f1.user1\n"
        "JOIN Friendships f2 ON u.user_id = f2.user2\n"
        "WHERE f1.user2 = f2.user1;"
    )
    # Fake subquery: assume only Alice has reciprocal friendship.
    fake = [{"user_id": 1, "name": "Alice"}]
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("UsersWithReciprocal", fake, sql_str="SELECT user_id, name FROM UsersWithReciprocal"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return {"Users": users}, correct_query, wrong_query


def init_ecommerce_reviews_queries():
    products = [
        {"product_id": 1, "product_name": "Laptop"},
        {"product_id": 2, "product_name": "Smartphone"},
        {"product_id": 3, "product_name": "Headphones"}
    ]
    reviews = [
        {"review_id": 1, "product_id": 1, "rating": 5},
        {"review_id": 2, "product_id": 1, "rating": 4},
        {"review_id": 3, "product_id": 2, "rating": 3},
        {"review_id": 4, "product_id": 3, "rating": 5}
    ]
    database = {"Products": products, "Reviews": reviews}
    wrong_sql = (
        "SELECT p.product_id, p.product_name\n"
        "FROM Products p\n"
        "JOIN Reviews r ON p.product_id = r.product_id\n"
        "WHERE r.rating >= 4;"
    )
    wrong_query = RAProjection(
        ['product_id', 'product_name'],
        RAJoin(
            predicate=lambda p, r: p['product_id'] == r['product_id'] and r['rating'] >= 4,
            left=RATable("Products", products, sql_str="SELECT * FROM Products p"),
            right=RATable("Reviews", reviews, sql_str="SELECT * FROM Reviews r"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    correct_sql = (
        "SELECT p.product_id, p.product_name\n"
        "FROM Products p\n"
        "JOIN Reviews r1 ON p.product_id = r1.product_id\n"
        "JOIN Reviews r2 ON p.product_id = r2.product_id\n"
        "WHERE r1.rating >= 4 AND r2.rating >= 4 AND r1.review_id <> r2.review_id;"
    )
    # Fake subquery: assume only Laptop has two distinct reviews ≥ 4.
    fake = [{"product_id": 1, "product_name": "Laptop"}]
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("ProductsWithMultipleReviews", fake, sql_str="SELECT product_id, product_name FROM ProductsWithMultipleReviews"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_sensor_data_queries():
    sensors = [
        {"sensor_id": 1, "location": "Room 101"},
        {"sensor_id": 2, "location": "Room 102"},
        {"sensor_id": 3, "location": "Room 103"}
    ]
    readings = [
        {"sensor_id": 1, "timestamp": "2023-01-01 10:00", "value": 85},
        {"sensor_id": 1, "timestamp": "2023-01-01 11:00", "value": 90},
        {"sensor_id": 2, "timestamp": "2023-01-01 10:30", "value": 75},
        {"sensor_id": 3, "timestamp": "2023-01-01 12:00", "value": 80}
    ]
    database = {"Sensors": sensors, "Readings": readings}
    wrong_sql = (
        "SELECT s.sensor_id, s.location\n"
        "FROM Sensors s\n"
        "JOIN Readings r ON s.sensor_id = r.sensor_id\n"
        "WHERE r.value >= 80;"
    )
    wrong_query = RAProjection(
        ['sensor_id', 'location'],
        RAJoin(
            predicate=lambda s, r: s['sensor_id'] == r['sensor_id'] and r['value'] >= 80,
            left=RATable("Sensors", sensors, sql_str="SELECT * FROM Sensors s"),
            right=RATable("Readings", readings, sql_str="SELECT * FROM Readings r"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    correct_sql = (
        "SELECT s.sensor_id, s.location\n"
        "FROM Sensors s\n"
        "JOIN Readings r1 ON s.sensor_id = r1.sensor_id\n"
        "JOIN Readings r2 ON s.sensor_id = r2.sensor_id\n"
        "WHERE r1.value >= 80 AND r2.value >= 80 AND r1.timestamp <> r2.timestamp;"
    )
    # Fake subquery: assume only Room 101 has two distinct high readings.
    fake = [{"sensor_id": 1, "location": "Room 101"}]
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("SensorsWithMultipleHighReadings", fake, sql_str="SELECT sensor_id, location FROM SensorsWithMultipleHighReadings"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_online_course_queries():
    courses = [
        {"course_id": 1, "course_name": "Intro to CS", "term": "Fall2023"},
        {"course_id": 2, "course_name": "Calculus", "term": "Fall2023"},
        {"course_id": 3, "course_name": "History", "term": "Fall2023"}
    ]
    enrollments = [
        {"course_id": 1, "section": "A", "student_id": 101},
        {"course_id": 1, "section": "B", "student_id": 102},
        {"course_id": 2, "section": "A", "student_id": 103},
        {"course_id": 3, "section": "A", "student_id": 104},
        {"course_id": 3, "section": "A", "student_id": 105}
    ]
    database = {"Courses": courses, "Enrollments": enrollments}
    wrong_sql = (
        "SELECT c.course_id, c.course_name\n"
        "FROM Courses c\n"
        "JOIN Enrollments e ON c.course_id = e.course_id;"
    )
    wrong_query = RAProjection(
        ['course_id', 'course_name'],
        RAJoin(
            predicate=lambda c, e: c['course_id'] == e['course_id'],
            left=RATable("Courses", courses, sql_str="SELECT * FROM Courses c"),
            right=RATable("Enrollments", enrollments, sql_str="SELECT * FROM Enrollments e"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    correct_sql = (
        "SELECT c.course_id, c.course_name\n"
        "FROM Courses c\n"
        "JOIN Enrollments e1 ON c.course_id = e1.course_id\n"
        "JOIN Enrollments e2 ON c.course_id = e2.course_id\n"
        "WHERE e1.section <> e2.section;"
    )
    # Fake subquery: assume Calculus (course_id=2) is offered in a single section.
    fake = [{"course_id": 2, "course_name": "Calculus"}]
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("CoursesWithSingleSection", fake, sql_str="SELECT course_id, course_name FROM CoursesWithSingleSection"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query


def init_telecom_calls_queries():
    subscribers = [
        {"subscriber_id": 1, "name": "Alice"},
        {"subscriber_id": 2, "name": "Bob"},
        {"subscriber_id": 3, "name": "Charlie"}
    ]
    calls = [
        {"call_id": 1, "caller_id": 1, "callee_id": 2},
        {"call_id": 2, "caller_id": 1, "callee_id": 3},
        {"call_id": 3, "caller_id": 2, "callee_id": 3},
        {"call_id": 4, "caller_id": 3, "callee_id": 1}
    ]
    database = {"Subscribers": subscribers, "Calls": calls}
    wrong_sql = (
        "SELECT s.subscriber_id, s.name\n"
        "FROM Subscribers s\n"
        "JOIN Calls c ON s.subscriber_id = c.caller_id;"
    )
    wrong_query = RAProjection(
        ['subscriber_id', 'name'],
        RAJoin(
            predicate=lambda s, c: s['subscriber_id'] == c['caller_id'],
            left=RATable("Subscribers", subscribers, sql_str="SELECT * FROM Subscribers s"),
            right=RATable("Calls", calls, sql_str="SELECT * FROM Calls c"),
            sql_str=wrong_sql
        ),
        sql_str=wrong_sql
    )
    correct_sql = (
        "SELECT s.subscriber_id, s.name\n"
        "FROM Subscribers s\n"
        "JOIN Calls c1 ON s.subscriber_id = c1.caller_id\n"
        "JOIN Calls c2 ON s.subscriber_id = c2.caller_id\n"
        "WHERE c1.callee_id <> c2.callee_id;"
    )
    # Fake subquery: assume only Alice made calls to more than one distinct callee.
    fake = [{"subscriber_id": 1, "name": "Alice"}]
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("SubscribersWithMultipleCallees", fake, sql_str="SELECT subscriber_id, name FROM SubscribersWithMultipleCallees"),
        sql_str=correct_sql
    )
    wrong_query.sql_str = wrong_sql
    correct_query.sql_str = correct_sql
    return database, correct_query, wrong_query

###############################################
# EXAMPLE MAPPING
###############################################

EXAMPLE_MAPPING = {
    "Toy Student Queries": init_toy_student_queries,
    "Random Student Queries": init_random_student_queries,
    "Employee Queries": init_employee_queries,
    "Library Queries": init_library_queries,
    "Store Queries": init_store_queries,
    "Social Network Queries": init_social_network_queries,
    "E-commerce Reviews Queries": init_ecommerce_reviews_queries,
    "Sensor Data Queries": init_sensor_data_queries,
    "Online Course Enrollment Queries": init_online_course_queries,
    "Telecom Call Records Queries": init_telecom_calls_queries,
}

###############################################
# TKINTER USER INTERFACE (3 Modes: Pre-defined, User JSON, File Upload)
###############################################

class SPJUDUI:
    def __init__(self, root):
        self.root = root
        self.root.title("SPJUD Minimal Counterexample Finder")
        self.create_menu()
        self.create_widgets()

    def create_menu(self):
        menu_bar = tk.Menu(self.root)
        self.root.config(menu=menu_bar)
        file_menu = tk.Menu(menu_bar, tearoff=0)
        menu_bar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Exit", command=self.root.quit)

    def create_widgets(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True)

        # Tab 1: Pre-defined Examples
        self.tab1 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab1, text="Pre-defined Examples")
        self.create_tab_predefined(self.tab1)

        # Tab 2: User Entered JSON/SQL
        self.tab2 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab2, text="User Entered JSON/SQL")
        self.create_tab_user_json(self.tab2)

        # Tab 3: File Upload
        self.tab3 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab3, text="File Upload")
        self.create_tab_file_upload(self.tab3)

    def create_tab_predefined(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="x")
        ttk.Label(frm, text="Select Example:").grid(row=0, column=0, sticky="W")
        self.example_var = tk.StringVar(value="Toy Student Queries")
        self.example_combo = ttk.Combobox(frm, textvariable=self.example_var,
                                          values=list(EXAMPLE_MAPPING.keys()), state="readonly", width=40)
        self.example_combo.grid(row=0, column=1, padx=5, sticky="W")
        btn = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_predefined)
        btn.grid(row=0, column=2, padx=10)
        self.text_predef = tk.Text(frame, width=100, height=30)
        self.text_predef.pack(padx=10, pady=10)
        self.text_predef.tag_config("green", foreground="green")
        self.text_predef.tag_config("red", foreground="red")
        scrollbar = ttk.Scrollbar(frame, command=self.text_predef.yview)
        scrollbar.pack(side="right", fill="y")
        self.text_predef.config(yscrollcommand=scrollbar.set)

    def create_tab_user_json(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="both", expand=True)
        ttk.Label(frm, text="Enter JSON (must include 'database', 'correct_query', 'wrong_query'):", wraplength=600).pack(anchor="w")
        self.text2_input = tk.Text(frm, width=100, height=15)
        self.text2_input.pack(padx=5, pady=5)
        btn = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_user_input)
        btn.pack(pady=5)
        ttk.Label(frm, text="Results:").pack(anchor="w")
        self.text2_output = tk.Text(frm, width=100, height=15)
        self.text2_output.pack(padx=5, pady=5)
        self.text2_output.tag_config("green", foreground="green")
        self.text2_output.tag_config("red", foreground="red")
        scrollbar2 = ttk.Scrollbar(frm, command=self.text2_output.yview)
        scrollbar2.pack(side="right", fill="y")
        self.text2_output.config(yscrollcommand=scrollbar2.set)

    def create_tab_file_upload(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="both", expand=True)
        btn_upload = ttk.Button(frm, text="Upload JSON File", command=self.upload_file)
        btn_upload.pack(pady=5)
        ttk.Label(frm, text="File Content:").pack(anchor="w")
        self.text3_input = tk.Text(frm, width=100, height=10)
        self.text3_input.pack(padx=5, pady=5)
        btn_comp = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_file_input)
        btn_comp.pack(pady=5)
        ttk.Label(frm, text="Results:").pack(anchor="w")
        self.text3_output = tk.Text(frm, width=100, height=10)
        self.text3_output.pack(padx=5, pady=5)
        self.text3_output.tag_config("green", foreground="green")
        self.text3_output.tag_config("red", foreground="red")
        scrollbar3 = ttk.Scrollbar(frm, command=self.text3_output.yview)
        scrollbar3.pack(side="right", fill="y")
        self.text3_output.config(yscrollcommand=scrollbar3.set)

    ###############################################
    # Displaying Queries in SQL Format
    ###############################################
    def show_queries_in_sql(self, text_widget, correct_Q, wrong_Q):
        text_widget.insert(tk.END, "Correct Query (SQL):\n", "green")
        correct_sql = ra_to_sql_string(correct_Q)
        text_widget.insert(tk.END, correct_sql + "\n\n", "green")
        text_widget.insert(tk.END, "Wrong Query (SQL):\n", "red")
        wrong_sql = ra_to_sql_string(wrong_Q)
        text_widget.insert(tk.END, wrong_sql + "\n\n", "red")

    def display_counterexample(self, text_widget, ce, cost):
        if ce is None:
            text_widget.insert(tk.END, "Queries are equivalent on the given database.\n")
        else:
            text_widget.insert(tk.END, f"Minimal counterexample ({cost} tuple(s)) found:\n")
            for table, rows in ce.items():
                if rows:
                    table_str = tabulate(rows, headers="keys", tablefmt="grid")
                    text_widget.insert(tk.END, f"\nTable {table}:\n{table_str}\n")

    ###############################################
    # Mode 1: Pre-defined Examples
    ###############################################
    def compute_predefined(self):
        self.text_predef.delete("1.0", tk.END)
        example_name = self.example_var.get()
        init_func = EXAMPLE_MAPPING.get(example_name)
        if not init_func:
            self.text_predef.insert(tk.END, "No such example.\n")
            return
        try:
            database, correct_Q, wrong_Q = init_func()
            self.show_queries_in_sql(self.text_predef, correct_Q, wrong_Q)
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, database)
            self.display_counterexample(self.text_predef, ce, cost)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    ###############################################
    # Mode 2: User Entered JSON/SQL
    ###############################################
    def compute_user_input(self):
        self.text2_output.delete("1.0", tk.END)
        json_text = self.text2_input.get("1.0", tk.END)
        try:
            data = json.loads(json_text)
            global GLOBAL_DATABASE
            GLOBAL_DATABASE = data["database"]
            correct_Q = build_ra_tree(data["correct_query"])
            wrong_Q = build_ra_tree(data["wrong_query"])
            self.text2_output.insert(tk.END, "Correct Query (SQL):\n", "green")
            self.text2_output.insert(tk.END, ra_to_sql_string(correct_Q) + "\n\n", "green")
            self.text2_output.insert(tk.END, "Wrong Query (SQL):\n", "red")
            self.text2_output.insert(tk.END, ra_to_sql_string(wrong_Q) + "\n\n", "red")
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, GLOBAL_DATABASE)
            self.display_counterexample(self.text2_output, ce, cost)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    ###############################################
    # Mode 3: File Upload
    ###############################################
    def upload_file(self):
        filename = filedialog.askopenfilename(title="Select JSON File",
                                              filetypes=[("JSON Files", "*.json"), ("All Files", "*.*")])
        if filename:
            try:
                with open(filename, "r") as f:
                    content = f.read()
                self.text3_input.delete("1.0", tk.END)
                self.text3_input.insert(tk.END, content)
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def compute_file_input(self):
        self.text3_output.delete("1.0", tk.END)
        json_text = self.text3_input.get("1.0", tk.END)
        try:
            data = json.loads(json_text)
            global GLOBAL_DATABASE
            GLOBAL_DATABASE = data["database"]
            correct_Q = build_ra_tree(data["correct_query"])
            wrong_Q = build_ra_tree(data["wrong_query"])
            self.text3_output.insert(tk.END, "Correct Query (SQL):\n", "green")
            self.text3_output.insert(tk.END, ra_to_sql_string(correct_Q) + "\n\n", "green")
            self.text3_output.insert(tk.END, "Wrong Query (SQL):\n", "red")
            self.text3_output.insert(tk.END, ra_to_sql_string(wrong_Q) + "\n\n", "red")
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, GLOBAL_DATABASE)
            self.display_counterexample(self.text3_output, ce, cost)
        except Exception as e:
            messagebox.showerror("Error", str(e))


###############################################
# MAIN
###############################################
def main():
    root = tk.Tk()
    app = SPJUDUI(root)
    root.mainloop()

if __name__ == "__main__":
    main()
