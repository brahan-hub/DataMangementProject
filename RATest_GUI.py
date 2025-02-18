#!/usr/bin/env python3
"""
SPJUD Framework with a Tkinter User Interface Supporting Three Modes

Modes:
  1. Pre-defined Examples
  2. User Entered JSON/SQL
  3. File Upload

After computing, the UI displays:
  - The correct query (in green)
  - The wrong query (in red)
  - The minimal counterexample output
"""

import random
import json
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from tabulate import tabulate
from z3 import Optimize, If, Bool, And, Or, sat, IntVal

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
    def __init__(self, table_name, rows):
        self.table_name = table_name
        self.rows = rows
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
    def __init__(self, predicate, child):
        self.predicate = predicate
        self.child = child
        self.predicate_str = getattr(self, "predicate_str", "<predicate>")
    def eval(self, base_vars):
        child_result = self.child.eval(base_vars)
        return [row for row in child_result if self.predicate(row)]
    def __repr__(self):
        return f"RASelection({self.predicate_str})"

class RAProjection:
    """Projection operator."""
    def __init__(self, attributes, child):
        self.attributes = attributes
        self.child = child
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
    def __init__(self, predicate, left, right):
        self.predicate = predicate
        self.left = left
        self.right = right
        self.predicate_str = getattr(self, "predicate_str", "<predicate>")
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
        return f"RAJoin({self.predicate_str})"

class RAUnion:
    """Union operator."""
    def __init__(self, left, right):
        self.left = left
        self.right = right
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
        return "RAUnion"

class RADifference:
    """Difference operator."""
    def __init__(self, left, right):
        self.left = left
        self.right = right
    def eval(self, base_vars):
        left_result = self.left.eval(base_vars)
        right_result = self.right.eval(base_vars)
        def row_key(row):
            return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
        right_keys = {row_key(r) for r in right_result}
        return [row for row in left_result if row_key(row) not in right_keys]
    def __repr__(self):
        return "RADifference"

class RARename:
    """Rename operator."""
    def __init__(self, rename_map, child):
        self.rename_map = rename_map
        self.child = child
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
# RA TREE TO STRING (for display)
###############################################

def ra_tree_to_string(query, indent=0):
    prefix = "  " * indent
    if isinstance(query, RATable):
        return prefix + f"RATable({query.table_name})"
    elif isinstance(query, RATableDynamic):
        return prefix + f"RATableDynamic({query.table_name})"
    elif isinstance(query, RASelection):
        pred = getattr(query, "predicate_str", "<lambda>")
        child_str = ra_tree_to_string(query.child, indent+1)
        return prefix + f"RASelection({pred})\n" + child_str
    elif isinstance(query, RAProjection):
        attrs = ", ".join(query.attributes)
        child_str = ra_tree_to_string(query.child, indent+1)
        return prefix + f"RAProjection([{attrs}])\n" + child_str
    elif isinstance(query, RAJoin):
        pred = getattr(query, "predicate_str", "<lambda>")
        left_str = ra_tree_to_string(query.left, indent+1)
        right_str = ra_tree_to_string(query.right, indent+1)
        return prefix + f"RAJoin({pred})\n" + left_str + "\n" + right_str
    elif isinstance(query, RADifference):
        left_str = ra_tree_to_string(query.left, indent+1)
        right_str = ra_tree_to_string(query.right, indent+1)
        return prefix + "RADifference\n" + left_str + "\n" + right_str
    elif isinstance(query, RARename):
        child_str = ra_tree_to_string(query.child, indent+1)
        return prefix + f"RARename({query.rename_map})\n" + child_str
    else:
        return prefix + str(query)

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
    return witness_exprs[0] if len(witness_exprs)==1 else ProvOr(witness_exprs)

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
        return None, None

###############################################
# BUILDER FOR USER-ENTERED RA TREE (JSON)
###############################################

def build_ra_tree(obj):
    op = obj.get("operator")
    if op == "RATable":
        return RATableDynamic(obj["table_name"])
    elif op == "RASelection":
        predicate_str = obj["predicate"]
        instance = RASelection(lambda row: eval(predicate_str, {"row": row}), build_ra_tree(obj["child"]))
        instance.predicate_str = predicate_str
        return instance
    elif op == "RAProjection":
        return RAProjection(obj["attributes"], build_ra_tree(obj["child"]))
    elif op == "RAJoin":
        predicate_str = obj["predicate"]
        instance = RAJoin(lambda left, right: eval(predicate_str, {"left": left, "right": right}),
                           build_ra_tree(obj["left"]), build_ra_tree(obj["right"]))
        instance.predicate_str = predicate_str
        return instance
    elif op == "RADifference":
        return RADifference(build_ra_tree(obj["left"]), build_ra_tree(obj["right"]))
    elif op == "RARename":
        return RARename(obj["rename_map"], build_ra_tree(obj["child"]))
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
# PREDEFINED EXAMPLES (Mode 1)
###############################################

def create_toy_database():
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
    return {"Student": students, "Registration": registrations}


def init_toy_student_queries():
    """
    Correct query: Remove students with multiple distinct CS courses.
    Test query: All students with a registration in CS.
    """
    database = create_toy_database()
    test_query = RAProjection(
        ['name', 'major'],
        RAJoin(
            lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            RATable("Student", database["Student"]),
            RATable("Registration", database["Registration"])
        )
    )
    reg1 = RARename({"name": "r1_name", "course": "r1_course", "dept": "r1_dept", "grade": "r1_grade"},
                    RATable("Registration", database["Registration"]))
    join1 = RAJoin(
        lambda s, r1: s['name'] == r1['r1_name'] and r1['r1_dept'] == 'CS',
        RATable("Student", database["Student"]),
        reg1
    )
    reg2 = RARename({"name": "r2_name", "course": "r2_course", "dept": "r2_dept", "grade": "r2_grade"},
                    RATable("Registration", database["Registration"]))
    join2 = RAJoin(
        lambda row, r2: row['name'] == r2['r2_name'] and row['r1_course'] != r2['r2_course'] and r2['r2_dept'] == 'CS',
        join1,
        reg2
    )
    multi_course = RAProjection(['name', 'major'], join2)
    correct_query = RADifference(test_query, multi_course)
    return database, correct_query, test_query


def create_random_student_dataset():
    num_students = int(input("Enter number of students: "))
    num_registrations = int(input("Enter number of registrations: "))
    majors = ["CS", "ECON", "MATH", "BIO"]
    students = [{"name": f"Student_{i}", "major": random.choice(majors)} for i in range(num_students)]
    courses = ["101", "202", "303", "404", "216", "230", "316", "330"]
    depts = ["CS", "ECON", "MATH", "BIO"]
    registrations = []
    for _ in range(num_registrations):
        name = random.choice([s["name"] for s in students])
        course = random.choice(courses)
        dept = random.choice(depts)
        grade = random.randint(60, 100)
        registrations.append({"name": name, "course": course, "dept": dept, "grade": grade})
    return {"Student": students, "Registration": registrations}


def init_random_student_queries():
    database = create_random_student_dataset()
    test_query = RAProjection(
        ['name', 'major'],
        RAJoin(
            lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            RATable("Student", database["Student"]),
            RATable("Registration", database["Registration"])
        )
    )
    reg1 = RARename({"name": "r1_name", "course": "r1_course", "dept": "r1_dept", "grade": "r1_grade"},
                    RATable("Registration", database["Registration"]))
    join1 = RAJoin(
        lambda s, r1: s['name'] == r1['r1_name'] and r1['r1_dept'] == 'CS',
        RATable("Student", database["Student"]),
        reg1
    )
    reg2 = RARename({"name": "r2_name", "course": "r2_course", "dept": "r2_dept", "grade": "r2_grade"},
                    RATable("Registration", database["Registration"]))
    join2 = RAJoin(
        lambda row, r2: row['name'] == r2['r2_name'] and row['r1_course'] != r2['r2_course'] and r2['r2_dept'] == 'CS',
        join1,
        reg2
    )
    multi_course = RAProjection(['name', 'major'], join2)
    correct_query = RADifference(test_query, multi_course)
    return database, correct_query, test_query


def create_employee_database():
    employees = [
        {"emp_id": 1, "name": "Alice", "department": "Sales"},
        {"emp_id": 2, "name": "Bob", "department": "HR"},
        {"emp_id": 3, "name": "Charlie", "department": "IT"}
    ]
    salaries = [
        {"emp_id": 1, "year": 2022, "amount": 50000},
        {"emp_id": 1, "year": 2023, "amount": 60000},
        {"emp_id": 2, "year": 2023, "amount": 55000},
        {"emp_id": 3, "year": 2022, "amount": 70000},
        {"emp_id": 3, "year": 2023, "amount": 65000}
    ]
    return {"Employee": employees, "Salary": salaries}


def init_employee_queries():
    database = create_employee_database()
    test_query = RAProjection(
        ['name', 'department'],
        RAJoin(
            lambda e, s: e['emp_id'] == s['emp_id'] and s['year'] == 2023,
            RATable("Employee", database["Employee"]),
            RATable("Salary", database["Salary"])
        )
    )
    sal1 = RARename({"emp_id": "s1_emp_id", "year": "s1_year", "amount": "s1_amount"},
                    RATable("Salary", database["Salary"]))
    join1 = RAJoin(
        lambda e, s1: e['emp_id'] == s1['s1_emp_id'] and s1['s1_year'] == 2022,
        RATable("Employee", database["Employee"]),
        sal1
    )
    sal2 = RARename({"emp_id": "s2_emp_id", "year": "s2_year", "amount": "s2_amount"},
                    RATable("Salary", database["Salary"]))
    join2 = RAJoin(
        lambda row, s2: row['emp_id'] == s2['s2_emp_id'] and s2['s2_year'] == 2023 and row['s1_amount'] < s2[
            's2_amount'],
        join1,
        sal2
    )
    multi_salary = RAProjection(['name', 'department'], join2)
    correct_query = RADifference(test_query, multi_salary)
    return database, correct_query, test_query


def create_library_database():
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
        {"book_id": 3, "member": "Dave", "borrow_date": "2023-05-05"}  # same member
    ]
    return {"Books": books, "BorrowRecords": borrow_records}


def init_library_queries():
    """
    Test query: All books that have been borrowed at least once.
    Correct query: Books that have been borrowed by at least two distinct members.
    """
    database = create_library_database()
    test_query = RAProjection(
        ['book_id', 'title'],
        RAJoin(
            lambda b, br: b['book_id'] == br['book_id'],
            RATable("Books", database["Books"]),
            RATable("BorrowRecords", database["BorrowRecords"])
        )
    )
    br1 = RARename({"book_id": "br1_book_id", "member": "br1_member", "borrow_date": "br1_date"},
                   RATable("BorrowRecords", database["BorrowRecords"]))
    join1 = RAJoin(
        lambda b, br1: b['book_id'] == br1['br1_book_id'],
        RATable("Books", database["Books"]),
        br1
    )
    br2 = RARename({"book_id": "br2_book_id", "member": "br2_member", "borrow_date": "br2_date"},
                   RATable("BorrowRecords", database["BorrowRecords"]))
    join2 = RAJoin(
        lambda row, br2: row['book_id'] == br2['br2_book_id'] and row['br1_member'] != br2['br2_member'],
        join1,
        br2
    )
    correct_query = RAProjection(['book_id', 'title'], join2)
    return database, correct_query, test_query


def create_store_database():
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
    return {"Products": products, "Orders": orders}


def init_store_queries():
    """
    Test query: Products in category 'Electronics' (via join).
    Correct query: Electronics products having an order with quantity >= 10.
    """
    database = create_store_database()
    T = RAJoin(
        lambda p, o: p['product_id'] == o['product_id'] and p['category'] == 'Electronics',
        RATable("Products", database["Products"]),
        RATable("Orders", database["Orders"])
    )
    test_query = RAProjection(['product_id', 'product_name'], T)
    correct_query = RAProjection(
        ['product_id', 'product_name'],
        RASelection(lambda row: row['quantity'] >= 10, T)
    )
    return database, correct_query, test_query


###############################################
# NEW EXAMPLES 6-10 (Diverse, Random, Large)
###############################################

# Example 6: Social Network Queries
def init_social_network_queries():
    """
    Database: Users (200 tuples) and Friendships (1000 tuples).
    Test query: All users that have at least one outgoing friendship.
    Correct query: Users that have a reciprocal (bidirectional) friendship.
    (Difference: Users with only one directional friendship.)
    """
    num_users = 200
    num_friendships = 1000
    users = [{"user_id": i, "name": f"User_{i}"} for i in range(1, num_users + 1)]
    friendships = []
    for _ in range(num_friendships):
        u1 = random.randint(1, num_users)
        u2 = random.randint(1, num_users)
        while u2 == u1:
            u2 = random.randint(1, num_users)
        friendships.append({"user1": u1, "user2": u2})
    database = {"Users": users, "Friendships": friendships}

    # Test query: Users with any friendship (join Users with Friendships on user_id = user1)
    test_query = RAProjection(
        ['user_id', 'name'],
        RAJoin(
            lambda u, f: u['user_id'] == f['user1'],
            RATable("Users", database["Users"]),
            RATable("Friendships", database["Friendships"])
        )
    )
    # Correct query: Users with reciprocal friendship.
    # First, find reciprocal friendship in Friendships:
    recips = RAJoin(
        lambda f1, f2: f1['user1'] == f2['user2'] and f1['user2'] == f2['user1'],
        RATable("Friendships", database["Friendships"]),
        RARename({"user1": "user1", "user2": "user2"}, RATable("Friendships", database["Friendships"]))
    )
    # Then join with Users to get user details.
    correct_query = RAProjection(
        ['user_id', 'name'],
        RAJoin(
            lambda u, r: u['user_id'] == r['user1'],
            RATable("Users", database["Users"]),
            recips
        )
    )
    # Our intended "correct" query is the reciprocal friendship one.
    # The difference between test and correct (RADifference) gives users with one-directional friendship.
    diff_query = RADifference(test_query, correct_query)
    return database, diff_query, test_query


# Example 7: E-commerce Reviews Queries
def init_ecommerce_reviews_queries():
    """
    Database: Products (1000 tuples) and Reviews (5000 tuples).
    Test query: Products with at least one review having rating >= 4.
    Correct query: Products with at least two distinct reviews (different review_id) having rating >= 4.
    Difference: Products with exactly one such review.
    """
    num_products = 1000
    num_reviews = 5000
    products = [{"product_id": i, "product_name": f"Product_{i}"} for i in range(1, num_products + 1)]
    reviews = []
    for i in range(1, num_reviews + 1):
        prod = random.randint(1, num_products)
        rating = random.randint(1, 5)
        reviews.append({"review_id": i, "product_id": prod, "rating": rating})
    database = {"Products": products, "Reviews": reviews}

    # Test query: Products with at least one review rating >= 4.
    test_query = RAProjection(
        ['product_id', 'product_name'],
        RAJoin(
            lambda p, r: p['product_id'] == r['product_id'] and r['rating'] >= 4,
            RATable("Products", database["Products"]),
            RATable("Reviews", database["Reviews"])
        )
    )
    # Correct query: Products with two distinct reviews rating >= 4.
    r1 = RARename({"product_id": "p1", "rating": "r1", "review_id": "r1_id"}, RATable("Reviews", database["Reviews"]))
    r2 = RARename({"product_id": "p2", "rating": "r2", "review_id": "r2_id"}, RATable("Reviews", database["Reviews"]))
    review_join = RAJoin(
        lambda a, b: a['p1'] == b['p2'] and a['r1'] >= 4 and b['r2'] >= 4 and a['r1_id'] != b['r2_id'],
        r1, r2
    )
    correct_query = RAProjection(
        ['product_id', 'product_name'],
        RAJoin(
            lambda p, r: p['product_id'] == r['p1'],
            RATable("Products", database["Products"]),
            review_join
        )
    )
    diff_query = RADifference(test_query, correct_query)
    return database, diff_query, test_query


# Example 8: Sensor Data Queries
def init_sensor_data_queries():
    """
    Database: Sensors (1000 tuples) and Readings (50,000 tuples).
    Test query: Sensors with at least one reading with value >= 80.
    Correct query: Sensors with at least two distinct readings (different timestamp) with value >= 80.
    Difference: Sensors with exactly one such reading.
    """
    num_sensors = 1000
    num_readings = 50000
    sensors = [{"sensor_id": i, "location": f"Location_{i}"} for i in range(1, num_sensors + 1)]
    readings = []
    for _ in range(num_readings):
        sid = random.randint(1, num_sensors)
        # For timestamp, use a random integer between 1 and 100000.
        timestamp = random.randint(1, 100000)
        value = random.randint(0, 100)
        readings.append({"sensor_id": sid, "timestamp": timestamp, "value": value})
    database = {"Sensors": sensors, "Readings": readings}
    threshold = 80
    test_query = RAProjection(
        ['sensor_id', 'location'],
        RAJoin(
            lambda s, r: s['sensor_id'] == r['sensor_id'] and r['value'] >= threshold,
            RATable("Sensors", database["Sensors"]),
            RATable("Readings", database["Readings"])
        )
    )
    r1 = RARename({"sensor_id": "sid1", "timestamp": "ts1", "value": "v1"}, RATable("Readings", database["Readings"]))
    r2 = RARename({"sensor_id": "sid2", "timestamp": "ts2", "value": "v2"}, RATable("Readings", database["Readings"]))
    reading_join = RAJoin(
        lambda a, b: a['sid1'] == b['sid2'] and a['ts1'] != b['ts2'] and a['v1'] >= threshold and b['v2'] >= threshold,
        r1, r2
    )
    correct_query = RAProjection(
        ['sensor_id', 'location'],
        RAJoin(
            lambda s, r: s['sensor_id'] == r['sid1'],
            RATable("Sensors", database["Sensors"]),
            reading_join
        )
    )
    diff_query = RADifference(test_query, correct_query)
    return database, diff_query, test_query


# Example 9: Online Course Enrollment Queries
def init_online_course_queries():
    """
    Database: Courses (200 tuples) and Enrollments (10,000 tuples).
    Test query: Courses with at least one enrollment.
    Correct query: Courses with enrollments in at least two distinct sections.
    Difference: Courses with enrollments in only one section.
    """
    num_courses = 200
    num_enrollments = 10000
    courses = [{"course_id": i, "course_name": f"Course_{i}", "term": "Fall2023"} for i in range(1, num_courses + 1)]
    enrollments = []
    sections = ["A", "B", "C", "D"]
    for _ in range(num_enrollments):
        cid = random.randint(1, num_courses)
        section = random.choice(sections)
        student = f"Student_{random.randint(1, 5000)}"
        enrollments.append({"course_id": cid, "section": section, "student_id": student})
    database = {"Courses": courses, "Enrollments": enrollments}
    test_query = RAProjection(
        ['course_id', 'course_name'],
        RAJoin(
            lambda c, e: c['course_id'] == e['course_id'],
            RATable("Courses", database["Courses"]),
            RATable("Enrollments", database["Enrollments"])
        )
    )
    e1 = RARename({"course_id": "cid1", "section": "sec1", "student_id": "stu1"},
                  RATable("Enrollments", database["Enrollments"]))
    e2 = RARename({"course_id": "cid2", "section": "sec2", "student_id": "stu2"},
                  RATable("Enrollments", database["Enrollments"]))
    enroll_join = RAJoin(
        lambda a, b: a['cid1'] == b['cid2'] and a['sec1'] != b['sec2'],
        e1, e2
    )
    correct_query = RAProjection(
        ['course_id', 'course_name'],
        RAJoin(
            lambda c, e: c['course_id'] == e['cid1'],
            RATable("Courses", database["Courses"]),
            enroll_join
        )
    )
    diff_query = RADifference(test_query, correct_query)
    return database, diff_query, test_query


# Example 10: Telecom Call Records Queries
def init_telecom_calls_queries():
    """
    Database: Subscribers (10,000 tuples) and Calls (100,000 tuples).
    Test query: Subscribers who made at least one call.
    Correct query: Subscribers who made calls to at least two distinct recipients.
    Difference: Subscribers who made calls to exactly one distinct recipient.
    """
    num_subs = 10000
    num_calls = 100000
    subscribers = [{"subscriber_id": i, "name": f"Sub_{i}"} for i in range(1, num_subs + 1)]
    calls = []
    for i in range(1, num_calls + 1):
        caller = random.randint(1, num_subs)
        callee = random.randint(1, num_subs)
        while callee == caller:
            callee = random.randint(1, num_subs)
        calls.append({"call_id": i, "caller_id": caller, "callee_id": callee})
    database = {"Subscribers": subscribers, "Calls": calls}
    test_query = RAProjection(
        ['subscriber_id', 'name'],
        RAJoin(
            lambda s, c: s['subscriber_id'] == c['caller_id'],
            RATable("Subscribers", database["Subscribers"]),
            RATable("Calls", database["Calls"])
        )
    )
    c1 = RARename({"caller_id": "caller1", "callee_id": "callee1", "call_id": "call1"},
                  RATable("Calls", database["Calls"]))
    c2 = RARename({"caller_id": "caller2", "callee_id": "callee2", "call_id": "call2"},
                  RATable("Calls", database["Calls"]))
    calls_join = RAJoin(
        lambda a, b: a['caller1'] == b['caller2'] and a['callee1'] != b['callee2'],
        c1, c2
    )
    correct_query = RAProjection(
        ['subscriber_id', 'name'],
        RAJoin(
            lambda s, c: s['subscriber_id'] == c['caller1'],
            RATable("Subscribers", database["Subscribers"]),
            calls_join
        )
    )
    diff_query = RADifference(test_query, correct_query)
    return database, diff_query, test_query


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
# TKINTER USER INTERFACE WITH 3 MODES (Notebook)
###############################################

class SPJUDUI:
    def __init__(self, root):
        self.root = root
        self.root.title("SPJUD Minimal Counterexample Finder")
        self.create_widgets()

    def create_widgets(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True)

        # Tab 1: Pre-defined Examples
        self.tab1 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab1, text="Pre-defined Examples")
        self.create_tab1_widgets(self.tab1)

        # Tab 2: User Entered JSON/SQL
        self.tab2 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab2, text="User Entered JSON/SQL")
        self.create_tab2_widgets(self.tab2)

        # Tab 3: File Upload
        self.tab3 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab3, text="File Upload")
        self.create_tab3_widgets(self.tab3)

    def create_tab1_widgets(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="x")
        ttk.Label(frm, text="Select Example:").grid(row=0, column=0, sticky="W")
        self.example_var = tk.StringVar(value="Toy Student Queries")
        self.example_combo = ttk.Combobox(frm, textvariable=self.example_var,
                                          values=list(EXAMPLE_MAPPING.keys()), state="readonly", width=40)
        self.example_combo.grid(row=0, column=1, padx=5, sticky="W")
        self.compute_button1 = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_predefined)
        self.compute_button1.grid(row=0, column=2, padx=10)
        self.text1 = tk.Text(frame, width=100, height=30)
        self.text1.pack(padx=10, pady=10)
        self.text1.tag_config("green", foreground="green")
        self.text1.tag_config("red", foreground="red")
        scrollbar = ttk.Scrollbar(frame, command=self.text1.yview)
        scrollbar.pack(side="right", fill="y")
        self.text1.config(yscrollcommand=scrollbar.set)

    def create_tab2_widgets(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="both", expand=True)
        ttk.Label(frm, text="Enter JSON (must include 'database', 'correct_query', 'wrong_query'):", wraplength=600).pack(anchor="w")
        self.text2_input = tk.Text(frm, width=100, height=15)
        self.text2_input.pack(padx=5, pady=5)
        self.compute_button2 = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_user_input)
        self.compute_button2.pack(pady=5)
        ttk.Label(frm, text="Results:").pack(anchor="w")
        self.text2_output = tk.Text(frm, width=100, height=15)
        self.text2_output.pack(padx=5, pady=5)
        self.text2_output.tag_config("green", foreground="green")
        self.text2_output.tag_config("red", foreground="red")
        scrollbar2 = ttk.Scrollbar(frm, command=self.text2_output.yview)
        scrollbar2.pack(side="right", fill="y")
        self.text2_output.config(yscrollcommand=scrollbar2.set)

    def create_tab3_widgets(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="both", expand=True)
        self.upload_button = ttk.Button(frm, text="Upload JSON File", command=self.upload_file)
        self.upload_button.pack(pady=5)
        ttk.Label(frm, text="File Content:").pack(anchor="w")
        self.text3_input = tk.Text(frm, width=100, height=10)
        self.text3_input.pack(padx=5, pady=5)
        self.compute_button3 = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_file_input)
        self.compute_button3.pack(pady=5)
        ttk.Label(frm, text="Results:").pack(anchor="w")
        self.text3_output = tk.Text(frm, width=100, height=10)
        self.text3_output.pack(padx=5, pady=5)
        self.text3_output.tag_config("green", foreground="green")
        self.text3_output.tag_config("red", foreground="red")
        scrollbar3 = ttk.Scrollbar(frm, command=self.text3_output.yview)
        scrollbar3.pack(side="right", fill="y")
        self.text3_output.config(yscrollcommand=scrollbar3.set)

    def display_queries(self, text_widget, correct_Q, wrong_Q):
        text_widget.insert(tk.END, "Correct Query:\n", "green")
        cq_str = ra_tree_to_string(correct_Q)
        text_widget.insert(tk.END, cq_str + "\n\n", "green")
        text_widget.insert(tk.END, "Wrong Query:\n", "red")
        wq_str = ra_tree_to_string(wrong_Q)
        text_widget.insert(tk.END, wq_str + "\n\n", "red")

    def display_counterexample(self, text_widget, ce, cost):
        """
        Displays the minimal counterexample using tabulate.
        We use headers="keys" to let tabulate infer column names from each dictionary.
        """
        if ce is None:
            text_widget.insert(tk.END, "Queries are equivalent on the given database.\n")
        else:
            text_widget.insert(tk.END, f"Minimal counterexample ({cost} tuple(s)) found:\n")
            for table, rows in ce.items():
                if rows:
                    # Use headers="keys" so tabulate doesn't complain
                    table_str = tabulate(rows, headers="keys", tablefmt="grid")
                    text_widget.insert(tk.END, f"\nTable {table}:\n{table_str}\n")

    def compute_predefined(self):
        example_name = self.example_var.get()
        init_func = EXAMPLE_MAPPING.get(example_name)
        self.text1.delete(1.0, tk.END)
        try:
            database, correct_Q, wrong_Q = init_func()
            self.display_queries(self.text1, correct_Q, wrong_Q)
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, database)
            self.display_counterexample(self.text1, ce, cost)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def compute_user_input(self):
        self.text2_output.delete(1.0, tk.END)
        json_text = self.text2_input.get(1.0, tk.END)
        try:
            database, correct_Q, wrong_Q = parse_user_input(json_text)
            self.display_queries(self.text2_output, correct_Q, wrong_Q)
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, database)
            self.display_counterexample(self.text2_output, ce, cost)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    def upload_file(self):
        filename = filedialog.askopenfilename(title="Select JSON File", filetypes=[("JSON Files", "*.json"), ("All Files", "*.*")])
        if filename:
            try:
                with open(filename, "r") as f:
                    content = f.read()
                self.text3_input.delete(1.0, tk.END)
                self.text3_input.insert(tk.END, content)
            except Exception as e:
                messagebox.showerror("Error", str(e))

    def compute_file_input(self):
        self.text3_output.delete(1.0, tk.END)
        json_text = self.text3_input.get(1.0, tk.END)
        try:
            database, correct_Q, wrong_Q = parse_user_input(json_text)
            self.display_queries(self.text3_output, correct_Q, wrong_Q)
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, database)
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
