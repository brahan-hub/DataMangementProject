#!/usr/bin/env python3
"""
SPJUD Framework with 10 Diverse Examples

This program implements a provenance‐based approach for explaining differences
between two SPJUD queries (Select, Project, Join, Union, Difference) using Z3
optimization to find a minimal counterexample.

Five examples (Examples 1-5) are similar to earlier toy datasets, while five
new examples (Examples 6-10) generate random datasets of varying sizes (between
100 and 100,000 tuples) and use different SPJUD query patterns.
"""

import random
from z3 import Optimize, If, Bool, And, Or, sat, IntVal


###############################################
# PROVENANCE EXPRESSION CLASSES
###############################################

class ProvExpr:
    """Base class for provenance expressions."""
    pass


class ProvVar(ProvExpr):
    """A base variable (i.e. an input tuple). 'var' is a tuple like (table_name, row_index)."""

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
    """
    A base table. 'rows' is a list of dictionaries representing tuples.
    Each tuple is annotated with a provenance variable.
    """

    def __init__(self, table_name, rows):
        self.table_name = table_name
        self.rows = rows

    def eval(self, base_vars):
        result = []
        for i, row in enumerate(self.rows):
            row_copy = dict(row)  # shallow copy
            row_copy['prov'] = ProvVar((self.table_name, i))
            result.append(row_copy)
        return result


class RASelection:
    """
    Selection operator. 'predicate' is a function that takes a row (a dict) and returns True/False.
    """

    def __init__(self, predicate, child):
        self.predicate = predicate
        self.child = child

    def eval(self, base_vars):
        child_result = self.child.eval(base_vars)
        return [row for row in child_result if self.predicate(row)]


class RAProjection:
    """
    Projection operator. 'attributes' is a list of attribute names to keep.
    When multiple input tuples project to the same output, their provenances are OR-ed.
    """

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


class RAJoin:
    """
    Join operator. 'predicate' is a function that takes two rows (from left and right) and returns True/False.
    The joined tuple’s provenance is the AND of the input provenances.
    """

    def __init__(self, predicate, left, right):
        self.predicate = predicate
        self.left = left
        self.right = right

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


class RAUnion:
    """
    Union operator. Tuples with the same non-provenance attributes are merged (their provenances are OR-ed).
    """

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


class RADifference:
    """
    Difference operator. Returns tuples from the left that do not appear in the right (ignoring provenance).
    """

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


class RARename:
    """
    Rename operator. 'rename_map' is a dict mapping old attribute names to new names.
    This operator renames all attributes (except 'prov') of each tuple.
    """

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


###############################################
# WITNESS PROVENANCE & Z3 CONVERSION
###############################################

def compute_witness_provenance(q1_rows, q2_rows):
    """
    Given outputs (with provenance) of two queries, compute a witness for inequivalence.
    For tuples that appear only in one query, collect their provenance expressions.
    Returns a single provenance expression (OR-ed) or None if the queries are equivalent.
    """

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
    """
    Convert a provenance expression into a Z3 Boolean formula.
    'base_vars' maps base tuple identifiers to Z3 Bool variables.
    """
    if isinstance(prov, ProvVar):
        return base_vars[prov.var]
    elif isinstance(prov, ProvAnd):
        return And([prov_to_z3(child, base_vars) for child in prov.children])
    elif isinstance(prov, ProvOr):
        return Or([prov_to_z3(child, base_vars) for child in prov.children])
    else:
        raise ValueError("Unknown provenance expression type")


def create_base_vars(database):
    """
    Given a database (dict: table_name -> list-of-rows), create a dict mapping
    (table_name, row_index) to a Z3 Bool variable.
    """
    base_vars = {}
    for table_name, rows in database.items():
        for i, _ in enumerate(rows):
            base_vars[(table_name, i)] = Bool(f"in_{table_name}_{i}")
    return base_vars


###############################################
# MINIMAL COUNTEREXAMPLE EXTRACTION
###############################################

def find_minimal_counterexample(Q1, Q2, database):
    """
    Given two RA query trees Q1 and Q2 and a database (dict mapping table names to rows),
    evaluate Q1 and Q2 (which produce provenance-annotated results), compute a witness for inequivalence,
    convert that witness into a Z3 formula over base tuple indicators, and then use Z3's Optimize to
    find the smallest subset of base tuples that witness the difference.

    Returns a tuple (counterexample, cost) where counterexample is a dict mapping table names to a list of
    rows (from the original database) included in the counterexample, and cost is the total count.
    If Q1 and Q2 are equivalent, returns (None, 0).
    """
    base_vars = create_base_vars(database)
    q1_rows = Q1.eval(base_vars)
    q2_rows = Q2.eval(base_vars)
    witness_prov = compute_witness_provenance(q1_rows, q2_rows)
    if witness_prov is None:
        print("Queries are equivalent on the given database.")
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
        print("No solution found.")
        return None, None


###############################################
# EXAMPLES 1-5 (Toy/Benchmark Examples)
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


###############################################
# MAIN DRIVER
###############################################

def main():
    examples = {
        "1": ("Toy Student Queries Example", init_toy_student_queries),
        "2": ("Random Student Queries Example", init_random_student_queries),
        "3": ("Employee Queries Example", init_employee_queries),
        "4": ("Library Queries Example", init_library_queries),
        "5": ("Store Queries Example", init_store_queries),
        "6": ("Social Network Queries Example", init_social_network_queries),
        "7": ("E-commerce Reviews Queries Example", init_ecommerce_reviews_queries),
        "8": ("Sensor Data Queries Example", init_sensor_data_queries),
        "9": ("Online Course Enrollment Queries Example", init_online_course_queries),
        "10": ("Telecom Call Records Queries Example", init_telecom_calls_queries)
    }
    print("Select an example to run:")
    for key, (desc, _) in examples.items():
        print(f"  {key}. {desc}")
    choice = input("Enter choice (1-10): ").strip()
    if choice not in examples:
        print("Invalid choice.")
        return
    desc, init_func = examples[choice]
    print(f"\n=== {desc} ===")
    database, correct_Q, test_Q = init_func()
    print("\nRunning minimal counterexample extraction...")
    ce, cost = find_minimal_counterexample(correct_Q, test_Q, database)
    if ce is not None:
        print(f"Minimal counterexample ({cost} tuple(s)) found:")
        for table, rows in ce.items():
            print(f"Table {table}:")
            for row in rows:
                print("  ", row)
    else:
        print("No counterexample found (queries are equivalent).")


if __name__ == "__main__":
    main()
