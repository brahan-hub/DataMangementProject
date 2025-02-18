# #!/usr/bin/env python3
# """
# Full implementation for SPJUD queries (Select, Project, Join, Union, Difference)
# with provenance tracking and minimal counterexample extraction via Z3 SMT/Optimize.
#
# This implementation defines:
#   - A simple Boolean provenance language (variables, AND, OR).
#   - Relational-algebra operators as classes:
#       RATable, RASelection, RAProjection, RAJoin, RAUnion, RADifference.
#   - A function to compute the “witness” provenance from the difference between two queries.
#   - A function to convert a provenance expression into a Z3 Boolean formula.
#   - A function to build base tuple indicator variables.
#   - A driver function to extract a minimal counterexample (smallest set of base tuples
#     that forces Q₁ and Q₂ to produce different outputs).
#
# An example is provided at the end using a join query over two tables (“Employees” and “Departments”).
# """
#
# from z3 import Optimize, If, Bool, And, Or, sat, IntVal
#
#
# # === Provenance Expression Classes ===
#
# class ProvExpr:
#     """Base class for provenance expressions."""
#     pass
#
#
# class ProvVar(ProvExpr):
#     """A base variable (i.e. an input tuple). 'var' is a tuple like (table_name, row_index)."""
#
#     def __init__(self, var):
#         self.var = var
#
#     def __repr__(self):
#         return f"{self.var}"
#
#
# class ProvAnd(ProvExpr):
#     """AND of a list of provenance expressions."""
#
#     def __init__(self, children):
#         # Flatten nested AND's if desired.
#         self.children = children
#
#     def __repr__(self):
#         return "(" + " ∧ ".join([str(c) for c in self.children]) + ")"
#
#
# class ProvOr(ProvExpr):
#     """OR of a list of provenance expressions."""
#
#     def __init__(self, children):
#         self.children = children
#
#     def __repr__(self):
#         return "(" + " ∨ ".join([str(c) for c in self.children]) + ")"
#
#
# # === Relational Algebra Operator Classes ===
#
# class RATable:
#     """
#     A base table. 'rows' is a list of dictionaries (each dictionary is a tuple).
#     When evaluated, each row is annotated with a provenance variable (of the form (table_name, index)).
#     """
#
#     def __init__(self, table_name, rows):
#         self.table_name = table_name
#         self.rows = rows  # rows should not contain a 'prov' field
#
#     def eval(self, base_vars):
#         result = []
#         for i, row in enumerate(self.rows):
#             row_copy = dict(row)  # shallow copy of row data
#             # Annotate provenance with a variable for the base tuple.
#             row_copy['prov'] = ProvVar((self.table_name, i))
#             result.append(row_copy)
#         return result
#
#
# class RASelection:
#     """
#     Selection operator. 'predicate' is a function that takes a row (a dict) and returns True/False.
#     """
#
#     def __init__(self, predicate, child):
#         self.predicate = predicate
#         self.child = child
#
#     def eval(self, base_vars):
#         child_result = self.child.eval(base_vars)
#         result = []
#         for row in child_result:
#             if self.predicate(row):
#                 result.append(row)
#         return result
#
#
# class RAProjection:
#     """
#     Projection operator. 'attributes' is a list of attribute names to keep.
#     If multiple input tuples project to the same output tuple, their provenances are OR-ed.
#     """
#
#     def __init__(self, attributes, child):
#         self.attributes = attributes
#         self.child = child
#
#     def eval(self, base_vars):
#         child_result = self.child.eval(base_vars)
#         proj_dict = {}  # mapping from projected key -> provenance expression
#         for row in child_result:
#             key = tuple(row[attr] for attr in self.attributes)
#             if key in proj_dict:
#                 # OR the provenance expressions.
#                 existing = proj_dict[key]
#                 if isinstance(existing, ProvOr):
#                     new_children = existing.children + [row['prov']]
#                     proj_dict[key] = ProvOr(new_children)
#                 else:
#                     proj_dict[key] = ProvOr([existing, row['prov']])
#             else:
#                 proj_dict[key] = row['prov']
#         # Build result rows.
#         result = []
#         for key, prov in proj_dict.items():
#             new_row = {attr: value for attr, value in zip(self.attributes, key)}
#             new_row['prov'] = prov
#             result.append(new_row)
#         return result
#
#
# class RAJoin:
#     """
#     Join operator. 'predicate' is a function that takes two rows (one from left, one from right) and returns True/False.
#     The resulting row is the union of the two rows and its provenance is the AND of the input provenances.
#     """
#
#     def __init__(self, predicate, left, right):
#         self.predicate = predicate
#         self.left = left
#         self.right = right
#
#     def eval(self, base_vars):
#         left_result = self.left.eval(base_vars)
#         right_result = self.right.eval(base_vars)
#         result = []
#         for l in left_result:
#             for r in right_result:
#                 # Check join condition.
#                 if self.predicate(l, r):
#                     # Combine rows. (Assumes no attribute name conflicts.)
#                     combined = {**l, **r}
#                     combined['prov'] = ProvAnd([l['prov'], r['prov']])
#                     result.append(combined)
#         return result
#
#
# class RAUnion:
#     """
#     Union operator. The result contains all tuples from both inputs. If the same tuple (ignoring provenance)
#     appears from both branches, their provenances are OR-ed.
#     """
#
#     def __init__(self, left, right):
#         self.left = left
#         self.right = right
#
#     def eval(self, base_vars):
#         left_result = self.left.eval(base_vars)
#         right_result = self.right.eval(base_vars)
#         union_dict = {}
#
#         def row_key(row):
#             # Key is all attributes except provenance.
#             return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
#
#         for row in left_result:
#             key = row_key(row)
#             union_dict[key] = dict(row)
#         for row in right_result:
#             key = row_key(row)
#             if key in union_dict:
#                 existing = union_dict[key]['prov']
#                 if isinstance(existing, ProvOr):
#                     union_dict[key]['prov'] = ProvOr(existing.children + [row['prov']])
#                 else:
#                     union_dict[key]['prov'] = ProvOr([existing, row['prov']])
#             else:
#                 union_dict[key] = dict(row)
#         return list(union_dict.values())
#
#
# class RADifference:
#     """
#     Difference operator. Returns tuples from the left that do not appear in the right (based on non-provenance attributes).
#     Provenance is inherited from the left.
#     """
#
#     def __init__(self, left, right):
#         self.left = left
#         self.right = right
#
#     def eval(self, base_vars):
#         left_result = self.left.eval(base_vars)
#         right_result = self.right.eval(base_vars)
#
#         def row_key(row):
#             return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
#
#         right_keys = {row_key(r) for r in right_result}
#         result = []
#         for row in left_result:
#             if row_key(row) not in right_keys:
#                 result.append(row)
#         return result
#
#
# # === Witness Provenance and Z3 Conversion ===
#
# def compute_witness_provenance(q1_rows, q2_rows):
#     """
#     Given the output (with provenance) of two queries, compute a witness for inequivalence.
#     For tuples that appear only in Q₁ or only in Q₂, we OR their provenance expressions.
#     If the queries are equivalent, return None.
#     """
#
#     def row_key(row):
#         return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
#
#     q1_dict = {}
#     for row in q1_rows:
#         key = row_key(row)
#         if key in q1_dict:
#             existing = q1_dict[key]
#             if isinstance(existing, ProvOr):
#                 q1_dict[key] = ProvOr(existing.children + [row['prov']])
#             else:
#                 q1_dict[key] = ProvOr([existing, row['prov']])
#         else:
#             q1_dict[key] = row['prov']
#     q2_dict = {}
#     for row in q2_rows:
#         key = row_key(row)
#         if key in q2_dict:
#             existing = q2_dict[key]
#             if isinstance(existing, ProvOr):
#                 q2_dict[key] = ProvOr(existing.children + [row['prov']])
#             else:
#                 q2_dict[key] = ProvOr([existing, row['prov']])
#         else:
#             q2_dict[key] = row['prov']
#     witness_exprs = []
#     # Tuples in Q1 but not in Q2.
#     for key, prov in q1_dict.items():
#         if key not in q2_dict:
#             witness_exprs.append(prov)
#     # Tuples in Q2 but not in Q1.
#     for key, prov in q2_dict.items():
#         if key not in q1_dict:
#             witness_exprs.append(prov)
#     if not witness_exprs:
#         return None
#     if len(witness_exprs) == 1:
#         return witness_exprs[0]
#     return ProvOr(witness_exprs)
#
#
# def prov_to_z3(prov, base_vars):
#     """
#     Recursively convert a provenance expression into a Z3 Boolean formula.
#     'base_vars' is a dict mapping base tuple identifiers (e.g. ("Employees", 0)) to Z3 Bool variables.
#     """
#     if isinstance(prov, ProvVar):
#         return base_vars[prov.var]
#     elif isinstance(prov, ProvAnd):
#         return And([prov_to_z3(child, base_vars) for child in prov.children])
#     elif isinstance(prov, ProvOr):
#         return Or([prov_to_z3(child, base_vars) for child in prov.children])
#     else:
#         raise ValueError("Unknown provenance expression type")
#
#
# def create_base_vars(database):
#     """
#     Given a database (a dict mapping table names to list-of-rows),
#     create a dictionary mapping (table_name, row_index) to a Z3 Bool variable.
#     """
#     base_vars = {}
#     for table_name, rows in database.items():
#         for i, _ in enumerate(rows):
#             base_vars[(table_name, i)] = Bool(f"in_{table_name}_{i}")
#     return base_vars
#
#
# # === Minimal Counterexample Extraction ===
#
# def find_minimal_counterexample(Q1, Q2, database):
#     """
#     Given two RA query trees Q1 and Q2 and a database (dict: table_name -> rows),
#     evaluate Q1 and Q2 (which produce provenance-annotated results), compute a witness of inequivalence,
#     convert the witness to a Z3 formula over base tuple indicators, and use Z3's Optimize to minimize
#     the number of base tuples (i.e. find a smallest counterexample).
#
#     Returns a tuple (counterexample, cost) where 'counterexample' is a dict mapping table names to a list
#     of rows (from the original database) included in the minimal counterexample, and 'cost' is the total number
#     of tuples selected. If Q1 and Q2 are equivalent on the database, returns (None, 0).
#     """
#     # Create base tuple indicator variables.
#     base_vars = create_base_vars(database)
#
#     # Evaluate the queries.
#     q1_rows = Q1.eval(base_vars)
#     q2_rows = Q2.eval(base_vars)
#
#     # Compute witness provenance (difference between Q1 and Q2 outputs).
#     witness_prov = compute_witness_provenance(q1_rows, q2_rows)
#     if witness_prov is None:
#         print("Queries are equivalent on the given database.")
#         return None, 0
#
#     # Convert witness provenance into a Z3 constraint.
#     witness_z3 = prov_to_z3(witness_prov, base_vars)
#
#     # Set up the Optimize solver.
#     opt = Optimize()
#     opt.add(witness_z3)
#
#     # Objective: minimize the sum of base tuple indicator variables.
#     cost_expr = sum([If(var, 1, 0) for var in base_vars.values()])
#     opt.minimize(cost_expr)
#
#     if opt.check() == sat:
#         model = opt.model()
#         counterexample = {}
#         for (table, idx), var in base_vars.items():
#             if model.evaluate(var):
#                 if table not in counterexample:
#                     counterexample[table] = []
#                 # Include the original tuple from the database.
#                 counterexample[table].append(database[table][idx])
#         total = sum([1 for var in base_vars.values() if model.evaluate(var)])
#         return counterexample, total
#     else:
#         print("No solution found.")
#         return None, None
#
#
# # === Example Usage: SPJUD Query with Join, Projection, and Selection ===
#
# if __name__ == "__main__":
#     # Define a sample database with two tables.
#     employees_data = [
#         {"name": "Alice", "salary": 60000, "dept_id": 1},
#         {"name": "Bob", "salary": 50000, "dept_id": 2},  # Boundary case.
#         {"name": "Charlie", "salary": 40000, "dept_id": 1}
#     ]
#     departments_data = [
#         {"id": 1, "dept_name": "Sales"},
#         {"id": 2, "dept_name": "HR"}
#     ]
#     # Organize database as a dict.
#     database = {
#         "Employees": employees_data,
#         "Departments": departments_data
#     }
#
#     # Build two queries that join Employees and Departments and project (name, dept_name).
#     # Q1 (correct query): select employees with salary > 50000.
#     Q1 = RAProjection(
#         ['name', 'dept_name'],
#         RASelection(
#             lambda row: row['salary'] > 50000,
#             RAJoin(
#                 lambda l, r: l['dept_id'] == r['id'],
#                 RATable("Employees", employees_data),
#                 RATable("Departments", departments_data)
#             )
#         )
#     )
#
#     # Q2 (erroneous query): select employees with salary >= 50000.
#     Q2 = RAProjection(
#         ['name', 'dept_name'],
#         RASelection(
#             lambda row: row['salary'] >= 50000,
#             RAJoin(
#                 lambda l, r: l['dept_id'] == r['id'],
#                 RATable("Employees", employees_data),
#                 RATable("Departments", departments_data)
#             )
#         )
#     )
#
#     # Find the minimal counterexample (a smallest subset of base tuples showing Q1 != Q2).
#     counterexample, cost = find_minimal_counterexample(Q1, Q2, database)
#
#     if counterexample is not None:
#         print("Minimal counterexample ({} tuple(s)) found:".format(cost))
#         for table, rows in counterexample.items():
#             print(f"Table {table}:")
#             for row in rows:
#                 print("  ", row)
#     else:
#         print("No counterexample found (the queries appear equivalent).")
# !/usr/bin/env python3
"""
Full SPJUD implementation with provenance tracking and minimal counterexample extraction,
plus three toy example initializers for Student/Registration and Employee/Salary datasets.
"""

import random
from z3 import Optimize, If, Bool, And, Or, Xor, IntVal, sat


# === Provenance Expression Classes ===

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


# === Relational Algebra Operator Classes ===

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
            # Annotate with provenance variable (the base tuple indicator)
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
        result = []
        for row in child_result:
            if self.predicate(row):
                result.append(row)
        return result


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
        proj_dict = {}  # key: projected tuple; value: provenance expression
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
        result = []
        for row in left_result:
            if row_key(row) not in right_keys:
                result.append(row)
        return result


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


# === Witness Provenance and Z3 Conversion ===

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
    # Tuples in Q1 but not in Q2.
    for key, prov in q1_dict.items():
        if key not in q2_dict:
            witness_exprs.append(prov)
    # Tuples in Q2 but not in Q1.
    for key, prov in q2_dict.items():
        if key not in q1_dict:
            witness_exprs.append(prov)
    if not witness_exprs:
        return None
    if len(witness_exprs) == 1:
        return witness_exprs[0]
    return ProvOr(witness_exprs)


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


# === Minimal Counterexample Extraction ===

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
                if table not in counterexample:
                    counterexample[table] = []
                counterexample[table].append(database[table][idx])
        total = sum([1 for var in base_vars.values() if model.evaluate(var)])
        return counterexample, total
    else:
        print("No solution found.")
        return None, None


# === Toy Example Initializers ===

def create_toy_database():
    """
    Returns a dictionary with two tables: 'Student' and 'Registration'
    (each as a list of dictionaries).
    """
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


def create_random_student_dataset():
    """
    Prompts the user for number of students and registrations,
    then returns a random dataset as a dictionary.
    """
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


def init_toy_student_queries():
    """
    Builds RA trees for the toy student queries.
    The correct query removes students with multiple distinct course registrations in 'CS'
    (using EXCEPT/Difference) while the test query does not.
    """
    database = create_toy_database()
    # Test Query:
    # SELECT s.name, s.major FROM Student s, Registration r
    # WHERE s.name = r.name AND r.dept = 'CS';
    student_test_query = RAProjection(
        ['name', 'major'],
        RAJoin(
            lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            RATable("Student", database["Student"]),
            RATable("Registration", database["Registration"])
        )
    )
    # Correct Query:
    # (L) Same as test query.
    L = RAProjection(
        ['name', 'major'],
        RAJoin(
            lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            RATable("Student", database["Student"]),
            RATable("Registration", database["Registration"])
        )
    )
    # (R) Students with more than one distinct CS course:
    # Build join: Student ⋈ Registration AS r1 (with alias) on s.name = r1_name and r1_dept = 'CS'
    reg1 = RARename({"name": "r1_name", "course": "r1_course", "dept": "r1_dept", "grade": "r1_grade"},
                    RATable("Registration", database["Registration"]))
    join1 = RAJoin(
        lambda s, r1: s['name'] == r1['r1_name'] and r1['r1_dept'] == 'CS',
        RATable("Student", database["Student"]),
        reg1
    )
    # Join the above result with a second Registration (r2) where course differs.
    reg2 = RARename({"name": "r2_name", "course": "r2_course", "dept": "r2_dept", "grade": "r2_grade"},
                    RATable("Registration", database["Registration"]))
    join2 = RAJoin(
        lambda j, r2: j['name'] == r2['r2_name'] and j['r1_course'] != r2['r2_course'] and r2['r2_dept'] == 'CS',
        join1,
        reg2
    )
    R = RAProjection(['name', 'major'], join2)
    student_correct_query = RADifference(L, R)
    return database, student_correct_query, student_test_query


def init_random_student_queries():
    """
    Similar to init_toy_student_queries(), but using a random student dataset.
    """
    database = create_random_student_dataset()
    student_test_query = RAProjection(
        ['name', 'major'],
        RAJoin(
            lambda s, r: s['name'] == r['name'] and r['dept'] == 'CS',
            RATable("Student", database["Student"]),
            RATable("Registration", database["Registration"])
        )
    )
    L = RAProjection(
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
        lambda j, r2: j['name'] == r2['r2_name'] and j['r1_course'] != r2['r2_course'] and r2['r2_dept'] == 'CS',
        join1,
        reg2
    )
    R = RAProjection(['name', 'major'], join2)
    student_correct_query = RADifference(L, R)
    return database, student_correct_query, student_test_query


def create_employee_database():
    """
    Returns a simple employee database with two tables: 'Employee' and 'Salary'.
    """
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
    """
    Builds RA trees for the employee queries.
    The correct query excludes employees whose 2023 salary is greater than what they earned in 2022.
    (The EXCEPT query removes employees who have a 2022 salary that is lower than their 2023 salary.)
    """
    database = create_employee_database()
    # Test Query:
    # SELECT e.name, e.department FROM Employee e, Salary s
    # WHERE e.emp_id = s.emp_id AND s.year = 2023;
    employee_test_query = RAProjection(
        ['name', 'department'],
        RAJoin(
            lambda e, s: e['emp_id'] == s['emp_id'] and s['year'] == 2023,
            RATable("Employee", database["Employee"]),
            RATable("Salary", database["Salary"])
        )
    )
    # Left part L (same as test query)
    L = RAProjection(
        ['name', 'department'],
        RAJoin(
            lambda e, s: e['emp_id'] == s['emp_id'] and s['year'] == 2023,
            RATable("Employee", database["Employee"]),
            RATable("Salary", database["Salary"])
        )
    )
    # Right part R: Employees with a 2022 salary lower than 2023 salary.
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
        lambda j, s2: j['emp_id'] == s2['s2_emp_id'] and s2['s2_year'] == 2023 and j['s1_amount'] < s2['s2_amount'],
        join1,
        sal2
    )
    R = RAProjection(['name', 'department'], join2)
    employee_correct_query = RADifference(L, R)
    return database, employee_correct_query, employee_test_query


# === Main Driver ===

if __name__ == "__main__":
    # Uncomment one of the following examples to test:

    print("=== Toy Student Queries Example ===")
    db, correct_Q, test_Q = init_toy_student_queries()
    ce, cost = find_minimal_counterexample(correct_Q, test_Q, db)
    if ce is not None:
        print("Minimal counterexample ({} tuple(s)) found:".format(cost))
        for table, rows in ce.items():
            print(f"Table {table}:")
            for row in rows:
                print("  ", row)
    print("\n-------------------------\n")

    # Uncomment to run the random student dataset example:
    print("=== Random Student Queries Example ===")
    db, correct_Q, test_Q = init_random_student_queries()
    ce, cost = find_minimal_counterexample(correct_Q, test_Q, db)
    if ce is not None:
        print("Minimal counterexample ({} tuple(s)) found:".format(cost))
        for table, rows in ce.items():
            print(f"Table {table}:")
            for row in rows:
                print("  ", row)
    print("\n-------------------------\n")

    # Uncomment to run the employee queries example:
    print("=== Employee Queries Example ===")
    db, correct_Q, test_Q = init_employee_queries()
    ce, cost = find_minimal_counterexample(correct_Q, test_Q, db)
    if ce is not None:
        print("Minimal counterexample ({} tuple(s)) found:".format(cost))
        for table, rows in ce.items():
            print(f"Table {table}:")
            for row in rows:
                print("  ", row)
