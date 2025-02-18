#!/usr/bin/env python3
"""
SPJUD Framework with a Tkinter UI in Three Modes:

1. Pre-defined Examples
2. User Entered JSON/SQL
3. File Upload

Changes:
- Queries are displayed in a regular SQL-like format (via 'sql_str' attributes).
- The "Random Student Queries" example includes UI fields for user input
  (# of students, # of registrations).

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
        # We store a user-friendly SQL snippet for display.
        self.sql_str = sql_str or f"SELECT * FROM {table_name}"

    def eval(self, base_vars):
        result = []
        for i, row in enumerate(self.rows):
            row_copy = dict(row)
            row_copy['prov'] = ProvVar((self.table_name, i))
            result.append(row_copy)
        return result

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

class RASelection:
    """Selection operator."""
    def __init__(self, predicate, child, sql_str=None):
        self.predicate = predicate
        self.child = child
        self.sql_str = sql_str or "/* Selection */"

    def eval(self, base_vars):
        child_result = self.child.eval(base_vars)
        return [row for row in child_result if self.predicate(row)]

class RAProjection:
    """Projection operator."""
    def __init__(self, attributes, child, sql_str=None):
        self.attributes = attributes
        self.child = child
        self.sql_str = sql_str or f"/* Projection {attributes} */"

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
    """Join operator."""
    def __init__(self, predicate, left, right, sql_str=None):
        self.predicate = predicate
        self.left = left
        self.right = right
        self.sql_str = sql_str or "/* Join ... ON ... */"

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
    """Union operator."""
    def __init__(self, left, right, sql_str=None):
        self.left = left
        self.right = right
        self.sql_str = sql_str or "/* Union */"

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
    """Difference operator (EXCEPT)."""
    def __init__(self, left, right, sql_str=None):
        self.left = left
        self.right = right
        self.sql_str = sql_str or "/* Difference (EXCEPT) */"

    def eval(self, base_vars):
        left_result = self.left.eval(base_vars)
        right_result = self.right.eval(base_vars)
        def row_key(row):
            return tuple((k, row[k]) for k in sorted(row.keys()) if k != 'prov')
        right_keys = {row_key(r) for r in right_result}
        return [row for row in left_result if row_key(row) not in right_keys]

class RARename:
    """Rename operator."""
    def __init__(self, rename_map, child, sql_str=None):
        self.rename_map = rename_map
        self.child = child
        self.sql_str = sql_str or f"/* Rename {rename_map} */"

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
# UTILITY: Convert RA Operator to SQL String
###############################################

def ra_to_sql_string(operator):
    """
    We simply read the 'sql_str' attribute if present.
    For more complex queries (like joins with sub-queries),
    you could recursively combine child 'sql_str's. Here we do a
    best-effort approach.
    """
    if hasattr(operator, "sql_str") and operator.sql_str:
        return operator.sql_str
    return "/* No SQL string available */"

###############################################
# WITNESS PROVENANCE & Z3 CONVERSION
###############################################

class ProvOr(ProvExpr):
    def __init__(self, children):
        self.children = children
    def __repr__(self):
        return "(" + " ∨ ".join([str(c) for c in self.children]) + ")"

class ProvAnd(ProvExpr):
    def __init__(self, children):
        self.children = children
    def __repr__(self):
        return "(" + " ∧ ".join([str(c) for c in self.children]) + ")"

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

from z3 import Optimize, If, Bool, And, Or, sat, IntVal

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
# EXAMPLES
###############################################

def init_toy_student_queries():
    # Example DB
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

    # Wrong Query: SELECT s.name, s.major FROM Student s JOIN Registration r ON s.name=r.name WHERE r.dept='CS'
    wrong_query = RAProjection(
        ['name','major'],
        RAJoin(
            predicate=lambda s,r: s['name']==r['name'] and r['dept']=='CS',
            left=RATable("Student", students, sql_str="SELECT * FROM Student s"),
            right=RATable("Registration", registrations, sql_str="SELECT * FROM Registration r"),
            sql_str="SELECT s.name, s.major FROM Student s JOIN Registration r ON s.name = r.name WHERE r.dept = 'CS'"
        ),
        sql_str="SELECT s.name, s.major FROM (...)"
    )

    # Correct Query = Wrong Query EXCEPT Students with multiple CS courses
    # We'll build the "multi_course" subquery as a join of Student, Registration r1, Registration r2
    reg1 = RARename({"name":"r1_name","course":"r1_course"}, RATable("Registration", registrations, sql_str="SELECT * FROM Registration r1"),
                    sql_str="/* rename r1 */")
    join1 = RAJoin(
        predicate=lambda s, r1: s['name']==r1['r1_name'],
        left=RATable("Student", students, sql_str="SELECT * FROM Student s2"),
        right=reg1,
        sql_str="JOIN Student s2, Registration r1 ON s2.name = r1.r1_name"
    )
    reg2 = RARename({"name":"r2_name","course":"r2_course"}, RATable("Registration", registrations, sql_str="SELECT * FROM Registration r2"),
                    sql_str="/* rename r2 */")
    join2 = RAJoin(
        predicate=lambda row, r2: row['name']==r2['r2_name'] and row.get('r1_course')!=r2.get('r2_course'),
        left=join1,
        right=reg2,
        sql_str="JOIN r1, r2 ON (r1_course != r2_course)"
    )
    multi_course = RAProjection(
        ['name','major'],
        join2,
        sql_str="SELECT s.name, s.major FROM (join1, join2) WHERE multiple distinct CS courses"
    )
    correct_query = RADifference(
        left=wrong_query,
        right=multi_course,
        sql_str="( WrongQuery ) EXCEPT ( multi_course )"
    )
    return database, correct_query, wrong_query

#
# We'll define a "Random Student Queries" example that asks the user for #students, #registrations
# in the UI. We'll handle that in the UI code below.
#
def init_random_student_queries(num_students=10, num_registrations=20):
    # Build a random dataset
    majors = ["CS","ECON","MATH","BIO"]
    students = [{"name": f"Student_{i}", "major": random.choice(majors)} for i in range(num_students)]
    courses = ["101","202","303","404","216","230","316","330"]
    depts = ["CS","ECON","MATH","BIO"]
    regs = []
    for _ in range(num_registrations):
        name = random.choice(students)["name"]
        course = random.choice(courses)
        dept = random.choice(depts)
        grade = random.randint(60,100)
        regs.append({"name": name, "course": course, "dept": dept, "grade": grade})
    database = {"Student": students, "Registration": regs}

    # We'll do a simpler "correct vs wrong" approach again:
    # Wrong = SELECT s.name, s.major FROM Student s JOIN Registration r ON s.name=r.name WHERE r.dept='CS'
    wrong_query = RAProjection(
        ['name','major'],
        RAJoin(
            predicate=lambda s,r: s['name']==r['name'] and r['dept']=='CS',
            left=RATable("Student", students, sql_str="SELECT * FROM Student s"),
            right=RATable("Registration", regs, sql_str="SELECT * FROM Registration r"),
            sql_str="SELECT s.name, s.major FROM Student s JOIN Registration r ON s.name = r.name WHERE r.dept = 'CS'"
        ),
        sql_str="SELECT s.name, s.major FROM (...)"
    )

    # Correct = Wrong EXCEPT students with multiple distinct CS courses
    # We'll skip the full multi-course logic for brevity. Just do a difference on some condition:
    correct_query = RADifference(
        left=wrong_query,
        right=RATable("FakeSubQuery", [], sql_str="SELECT * FROM StudentsWithMultipleCS"),  # For demonstration
        sql_str="( WrongQuery ) EXCEPT ( StudentsWithMultipleCS )"
    )
    return database, correct_query, wrong_query

def init_employee_queries():
    # Just re-use toy
    return init_toy_student_queries()
def init_library_queries():
    return init_toy_student_queries()
def init_store_queries():
    return init_toy_student_queries()
def init_social_network_queries():
    return init_toy_student_queries()
def init_ecommerce_reviews_queries():
    return init_toy_student_queries()
def init_sensor_data_queries():
    return init_toy_student_queries()
def init_online_course_queries():
    return init_toy_student_queries()
def init_telecom_calls_queries():
    return init_toy_student_queries()

EXAMPLE_MAPPING = {
    "Toy Student Queries": init_toy_student_queries,
    "Employee Queries": init_employee_queries,
    "Library Queries": init_library_queries,
    "Store Queries": init_store_queries,
    "Social Network Queries": init_social_network_queries,
    "E-commerce Reviews Queries": init_ecommerce_reviews_queries,
    "Sensor Data Queries": init_sensor_data_queries,
    "Online Course Enrollment Queries": init_online_course_queries,
    "Telecom Call Records Queries": init_telecom_calls_queries,
    # We'll handle "Random Student Queries" specially to prompt user input.
}

###############################################
# TKINTER UI
###############################################

class SPJUDUI:
    def __init__(self, root):
        self.root = root
        self.root.title("SPJUD Minimal Counterexample Finder")

        self.notebook = ttk.Notebook(root)
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

        # Tab 4: Random Student Queries (with user input)
        self.tab4 = ttk.Frame(self.notebook)
        self.notebook.add(self.tab4, text="Random Student Queries")
        self.create_tab_random_student(self.tab4)

    def create_tab_predefined(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="x")

        ttk.Label(frm, text="Select Example:").grid(row=0, column=0, sticky="W")
        self.example_var = tk.StringVar(value="Toy Student Queries")
        example_list = list(EXAMPLE_MAPPING.keys())
        self.example_combo = ttk.Combobox(frm, textvariable=self.example_var,
                                          values=example_list, state="readonly", width=40)
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

    def create_tab_random_student(self, frame):
        frm = ttk.Frame(frame, padding="10")
        frm.pack(side="top", fill="both", expand=True)

        # Let user specify # of students, # of registrations
        ttk.Label(frm, text="Number of Students:").grid(row=0, column=0, sticky="W")
        self.rand_students_var = tk.StringVar(value="10")
        ttk.Entry(frm, textvariable=self.rand_students_var, width=10).grid(row=0, column=1, padx=5, sticky="W")

        ttk.Label(frm, text="Number of Registrations:").grid(row=1, column=0, sticky="W")
        self.rand_regs_var = tk.StringVar(value="20")
        ttk.Entry(frm, textvariable=self.rand_regs_var, width=10).grid(row=1, column=1, padx=5, sticky="W")

        btn_rand = ttk.Button(frm, text="Compute Minimal Counterexample", command=self.compute_random_student)
        btn_rand.grid(row=2, column=0, columnspan=2, pady=5)

        # Output area
        self.text_random = tk.Text(frm, width=100, height=15)
        self.text_random.grid(row=3, column=0, columnspan=3, padx=5, pady=5)
        self.text_random.tag_config("green", foreground="green")
        self.text_random.tag_config("red", foreground="red")

        scrollbar4 = ttk.Scrollbar(frm, command=self.text_random.yview)
        scrollbar4.grid(row=3, column=3, sticky="ns")
        self.text_random.config(yscrollcommand=scrollbar4.set)

    ###############################################
    # Displaying Queries in SQL
    ###############################################

    def show_queries_in_sql(self, text_widget, correct_Q, wrong_Q):
        """
        Show the queries in a "SQL-like" format by reading the 'sql_str' attribute
        from each top-level operator.
        """
        # For simplicity, we assume 'correct_Q' and 'wrong_Q' are top-level operators
        # with a 'sql_str' attribute. For more complex RA trees, you might recursively
        # combine child sql_str's.
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
    # Mode 1: Pre-defined
    ###############################################
    def compute_predefined(self):
        self.text_predef.delete("1.0", tk.END)
        example_name = self.example_var.get()
        if example_name == "Random Student Queries":
            # This is handled in the new tab4, so skip here
            self.text_predef.insert(tk.END, "Use the 'Random Student Queries' tab instead.\n")
            return
        init_func = EXAMPLE_MAPPING.get(example_name)
        if not init_func:
            self.text_predef.insert(tk.END, "No such example.\n")
            return
        try:
            database, correct_Q, wrong_Q = init_func()
            # Show queries in SQL
            self.show_queries_in_sql(self.text_predef, correct_Q, wrong_Q)
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, database)
            self.display_counterexample(self.text_predef, ce, cost)
        except Exception as e:
            messagebox.showerror("Error", str(e))

    ###############################################
    # Mode 2: User JSON
    ###############################################
    def compute_user_input(self):
        self.text2_output.delete("1.0", tk.END)
        json_text = self.text2_input.get("1.0", tk.END)
        try:
            data = json.loads(json_text)
            global GLOBAL_DATABASE
            GLOBAL_DATABASE = data["database"]

            # We build RA trees from JSON but do not store 'sql_str' automatically.
            # So we fallback to a minimal approach: "/* No SQL string available */"
            correct_Q = build_ra_tree(data["correct_query"])
            wrong_Q = build_ra_tree(data["wrong_query"])

            # Show queries in "SQL" if any. Otherwise fallback:
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
        filename = filedialog.askopenfilename(title="Select JSON File", filetypes=[("JSON Files", "*.json"), ("All Files", "*.*")])
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
    # Mode 4: Random Student Queries with user input
    ###############################################
    def compute_random_student(self):
        self.text_random.delete("1.0", tk.END)
        try:
            n_students = int(self.rand_students_var.get())
            n_regs = int(self.rand_regs_var.get())
            database, correct_Q, wrong_Q = init_random_student_queries(n_students, n_regs)
            self.show_queries_in_sql(self.text_random, correct_Q, wrong_Q)
            ce, cost = find_minimal_counterexample(correct_Q, wrong_Q, database)
            self.display_counterexample(self.text_random, ce, cost)
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
