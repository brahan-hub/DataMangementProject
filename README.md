# SPJUD Queries and Provenance Computation Project

## Project Overview

The goal of the project is to handle **SPJUD** queries (Select, Project, Join, Union, Difference) and compute provenance for these queries using a SAT solver (Z3). The project also includes a GUI interface for testing and experimenting with the system. This project was implemented in accordance with the methodology outlined in the paper **"[Explaining wrong queries using small examples](https://dl.acm.org/doi/pdf/10.1145/3299869.3319866)"**.

## 1. Description of Algorithms Implemented

### SPJUD Queries

- **Select**: Selects rows from a relation based on a condition.
- **Project**: Projects specific columns (attributes) from a relation.
- **Join**: Joins two relations based on a condition (predicate).
- **Union**: Unions the results of two relations, combining their rows while removing duplicates.
- **Difference**: Computes the difference between two relations, returning tuples that are in the left but not in the right.

### Provenance Computation

The project computes **provenance** for the results of SPJUD queries. Provenance tracks how each tuple in the result set can be traced back to the original data and operations that generated it.

- Provenance is computed for each query operation, and the output uses a trace that shows how each result was derived.
- The **smallest counterexample** problem is solved using the Z3 SAT solver, which is used to find the smallest set of operations that lead to a discrepancy between two queries (the "test" and "correct" queries).

### SAT Solver (Z3)

- A **Z3 solver** is used to find the smallest counterexample when evaluating **SPJUD** queries.
- Z3 is utilized to check for discrepancies between the results of the "test" and "correct" queries on a given dataset, and the solver identifies the minimal counterexample set of operations.

### GUI Interface

A **Graphical User Interface (GUI)** has been developed with the following features:

1. **Pre-defined Examples**: Users can choose from 10 examples of random datasets and queries, which have been pre-implemented for testing.
2. **Custom Query Input**: Users can copy-paste a JSON file containing a database, correct query, and test query to test their own inputs.
3. **JSON File Upload**: Users can upload a JSON file, similar to the above, to test the provenance computation and counterexample finding.

The GUI allows users to visualize and test the results of the provenance computation and the smallest counterexample for their chosen query and dataset.

### Alignment with "Explaining Wrong Queries Using Small Examples" Paper

The implementation of this project follows the **RATest** approach, as outlined in the paper **"Explaining wrong queries using small examples"**. In this paper, the authors propose a technique for generating small counterexamples to explain discrepancies between queries. Our project leverages this methodology to identify and compute minimal counterexamples, ensuring that users can easily understand the causes of query discrepancies.

## 2. Existing Code Used

- **Z3 SAT Solver**: The Z3 solver library is used for solving the smallest counterexample problem. You can find it [here](https://github.com/Z3Prover/z3).
- **Provenance Computation**: Custom algorithms for computing provenance, focusing on SPJUD queries.
- **GUI**: The graphical interface is developed using Tkinter.

## 3. Datasets

The project uses **toy datasets** that have been created specifically for the purpose of demonstrating the functionality of the SPJUD queries and provenance computation.

### Example of Toy Database

- **Student Table**: Includes data about students (e.g., name, major).
- **Registration Table**: Includes data about course registrations (e.g., student name, course, department, grade).

The datasets are randomly generated and consist of a set of **Students** and their **Registration** data, ensuring a wide variety of test cases for the queries.

### Query Examples

- **Test Query**: A query that retrieves students enrolled in a specific department (e.g., "CS").
- **Correct Query**: A query that removes students with multiple distinct course enrollments.

## 4. Results

The framework displays the smallest counterexample found to the user. If the queries are identical and no counterexample is found, then the output is blank.

- For each input query pair, the system uses the Z3 solver to find the smallest counterexample, which highlights the minimal differences between the results of the "test" and "correct" queries.
- Provenance computation for each query demonstrates how the results were derived and allows the user to track the lineage of each tuple in the results.

---

````bibtex
@article{DBLP:journals/corr/abs-1904-04467,
  author       = {Zhengjie Miao and
                  Sudeepa Roy and
                  Jun Yang},
  title        = {Explaining Wrong Queries Using Small Examples},
  journal      = {CoRR},
  volume       = {abs/1904.04467},
  year         = {2019},
  url          = {http://arxiv.org/abs/1904.04467},
  eprinttype   = {arXiv},
  eprint       = {1904.04467},
  biburl       = {https://dblp.org/rec/journals/corr/abs-1904-04467.bib},
  bibsource    = {dblp computer science bibliography, https://dblp.org}
}

