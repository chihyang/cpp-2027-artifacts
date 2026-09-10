Formalizing `einsum` with Named Tensor Notation
====

This is the supplementary materials for the CPP 2027 submission "Formalizing `einsum` with Named Tensor Notation."

The directory contains both [Agda](./Agda) and [Lean](./Lean) implementation of the named tensor language described in the paper, which are located in `./Agda` and `./Lean` directories under this directory respectively.
Under each folder, there is a file named as `Einsum`, which imports all implementations.
The implementations are split into the following files:

| File Name          | Location in Paper | Description                             |
|--------------------|-------------------|-----------------------------------------|
| `NamedShape`       | Section 5.1       | Named shape                             |
| `ShapeOperations`  | Section 5.1       | Union, intersection, difference of `Is` |
| `ShapeProperties`  | Section 5.1       | Compatible, subset, equivalence of `Is` |
| `NamedIndex`       | Section 5.2       | Named indices                           |
| `UnnamedIndex`     | Section 5.2       | Unnamed indices                         |
| `TensorExpr`       | Section 3.2       | Named tensor language                   |
| `TensorDenotation` | Section 4.2       | Denotational semantics                  |
| `ExpandProperties` | Section 6.1       | Fusion of `expand`                      |
| `EinsumProperties` | Section 6.2 & 6.3 | Commutativity of `einsum` and `expand`  |
| `TensorExamples`   | Section 2         | Some examples                           |

# Important Definitions

We list the location of important definitions and theorems below.
We give the description, the location in the paper, and the start line number in file in the form `filename:lineno`.

## Lean

* Syntax: [./Lean/Einsum/TensorExpr.lean](./Lean/Einsum/TensorExpr.lean#L50):50, `TExpr`.
* Denotational semantics: [./Lean/Einsum/TensorDenotation.lean](./Lean/Einsum/TensorDenotation.lea#:73):73, `denote`.
* union (`∪`): [./Lean/Einsum/ShapeOperations.lean](./Lean/Einsum/ShapeOperations.lean#L72):72, `unionIs`.
* intersection (`∩`): [./Lean/Einsum/ShapeOperations.lean](./Lean/Einsum/ShapeOperations.lean#L524):524, `intersectIs`.
* difference (`\`): [./Lean/Einsum/ShapeOperations.lean](./Lean/Einsum/ShapeOperations.lean#L775):775, `minusIs`.
* lookup-∪: [./Lean/Einsum/ShapeOperations.lean](./Lean/Einsum/ShapeOperations.lean#L285):285, `lookup_unionIs_eq`.
* lookup-∩: [./Lean/Einsum/ShapeOperations.lean](./Lean/Einsum/ShapeOperations.lean#L611):611, `lookup_intersectIs_eq`.
* difference-\: [./Lean/Einsum/ShapeOperations.lean](./Lean/Einsum/ShapeOperations.lean#L841):841, `lookup_minusIs_eq`.
* expand-fuse: [./Lean/Einsum/ExpandProperties.lean](./Lean/Einsum/ExpandProperties.lean#L26):26, `expand_fuse_minusIs_eq`.
* einsum-expand: [./Lean/Einsum/EinsumProperties.lean](./Lean/Einsum/EinsumProperties.lean#L478):478, `einsum_expand_comm_two`.
* summation-free einsum-expand: [./Lean/Einsum/EinsumProperties.lean](./Lean/Einsum/EinsumProperties.lean#L663):663, `einsum_expand_sum_free_comm_two`.

## Agda

* Syntax: [./Agda/Einsum/TensorExpr.agda](./Agda/Einsum/TensorExpr.agda#L65):65, `𝕋`.
* Denotational semantics: [./Agda/Einsum/TensorDenotation.agda](./Agda/Einsum/TensorDenotation.agda#L106):106, `⟦_⟧⦅_⨾_⦆`.
* union (`∪`): [./Agda/Einsum/ShapeOperations.agda](./Agda/Einsum/ShapeOperations.agda#L147):147, `∪`.
* intersection (`∩`): [./Agda/Einsum/ShapeOperations.agda](./Agda/Einsum/ShapeOperations.agda#L200):200, `∩`.
* difference (`∖`): [./Agda/Einsum/ShapeOperations.agda](./Agda/Einsum/ShapeOperations.agda#L397):397, `∖`.
* lookup-∪: [./Agda/Einsum/ShapeOperations.agda](./Agda/Einsum/ShapeOperations.agda#L305):305, `lookup-∪`.
* lookup-∩: [./Agda/Einsum/ShapeOperations.agda](./Agda/Einsum/ShapeOperations.agda#L611):611, `lookup-∩`.
* difference-\: [./Agda/Einsum/ShapeOperations.agda](./Agda/Einsum/ShapeOperations.agda#L841):841, `lookup-∖`.
* expand-fuse: [./Agda/Einsum/ExpandProperties.agda](./Agda/Einsum/ExpandProperties.agda#L75):75, `expand-fuse`.
* einsum-expand: [./Agda/Einsum/EinsumProperties.agda](./Agda/Einsum/EinsumProperties.agda#L478):478, `einsum-expand-comm`.
* summation-free einsum-expand: [./Agda/Einsum/EinsumProperties.agda](./Agda/Einsum/EinsumProperties.agda#L273):273, `einsum-expand-summation-free-comm`.


# Environments

To verify the implementation, we require the following environments:

## Lean

* Lean version: lean4 v4.27.0
* Mathlib standard library version: v4.27.0

## Agda

* Agda version: 2.7.0.1
* Agda standard library version: agda-stdlib-2.1.1

# Command

Suppose all libraries and tools are installed correctly, you can verify the files in the following way:

## Lean

``` shell
cd ./Lean
lake build
```

## Agda

```shell
cd ./Agda
agda Einsum.agda
```
