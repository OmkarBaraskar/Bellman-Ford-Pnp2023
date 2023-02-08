# Bellman-Ford-Pnp2023

This is a repository for implementing the Bellman-Ford algorithm (and maybe other graph algorithms) in Lean4. This is done as a part of a course project for [Proofs and Programs 2023](http://math.iisc.ac.in/~gadgil/proofs-and-programs-2023/).

## Goal

The goal for this project is to implement the Bellman-Ford algorithm. Adding implementations for other graph-based algorithms (like improvements to Bellman-Ford, such as the Shorter Path Faster algorithm) and finding and proving useful properties about them are the following steps.

## Approach

We look through the Graph library (link in References below) to understand how graphs have been defined there. Then, we use the definitions and functions to implement a function which takes a weighted directed graph with vertices labelled [1, 2, 3...., n] and a root vertex as input, and outputs two lists of length n; the Distance list, whose ith entry is the length of the shortest path between the root vertex and vertex i, and the Predecessor list, whose ith entry is the vertex preceding the ith vertex along the shortest path between the root vertex and vertex i. Thus, by observing these two lists, one can determine the shortest distance and the shortest path between the root vertex and any other vertex on the given weighted directed graph.

## References

The Bellman-Ford algorithm was concieved by Richard Bellman and Lester Ford in [1958](https://www.ams.org/journals/qam/1958-16-01/S0033-569X-1958-0102435-2/) and [1956](https://www.rand.org/pubs/papers/P923.html) respectively.

We are using a graph library for Lean4, available [here](https://github.com/goens/graph-library-for-lean4), as a part of our existing code.
