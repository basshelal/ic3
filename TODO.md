# TODO

## For Markus

* Make/get a medium sized toy example, use Harry's thesis example
* Get the invariant to be printed on completion
* Get the invariant printed on each iteration

## Reading

* Read more about AIGER format's extensions (after core MILOA)

## Improve `Model`

* Better variable and function names
* Deep logging (nearly trace level logging)
* Log all solver actions to understand what exactly we are giving to the solver and what is it 
  solving
* Log/inform total number of steps in circuit in addition to deep info about circuit
* Give all aiger file variables names and locations, make better aiger symbol types to hold this 
  (and more) information, such that a debug trace run is much clearer to follow

## Quality of Life

* Write our own translator into `dot` format for easy visualizations, we should make the graphs 
  as compact and readable as possible, it would be ideal to even have the drawing functionality 
  built into our own application somehow (output to svg or something like that)

## General Improvements

* Switch to CMake
* Switch to C++ 20
* Install Z3 C++ API
* Swap calls to minisat into calls to Z3
