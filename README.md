# ringsat
DPLL SAT-solver for GPUs

This is an old GPU solver for Boolean SAT I wrote in 2013-2015. 
It features DPLL algorithm with non-chronological backjumping, work stealing between threads etc.
Each GPU thread runs complete DPLL algorithm, no work is done by CPU.
Data structures and BCP procedures are highly optimized for GPU architecture. 
Code features Loop Fusion Transformation applied by hand to main BCP loops, and Next Jump Voting 
system for further optimisation of SIMD performance.
