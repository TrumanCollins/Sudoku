# Sudoku
Sudoku solver written in Haskell. Very fast.

I wrote this initially in 2015 while learning Haskell. I emphasized speed of execution
and heuristics/techniques that would quickly solve hard puzzles.

There is a set of nearly 50,000 puzzles with only 17 initial digits (the minimum for a
puzzle having only one solution), and this program will solve all of them in just over
4 minutes, so nearly 200 per second.

The code is well commented, but is farily long to support the various different
techniques for narrowing the solution space.

sudoku -h generates a help screen.
It will generae all possible solutions to the puzzle.
Puzzles are specified with the initial state all on one line, so for:

Initial board state:
3 0 0   0 8 0   0 0 0 
0 0 0   7 0 0   0 0 5 
1 0 0   0 0 0   0 0 0 

0 0 0   0 0 0   3 6 0 
0 0 2   0 0 4   0 0 0 
0 7 0   0 0 0   0 0 0 

0 0 0   0 6 0   1 3 0 
0 4 5   2 0 0   0 0 0 
0 0 0   0 0 0   8 0 0

run:

sudoku 300080000300080000000700005100000000000000360002004000070000000000060130045200000000000800
