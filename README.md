# Sudoku
Sudoku solver written in Haskell. Very fast execution speed.

I wrote this initially in 2015 while learning Haskell. I emphasized speed of execution
and heuristics/techniques that would quickly solve hard puzzles.

There is a set of nearly 50,000 puzzles with only 17 initial digits (the minimum for a
puzzle having only one solution), and this program will solve all of them in just over
4 minutes, so nearly 200 per second.

The code is well commented, but is farily long to support the various different
techniques for narrowing the solution space. All the code is in one file, which is
just the way it is.

I have included a file of tests, including one or two with multiple solutions.

sudoku -h generates a help screen.
It will generae all possible solutions to the puzzle.
Puzzles are specified with the initial state all on one line, so for:

Initial board state:  
3 0 0 &nbsp; &nbsp; 0 8 0 &nbsp; &nbsp; 0 0 0  
0 0 0 &nbsp; &nbsp; 7 0 0 &nbsp; &nbsp; 0 0 5  
1 0 0 &nbsp; &nbsp; 0 0 0 &nbsp; &nbsp; 0 0 0  

0 0 0 &nbsp; &nbsp; 0 0 0 &nbsp; &nbsp; 3 6 0  
0 0 2 &nbsp; &nbsp; 0 0 4 &nbsp; &nbsp; 0 0 0  
0 7 0 &nbsp; &nbsp; 0 0 0 &nbsp; &nbsp; 0 0 0  

0 0 0 &nbsp; &nbsp; 0 6 0 &nbsp; &nbsp; 1 3 0  
0 4 5 &nbsp; &nbsp; 2 0 0 &nbsp; &nbsp; 0 0 0  
0 0 0 &nbsp; &nbsp; 0 0 0 &nbsp; &nbsp; 8 0 0  

run:

sudoku 300080000000700005100000000000000360002004000070000000000060130045200000000000800

This software will also accept a puzzle and see if by removing any of the single clues
whether the resulting puzzle has a unique solution. So:

sudoku -r 300080000000700005100000000000000360002004000070000000000060130045200000000000852

results in:

Puzzles having one solution and one more empty cell:
300080000000700005100000000000000360002004000070000000000060130045200000000000802 (18)
300080000000700005100000000000000360002004000070000000000060130045200000000000850 (18)

Puzzles found with one solution and one fewer filled element: 2
Total time: 0.1918 sec.

