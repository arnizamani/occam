{-
    Author: Abdul Rahim Nizamani, ITIT, Gothenburg University
    Created: 2013-09-29
    Note: This is an agent file that defines the agent "NewAgent"
          Syntax:
              Agent name: the same as module name
              Agent working memory: defined by parameter width
              Agent attention span: defined by parameter depth
              Training problems for the agent: parameter filename
          This file is automatically updated by the program.
          Manual changes may be overwritten.
    These starting comments will not be overwritten. Any other comments
      in the file will automatically be removed.
tail (x : l) ->> l
tail2 (x : y : l) ->> l
init [1] ->> []
init x : [] ->> []
init (x : l) ->> [x] P.++ init l
nub [] ->> []
nub (x : l) ->> [x] `P.union` l
2 + 4 ->> 6
6 + 1 ->> 7
6 * 7 ->> 42
x <= y ->> not x || y
x || (y || z) ->> (x || y) || z
(x || y) || z ->> x || (y || z)
x || not x ->> True
not x || x ->> True
True || x ->> x
x || True ->> x
[] ++ [x] ->> [x]
[x] ++ [] ->> [x]
[x] ++ [y] ->> [x, y]
raven A ->> True
raven B ->> True
raven C ->> True
black D ->> True
x `mul` 0 ->> 0
x `mul` (y + 1) ->> (x `mul` y) + y
15 + 2 ->> 17
17 + 2 ->> 19
19 + 2 ->> 21
1 - 1 ->> 0
2 - 1 ->> 1
3 - 1 ->> 2
4 - 1 ->> 3
pal x ->> x == rev x
x == x ->> True
seq 0 ->> 15
seq x + 1 ->> seq x + 2
x || y -> x
x || y ->> y || x
Lightning ->> Thunder
2 * 8 ->> 16
3 * 8 ->> 24
6 * 8 ->> 48
2 + 2 ->> 4
2 + 3 ->> 5
f x ->> x * 8
under Hand ->> Palm
under Foot ->> Sole
rev [] ->> []
rev (x : xs) ->> rev xs ++ [x]
f2 Hand ->> Palm
x + y ->> y + x
black x -> raven x
[Alice,Crawls] ->> []
Plays ->> Crawls
Bob ->> Alice
x `g` 0 ->> 0
x `g` 1 ->> x
x `g` (y+1) ->> (x `g` y) + x
f 0 ->> 8
f (x + 1) ->> (f x) + 3
8 + 3 ->> 11
11 + 3 ->> 14
g(2,1)
(g(2,0) + 2) + 2
(0 + 2) + 2
2 + 2
4
g(2,3)
(g(2,2) + 2)
(g(2,1) + 2) + 2
((g(2,0) + 2) + 2) + 2
((0 + 2) + 2) + 2
(2 + 2) + 2
4 + 2
6
-}
Width ->> 8
Depth ->> 5
Solution ->> 6
Language ->> "Math"
Filename ->> "PaperExamples.hs"
0 + x ->> x
2 + 2 ->> 4
4 + 2 ->> 6
x `g` 0 ->> 0
x `g` (y + 1) ->> (x `g` y) + x

