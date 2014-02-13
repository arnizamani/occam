Example 1: Math. Solved
-- (2+3,3+2,1)

Example 2: Clause. Solved
-- (black(A),raven(A),1)

Example 3: Math. Solved
-- ((2+4)*(6+1),42,1)

Example 4: Logic. Solved
-- ((p <= q) || p,True,1)

Example 5: Solved
-- (rev ['h','i'],['i','h'],1)

Example 6: Stream. Done
-- ([Bob,Plays],[],1)

Example 7: size

Example 8: same as example 3.

--Example 9: Math. Solved
-- ((2+4)*(6+1),x,1)

Example 9: Math. Solved
--(3*0,0,1)
--(5*0,0,1)

Example 10: Math. Solved
--(5*0,0,1)
--(5*1,1,-1)
--(5*1,0,-1)

--(5+0,5,1)
--(5+1,5,-1)

Example 11: Math. Solved
--(2+3,3+2,1)
--(5+4,4+5,1)

Example 12: not done
--(black(A),True,1)
--(black(B),True,1)
--(black(C),True,1)
--(raven(D),True,-1)

Example 13: done
--(Wind || Rain,Wind,1)
--(Thunder || Lighting,Thunder,1)
--(Wind,Rain,-1)

Example 14
--(Rain && Lightning,Thunder,1)
--(Wind && Lightning,Thunder,1)
--(Thunder,Lighting,-1)

Example 15
--([Alice,Crawls],[],1)
--([Alice],[],-1)

Example 18. Computations done. Delta not yet.
(2 `g` 1,2,1)
(2 `g` 2,4,1)
(2 `g` 3,2,-1)
-- (2 `g` 2,2,-1)
--(0 `g` 0,4,-1)
--(0 `g` 0,6,-1)

Example 19. Solved
--(f 0,8,1)
--(f 1,11,1)
--(f 2,14,1)
--(f 0,0,-1)
--(f 1,8,-1)

--Example 20
--(rev ['h','i'],['i','h'],1)
--   (rev ['h','e','l','l','o'],['o','l','l','e','h'],1)
--(rev ['o','h'],['o','h'],-1)

-- Example 21
--(pal [1,2,1],True,1)

Example 23
--(f(2),16,1)
-- (f(3),24,1)
--(f(6),x,1)
--(f(2),2,-1)

Example 24
--(f2(Hand),Palm,1)
--(f2(Foot),x,1)
--(f2(Palm),Palm,-1)
