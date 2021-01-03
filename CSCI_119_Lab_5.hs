-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2
-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)

-- Check whether a finite state machine (qs, s, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function gives a state in qs for every state in qs and
--     letter from sigma

uniqueQs :: [Int]-> Bool
uniqueQs [] = True
uniqueQs (q:qs) = if elem q qs then False else uniqueQs qs 
{-*Main> uniqueQs [15,5,15,4]
False
*Main> uniqueQs [1,1,23]
False
*Main> uniqueQs [1,2,3,4]
True
*Main> uniqueQs [7,6,9,13]
True
*Main> uniqueQs [7,6,9,13]
True
-}
startState :: Int -> [Int] -> Bool
startState s qs = elem s qs
{-
*Main> startState 5 [1,5,7,15]
True
*Main> startState 1 [1,4,7,10]
True
*Main> startState 5 [1,6,9,10]
False
*Main> startState 2 [5,4,7,6]
False
-}
finalState:: [Int] -> [Int] -> Bool
finalState fs qs = and[f `elem` qs | f <- fs ]
{-
*Main> finalState [1,2,3] [1,2,4,5,6]
False
*Main> finalState [4,5,6] [7,8,9,10]
False
*Main> finalState [1,2,3] [1,2,3,4,5,6]
True
*Main> finalState [5,5,5] [5,5,5,8,10]
True
*Main> finalState [4,3,9] [4,3,9,10,14]
True
-}

tsCheck :: (Int -> Char -> Int) -> [Int] -> Bool
tsCheck ts qs = and [ts q s `elem` qs | q <- qs, s <- sigma]  

{-
-}
checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, ts) = (uniqueQs qs) && (startState s qs) && (finalState fs qs) && (tsCheck ts qs)
{-
*Main> checkFSM oddbs
True
*Main> checkFSM avoid_aab
True
*Main> checkFSM end_ab
True
*Main> checkFSM (exactly "")
True
-}

-- Gives the delta* function (recursive in w)
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m@(qs, s, fs, ts) q [] = q 
delta_star m@(qs, s, fs, ts) q (w:ws) = delta_star m (ts q w) ws

{-
*Main> delta_star oddbs 5 ['a', 'b', 'c']
1 
*Main> delta_star avoid_aab 6 ['g', 'h', 'i', 'j']
6
*Main> delta_star end_ab 4 ['z', 'y', 't', 'e']
4
*Main> delta_star (exactly "") 7 ['l', 'r', 'w', 'q']
0
-}
-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m@(qs,s,fs,ts) w = elem (delta_star m s w) fs
{-
*Main> accept1 oddbs ['a', 'b', 'c', 'd', 'e', 'f']
True
*Main> accept1 end_ab ['f', 'g', 'h', 'i']
False
*Main> accept1 avoid_aab ['o', 'p', 'g', 'i', 'j', 'e']
True
*Main> accept1 (exactly "") ['p', 'q']
True
*Main> accept1 (exactly "") []
True
-}

-- Machine acceptance, Definition 2 (via L_q(M))

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux m@(qs, s, fs, ts) q [] = q `elem` fs
accept2_aux m@(qs, s, fs, ts) q (w:ws) = accept2_aux m (ts q w) ws
{-
*Main> accept2_aux oddbs 5 ['e', 'f', 'g', 'h', 'i']
False
*Main> accept2_aux avoid_aab 2 ['x', 'y']
True
*Main> accept2_aux end_ab 7 ['o', 'p', 'q', 'r']
False
*Main> accept2_aux (exactly "") 10 ['g', 'h']
True
-}
--accept2_aux m ts q (w:ws) = accept2_aux m (ts m q w) ws
-- Acceptance, defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m@(_, s, _, _) w = accept2_aux m s w
{-
*Main> accept2 oddbs ['a', 'b', 'c', 'd', 'e']
True
*Main> accept2 avoid_aab  ['a', 'b', 'c', 'd', 'e']
True
*Main> accept2 end_ab  ['a', 'b', 'c', 'd', 'e']
True
*Main> accept2 (exactly "")  ['a', 'b', 'c', 'd', 'e']
True
-}

---- FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- and test it adequately
oddbs :: FSM
oddbs = ([0,1],0,[1],f) where
    f 1 _ = 1
    f q c = if c == 'b' then 1 else 0
--([0,1],0,[1],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',1)])
{-
*Main> accept1 oddbs "bb"
True
*Main> accept1 oddbs "aa"
False
*Main> accept2 oddbs "bb"
True
*Main> accept2 oddbs "aa"
False
-}
-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = ([0,1,2,3],0,[0,1,2], f) where 
    f 3 _ = 3
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 2
    f 1 'b' = 0
    f 2 'a' = 2
    f 2 'b' = 3
    f q c = 0
--([0,1,2,3],0,[0,1,2],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),(2,'a',2),(2,'b',3),(3,'a',3),(3,'b',3)])
{-
*Main> accept1 avoid_aab "aab"
False
*Main> accept1 avoid_aab "bbb"
True
*Main> accept2 avoid_aab "babaaaaaaab"
True
*Main> accept2 avoid_aab "bbbb"
True
-}
-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = ([0,1,2],0,[2], f) where 
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 1
    f 1 'b' = 2
    f 2 'a' = 1
    f 2 'b' = 0
    f q c = 0
--([0,1,2],0,[2],[(0,'a',1),(0,'b',0),(1,'a',1),(1,'b',2),(2,'a',1),(2,'b',0)])
{-
*Main> accept1 end_ab "abababababab"
True
*Main> accept2 end_ab "ababbb"
True
*Main> accept1 end_ab "bbb"
False
*Main> accept2 end_ab "aaa"
False
*Main> accept1 end_ab "bbb"
False
-}

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else
exactly :: String -> FSM
exactly s = (qs, st, fs, ts) where
     n = (length s)
     qs = [0..n+1]
     st = 0
     fs = [n]
     ts q a = if  (q /= n+1) && (s!!q == a) then q+1  
              else n+1
              
     
     
--([0,1,2,3],0,[0],[(0,'a',1),(0,'b',2),(1,'a',0),(1,'b',3),(2,'a',3),(2,'b',0),(3,'a',3),(3,'b',3)])
{-
*Main> accept1 (exactly "abab") "abab"
True
*Main> accept2 (exactly "bab") "bab"
True
*Main> accept2 (exactly "bab") "a"
False
*Main> accept2 (exactly "bbb") "aa"
False
-}