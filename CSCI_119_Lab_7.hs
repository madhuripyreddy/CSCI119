-- Lab 7: Convert FSMs to regular expressions

import Data.List
import Control.Monad (replicateM)  -- for strings function below


---------------- Given functions ----------------

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
             deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary RegExps into extended REs
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
fromRE' :: RegExp' -> RegExp
fromRE' Zero = Empty
fromRE' One = Star Empty
fromRE' (Let' c) = Let c
fromRE' (Union' []) = Empty
fromRE' (Union' [r]) = fromRE' r
fromRE' (Union' (r:rs)) = Union (fromRE' r) (fromRE' (Union' rs))
fromRE' (Cat' []) = Star Empty
fromRE' (Cat' [r]) = fromRE' r
fromRE' (Cat' (r:rs)) = Cat (fromRE' r) (fromRE' (Cat' rs))
fromRE' (Star' r) = Star (fromRE' r)

-- Basic postfix parser for RegExp', assuming binary + and ., for testing
toRE' :: String -> RegExp'
toRE' w = go w [] where
  go [] [r] = r
  go ('0':xs) rs = go xs (Zero:rs)
  go ('1':xs) rs = go xs (One:rs)
  go ('+':xs) (r2:r1:rs) = go xs (Union' [r1,r2]:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat' [r1,r2]:rs)
  go ('*':xs) (r:rs) = go xs (Star' r:rs)
  go (x:xs) rs = go xs (Let' x:rs)


-- Finite state machines (as records), indexed by the type of their states
type FSM a = ([a], a, [a], a -> Char -> a)



---------------- Lab 7 begins here ----------------


-- Check for proper (cannot recognize epsilon)
proper :: RegExp' -> Bool
proper Zero = True
proper One = False 
proper (Let' c) = True
proper (Union' rs) = and [proper a | a <- rs]
proper (Cat' rs) = or [proper a | a <- rs]
proper (Star' r) = False

-- Solve a system of proper linear equations
-- You can assume that the system is correctly formed and proper
solve :: [[RegExp']] -> [RegExp'] -> [RegExp']

solve [] [] = []
solve ((l11:l1J) : rows) (l1':lI') = simp x1 : xI where
  -- l11 is the corner element, and l1J = [l12,...,l1n] is the rest of 1st row
  -- rows are the rest of the rows [[l21,...,l2n], ..., [ln1,...,lnn]]
  -- l1' is the first constant
  -- lI' are the rest of the contants [l2',...,ln']
  
  -- first column [l21, ..., ln1]
  lI1 = map head rows

  -- sub-matrix [[l22,...,l2n], ..., [ln2,...,lnn]]
  lIJ = map tail rows

  -- [[l22_bar,...,l2n_bar], ..., [ln2_bar,...,lnn_bar]] computed via (6)
  lIJ_bar = zipWith sixes lI1 lIJ            -- loops for i = 2 .. n
  sixes li1 liJ = zipWith (six li1) l1J liJ  -- loops for j = 2 .. n
  six li1 l1j lij = Union' [Cat' [li1, (Star' l11), l1j], lij]

  -- [l2'_bar,..., ln'_bar] computed via (7)
  lI'_bar = zipWith seven lI1 lI'
  seven li1 li' = Union' [Cat' [li1, Star' l11, l1'], li']
    
  -- recursively solve the system of size n-1
  xI = solve lIJ_bar lI'_bar

  -- compute x1 from xI via (5)
  x1 = Cat' [Star' l11, Union' (zipWith (\lij xi -> Cat' [lij, xi]) l1J xI ++ [l1'])]


-- Generate a regular SPLE from an FSM via formulas in Theorem 6.5
toSPLE :: FSM Int -> ([[RegExp']], [RegExp'])
toSPLE (qs,s,fs,d) = (lIJ, lI') where
  
  -- Construct matrix of coefficients (coef i j = Lij)
  lIJ = [[simp (coef i j) | j <- qs] | i <- qs]
  coef i j = Union' [Cat' [Let' a, Star' Zero] | a <- sigma, (d i a == j)]

  -- Construct constants
  lI' = [if q `elem` fs then One else Zero| q <- qs]


-- Convert an FSM to a RegExp'
conv :: FSM Int -> RegExp'
conv m@(_,s,_,_) = simp $ solution !! s where
  (matrix, consts) = toSPLE m
  solution = solve matrix consts


-- Test! Test! Test! (and show your tests here)
{-
*Main> (proper (Zero))
True
*Main> (proper(One))
False
*Main> (proper(toRE' "a"))
True
*Main> (proper(toRE' "00+"))
True
*Main> (proper(toRE' "0b+"))
True
*Main> (proper(toRE' "a0+"))
True
*Main> (proper(toRE' "ab+"))
True
*Main> (proper(toRE' "0*0*+"))
False
*Main> (proper(toRE' "00."))
True
*Main> (proper(toRE' "0b."))
True
*Main> (proper(toRE' "a0."))
True
*Main> (proper(toRE' "ab."))
True
*Main> (proper(toRE' "0*0*."))
False
*Main> (proper(toRE' "a*"))
False
*Main> (proper(toRE' "0*"))
False
*Main> (proper(toRE' "0*0*0*0*0*0*....."))
False
*Main> (proper(toRE' "0*0*0*0*0*a....."))
True
*Main> (proper(toRE' "0*0*a*0*0*0....."))
True
*Main> (proper(toRE' "a*0*0*0*0*0....."))
True
*Main> (proper(toRE' "0*0*."))
False
*Main> (proper(toRE' "0*0*0*0*0*0*+++++"))
False
*Main> (proper(toRE' "0*0*0*0*0*a+++++"))
False
*Main> (proper(toRE' "0*0*a*0*0*0+++++"))
False
*Main> (proper(toRE' "a*0*0*0*0*0+++++"))
False
*Main> (proper(toRE' "0*0*+"))
False
-}

{-
*Main> fromRE' (solve [[toRE' "b", toRE' "a"], [toRE' "0", toRE' "ab+"]] [toRE' "1", toRE' "0"] !! 0)
Star (Let 'b')
*Main> fromRE' (solve [[Let' 'b', Let' 'a'], [Zero, Union' [Let' 'a', Let' 'b']]] [One, Zero] !! 0)
Star (Let 'b')
*Main> solve [[Let' 'a',Let' 'b'],[Let' 'b',Let' 'a']][Zero,One] !! 0
Cat' [Star' (Let' 'a'),Let' 'b',Star' (Union' [Let' 'a',Cat' [Let' 'b',Star' (Let' 'a'),Let' 'b']])]
*Main> solve [[Let' 'a',Let' 'b'],[Let' 'b',Let' 'a']][Zero,One] !! 1
Star' (Union' [Let' 'a',Cat' [Let' 'b',Star' (Let' 'a'),Let' 'b']])
*Main> fromRE' (solve [[toRE' "a*b.", toRE' "b"], [toRE' "a", toRE' "ab*+"]] [toRE' "a", toRE' "b"] !! 1)
Union (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) 
(Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'a')))) (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') 
(Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) (Let 'b'))
*Main> fromRE' (solve [[Cat' [Star' (Let' 'a'), Let' 'b'], Let' 'b'], [Let' 'a', Union' [Let' 'a', Star' (Let' 'b')]]] [Let' 'a', Let' 'b'] !! 0)
Union (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'a')) (Union (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) 
(Cat (Let 'b') (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) 
(Star (Let 'b'))))) (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) 
(Let 'b'))) (Let 'a')))))) (Cat (Star (Cat (Star (Let 'a')) 
(Let 'b'))) (Cat (Let 'b') (Cat (Star (Union (Let 'a') 
(Union (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) (Let 'b')))))
*Main> fromRE' (solve [[toRE' "a*b.", toRE' "b"], [toRE' "a", toRE' "ab*+"]] [toRE' "a", toRE' "b"] !! 0)
Union (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'a')) (Union (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) 
(Cat (Let 'b') (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) 
(Star (Let 'b'))))) (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'a')))))) (Cat (Star (Cat (Star (Let 'a')) 
(Let 'b'))) (Cat (Let 'b') (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) 
(Star (Let 'b'))))) (Let 'b')))))
*Main> fromRE' (solve [[Cat' [Star' (Let' 'a'), Let' 'b'], Let' 'b'], [Let' 'a', Union' [Let' 'a', Star' (Let' 'b')]]] [Let' 'a', Let' 'b'] !! 1)
Union (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') (Cat (Star (Cat 
(Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) 
(Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'a')))) 
(Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') 
(Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) (Let 'b'))
*Main> fromRE' (solve [[toRE' "a*b.", toRE' "b"], [toRE' "a", toRE' "ab*+"]] [toRE' "a", toRE' "b"] !! 1)
Union (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) 
(Cat (Let 'a') (Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'a')))) (Cat (Star (Union (Let 'a') (Union (Cat (Let 'a') 
(Cat (Star (Cat (Star (Let 'a')) (Let 'b'))) (Let 'b'))) (Star (Let 'b'))))) (Let 'b'))
*Main> fromRE' (solve [[toRE' "a", toRE' "b*a."], [toRE' "b", toRE' "bb*+"]] [toRE' "b", toRE' "a"] !! 1)
Union (Cat (Star (Union (Let 'b') (Union (Cat (Let 'b') (Cat (Star (Let 'a')) (Cat (Star (Let 'b')) (Let 'a')))) (Star (Let 'b'))))) 
(Let 'a')) (Cat (Star (Union (Let 'b') (Union (Cat (Let 'b') (Cat (Star (Let 'a')) (Cat (Star (Let 'b')) (Let 'a')))) (Star (Let 'b'))))) 
(Cat (Let 'b') (Cat (Star (Let 'a')) (Let 'b'))))
-}
-- Define a machine that accepts exactly the strings with an odd number of b's
-- and test it adequately
oddbs :: FSM Int
oddbs = ([0,1], 0, [1], f) where
  f q a = if a == 'b' then (q+1) `mod` 2 else q
--([0,1],0,[1],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',1)])

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM Int
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

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM Int
end_ab = ([0,1,2],0,[2], f) where 
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 1
    f 1 'b' = 2
    f 2 'a' = 1
    f 2 'b' = 0
    f q c = 0
--([0,1,2],0,[2],[(0,'a',1),(0,'b',0),(1,'a',1),(1,'b',2),(2,'a',1),(2,'b',0)])

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else
exactly :: String -> FSM Int
exactly s = (qs, st, fs, ts) where
     n = (length s)
     qs = [0..n+1]
     st = 0
     fs = [n]
     ts q a = if  (q /= n+1) && (s!!q == a) then q+1  
              else n+1    
--([0,1,2,3],0,[0],[(0,'a',1),(0,'b',2),(1,'a',0),(1,'b',3),(2,'a',3),(2,'b',0),(3,'a',3),(3,'b',3

-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], d) where 
    d 0 _ = 0
    
-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM x = ([0,1,2], 0, [1], d) where 
    d q y = if q == 0 && y == 'a' then 1 else 2
    
{-
*Main> toSPLE oddbs
([[Let' 'a',Let' 'b'],[Let' 'b',Let' 'a']],[Zero,One])
*Main> toSPLE avoid_aab
([[Let' 'b',Let' 'a',Zero,Zero],[Let' 'b',Zero,Let' 'a',Zero],[Zero,Zero,Let' 'a',Let' 'b'],[Zero,Zero,Zero,Union' [Let' 'a',Let' 'b']]],
[One,One,One,Zero])
*Main> toSPLE end_ab
([[Let' 'b',Let' 'a',Zero],[Zero,Let' 'a',Let' 'b'],[Let' 'b',Let' 'a',Zero]],[Zero,Zero,One])
*Main> toSPLE (exactly "")
([[*** Exception: Prelude.!!: index too large
*Main> toSPLE emptyFSM
([[Union' [Let' 'a',Let' 'b']]],[Zero])
*Main> toSPLE (letterFSM 'a')
([[Zero,Let' 'a',Let' 'b'],[Zero,Zero,Union' [Let' 'a',Let' 'b']],[Zero,Zero,Union' [Let' 'a',Let' 'b']]],[Zero,One,Zero])
-}


---------------- Lab 7 ends here ----------------------------------


{----------------------------------------------------------------------------
| Bonus feature:  A regular-expression simplifier
|----------------------------------------------------------------------------

A "simplified" RegExp' satisfies the following conditions:
(1) Every Union' is applied to a normalized list of two or more arguments,
    each of which is a One, Let', Cat', or Star' (i.e., not Zero or Union')
(2) Every Cat' is applied to a list of two or more arguments, each of which is
    a Let' or Star' (i.e., not Zero, One, Union', or Cat')
(3) Every Star' is applied to a Let', Union', or Cat' (i.e., not Zero, One,
    or Star')

The following simplification rules, when applied repeatedly at every subterm
of a RegExp' until it no longer changes, result in a simplified RegExp':

   Union' []                          --> Zero
   Union' [r]                         --> r
   Union' (rs1 ++ [Zero] ++ rs2)      --> Union' (rs1 ++ rs2)
   Union' (rs1 ++ [Union' rs] ++ rs2) --> Union' (rs1 ++ rs ++ rs2)
   Union' rs                          --> Union' (norm rs)                  (*)

   Cat' []                            --> One
   Cat' [r]                           --> r
   Cat' (rs1 ++ [Zero] ++ rs2)        --> Zero
   Cat' (rs1 ++ [One] ++ rs2)         --> Cat' (rs1 ++ rs2)
   Cat' (rs1 ++ [Union' rs] ++ rs2)   --> Union' (map (\r -> Cat' (rs1 ++ [r] ++ rs2)) rs)
   Cat' (rs1 ++ [Cat' rs] ++ rs2)     --> Cat' (rs1 ++ rs ++ rs2)

   Star' Zero                         --> One
   Star' One                          --> One
   Star' (Star' r)                    --> Star' r

(*) Note: this rule should only be applied if rs is not already normalized;
    normalization is used to realize the commutativity and idempotency of union
    (i.e., that  L1 u L2 = L2 u L1  and  L u L = L ).

However, it would be very inefficient to attempt to apply these rules in the
manner indicated. Instead, our approach is to stage the application of these
rules carefully to minimize the number of traversals of the regular expression.
-------------------------------------------------------------------------------}

simp :: RegExp' -> RegExp'
simp Zero = Zero
simp One = One
simp (Let' c) = Let' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RegExp'] -> RegExp'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RegExp'] -> RegExp'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RegExp' -> RegExp'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RegExp'] -> [RegExp']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RegExp'] -> [RegExp']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RegExp'] -> [RegExp'] -> [RegExp']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs
