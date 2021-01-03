--Lab 10: FSM Initialization
import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below
-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Given functions ----------------

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

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys

-- delta* construction
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

--Intersect function
inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs =  fs1 >< fs2
  -- fs = [(q1,q2) | q1 <- qs1, q2 <- qs2, q1 `elem` fs1, q2 `elem` fs2]
  d (q1, q2) a = (d1 q1 a, d2 q2 a)
  
--complementFSM function
complementFSM :: Ord a => FSM a -> FSM a
complementFSM m@(qs, s, fs, d) = (qs', s', fs', d') where
  qs' = qs
  s'  = s
  fs' = [q | q <- qs, elem q fs]
  d' q a = d q a
    
-- Complement function
compl :: Eq a => FSM a -> FSM a
compl m@(qs1, s1, fs1, d1) = (qs, s, fs, d) where 
  qs = qs1
  s  = s1
  fs = [q | q <- qs1, q `notElem` fs1]
  -- fs = [q | q <- qs1, null q || overlap q fs1]
  d = d1
reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable
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

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)

-- Check whether a finite state machine (qs, s, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function gives a state in qs for every state in qs and
--     letter from sigma

-- nodups xs = "xs has no duplicates"
nodups :: Eq a => [a] -> Bool
nodups [] = True           
nodups (x:xs) = notElem x xs && nodups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys
-- OR: subset xs ys = all (`elem` ys) xs

-- func d qs == "d is a function from qs x sigma to qs"
func :: Eq a => (a -> Char -> a) -> [a] -> Bool
func d qs = and [elem (d q a) qs | q <- qs, a <- sigma]

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = nodups qs &&         -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func d qs            -- (4)

-- All functions below assume that the machine is correct
delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star (_, _, _, d) = foldl d

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (delta_star m s w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m@(_, _, _, d) q (a:w) = accept2_aux m (d q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, s, _, _) w = accept2_aux m s w

-- odd_bs is a machine that accepts strings with an odd number of b's
-- states: (number of b's read so far) mod 2
odd_bs :: FSM Int
odd_bs = ([0,1], 0, [1], f) where
  f q a = if a == 'b' then (q+1) `mod` 2 else q

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

end_ab :: FSM Int
end_ab = ([0,1,2],0,[2], f) where 
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 1
    f 1 'b' = 2
    f 2 'a' = 1
    f 2 'b' = 0
    f q c = 0
-- Nondeterministic FSMs, indexed by their type of state
-- All states are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions)  
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- nap_hat d qs a == normalized list of all transitions possible from qs on a
nap_hat :: Ord a => Trans a -> [a] -> Char -> [a]
nap_hat d qs a =  norm $ concat [d q a | q <- qs, a <- sigma]

-- nap_hat_star d qs w == normalized list of transitions possible from qs on w
nap_hat_star :: Ord a => Trans a -> [a] -> [Char] -> [a]
nap_hat_star d qs ws = star (nap_hat d) qs ws
--nap_hat_star = foldl' . nap_hat

-- nacc m w == m accept the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (qs, ss, fs, d) w = overlap (nap_hat_star d ss w) fs

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs1, s1, fs1, d1) = (qs, s, fs, d) where 
  qs = qs1
  s = [s1] 
  fs = fs1
  d q a = [d1 q a]
  
-- Conversion from NFSM to FSM by the "subset construction"  
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (qs1, ss1, fs1, d1) = (qs, s, fs, d) where
  qs = power(qs1)
  s  = ss1
  fs = [x | x <- qs, x `overlap` fs1] 
  d q a = nap_hat d1 q a
  
-- Boolean binary operation on FSMs. Examples:
-- binopFSM (||) m1 m2 computes union machine
-- binopFSM (&&) m1 m2 computes intersection machine
binopFSM :: (Eq a, Eq b) => (Bool -> Bool -> Bool) -> FSM a -> FSM b -> FSM (a,b)
binopFSM op m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(q1, q2) | q1 <- qs1, q2 <- qs2, op (elem q1 fs1) (elem q2 fs2)]
  d (qs1, qs2) a = (d1 qs1 a, d2 qs2 a)


-- Reverse FSM to a NFSM. Output machine accepts reverse of language of input machine.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM m@(qs1, ss1, fs1, d1) = (qs, s, fs, d) where 
    qs = qs1
    s = fs1
    fs = [ss1]
    d q a = [q' | q' <- qs1, q == (d1 q' a)]

-- Reachable states of a NFSM (similar to reachable but on NFSMs)
nreachable :: Ord a => NFSM a -> [a]
nreachable m@(qs, s, fs, d) = (uclosure s f) where 
  f q = norm $ concat (map (d q) sigma)

-- Minimize a FSM. Put all of the above together to compute the minimum machine for m
minimize :: Ord a => FSM a -> FSM a
minimize (qs, s, fs, d) = (qs', s', fs', d') where
   xor = (binopFSM (/=) (qs, s, fs, d) (qs, s, fs, d))
   rever = (reverseFSM xor)
   nreach = (nreachable rever)
   compl = [(q1, q2) | q1 <- qs, q2 <- qs, (notElem (q1, q2) nreach)]
   rep r = (minimum[q2| (q1, q2) <- compl, q1 == r])
   qs' = (norm [(rep q)| q <- qs])
   s' = (rep s)
   fs' = (intersect (norm [(rep q)| q <- qs]) fs)
   d' q a = (rep (d q a))
  
-- Test. For example, make sure that the minimal machine agrees with the original machine
-- on lots of input strings. Try for multiple machines.
{-
*Main> (qs, s, fs, d) = intify odd_bs
*Main> qs
[0,1]
*Main> s
0
*Main> fs
[1]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1],0,[1],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)])
*Main> (qs, s, fs, d) = intify avoid_aab
*Main> qs
[0,1,2,3]
*Main> s
0
*Main> fs
[0,1,2]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1,2,3],0,[0,1,2],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),(2,'a',2),(2,'b',3),(3,'a',3),(3,'b',3)])
*Main> (qs, s, fs, d) = intify end_ab
*Main> qs
[0,1,2]
*Main> s
0
*Main> fs
[2]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1,2],0,[2],[(0,'a',1),(0,'b',0),(1,'a',1),(1,'b',2),(2,'a',1),(2,'b',0)])
*Main> m@(qs, s, fs, d) = binopFSM (/=) odd_bs odd_bs
*Main> qs
[(0,0),(0,1),(1,0),(1,1)]
*Main> s
(0,0)
*Main> fs
[(0,1),(1,0)]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([(0,0),(0,1),(1,0),(1,1)],(0,0),[(0,1),(1,0)],
[((0,0),'a',(0,0)),((0,0),'b',(1,1)),((0,1),'a',(0,1)),((0,1),'b',(1,0)),
((1,0),'a',(1,0)),((1,0),'b',(0,1)),((1,1),'a',(1,1)),((1,1),'b',(0,0))])
*Main>  nreachable $ reverseFSM $ binopFSM (/=) odd_bs odd_bs
[(0,1),(1,0)]
*Main> m@(qs, s, fs, d) = binopFSM (/=) avoid_aab avoid_aab
*Main> fs
[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2)]
*Main> s
(0,0)
*Main> qs
[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3),(3,0),(3,1),(3,2),(3,3)],
(0,0),[(0,3),(1,3),(2,3),(3,0),(3,1),(3,2)],[((0,0),'a',(1,1)),((0,0),'b',(0,0)),((0,1),'a',(1,2)),
((0,1),'b',(0,0)),((0,2),'a',(1,2)),((0,2),'b',(0,3)),((0,3),'a',(1,3)),((0,3),'b',(0,3)),((1,0),'a',
(2,1)),((1,0),'b',(0,0)),((1,1),'a',(2,2)),((1,1),'b',(0,0)),((1,2),'a',(2,2)),((1,2),'b',(0,3)),((1,3),
'a',(2,3)),((1,3),'b',(0,3)),((2,0),'a',(2,1)),((2,0),'b',(3,0)),((2,1),'a',(2,2)),((2,1),'b',(3,0)),
((2,2),'a',(2,2)),((2,2),'b',(3,3)),((2,3),'a',(2,3)),((2,3),'b',(3,3)),((3,0),'a',(3,1)),((3,0),'b',
(3,0)),((3,1),'a',(3,2)),((3,1),'b',(3,0)),((3,2),'a',(3,2)),((3,2),'b',(3,3)),((3,3),'a',(3,3)),
((3,3),'b',(3,3))])
*Main> nreachable $ reverseFSM $ binopFSM (/=) avoid_aab avoid_aab
[(0,1),(0,2),(0,3),(1,0),(1,2),(1,3),(2,0),(2,1),(2,3),(3,0),(3,1),(3,2)]
*Main>  m@(qs, s, fs, d) = binopFSM (/=) avoid_aab odd_bs
*Main> qs
[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]
*Main> fs
[(0,0),(1,0),(2,0),(3,1)]
*Main> s
(0,0)
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)],(0,0),[(0,0),(1,0),(2,0),(3,1)],
[((0,0),'a',(1,0)),((0,0),'b',(0,1)),((0,1),'a',(1,1)),((0,1),'b',(0,0)),((1,0),'a',(2,0)),
((1,0),'b',(0,1)),((1,1),'a',(2,1)),((1,1),'b',(0,0)),((2,0),'a',(2,0)),((2,0),'b',(3,1)),((2,1),
'a',(2,1)),((2,1),'b',(3,0)),((3,0),'a',(3,0)),((3,0),'b',(3,1)),((3,1),'a',(3,1)),((3,1),'b',(3,0))])
*Main> nreachable $ reverseFSM $ binopFSM (/=) avoid_aab odd_bs
[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]
*Main>  m@(qs, s, fs, d) = binopFSM (/=) end_ab end_ab
*Main> qs
[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)]
*Main> s
(0,0)
*Main> fs
[(0,2),(1,2),(2,0),(2,1)]
*Main>  (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)],(0,0),[(0,2),(1,2),(2,0),
(2,1)],[((0,0),'a',(1,1)),((0,0),'b',(0,0)),((0,1),'a',(1,1)),((0,1),'b',(0,2)),((0,2),'a',
(1,1)),((0,2),'b',(0,0)),((1,0),'a',(1,1)),((1,0),'b',(2,0)),((1,1),'a',(1,1)),((1,1),'b',(2,2)),
((1,2),'a',(1,1)),((1,2),'b',(2,0)),((2,0),'a',(1,1)),((2,0),'b',(0,0)),((2,1),'a',(1,1)),((2,1),'b',
(0,2)),((2,2),'a',(1,1)),((2,2),'b',(0,0))])
*Main> nreachable $ reverseFSM $ binopFSM (/=) end_ab end_ab
[(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
*Main> m@(qs, s, fs, d) = binopFSM (/=) end_ab avoid_aab
*Main> qs
[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)]
*Main> s
(0,0)
*Main> fs
[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,3)]
*Main>  (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)],(0,0),
[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,3)],[((0,0),'a',(1,1)),((0,0),'b',(0,0)),
((0,1),'a',(1,2)),((0,1),'b',(0,0)),((0,2),'a',(1,2)),((0,2),'b',(0,3)),((0,3),'a',(1,3)),
((0,3),'b',(0,3)),((1,0),'a',(1,1)),((1,0),'b',(2,0)),((1,1),'a',(1,2)),((1,1),'b',(2,0)),
((1,2),'a',(1,2)),((1,2),'b',(2,3)),((1,3),'a',(1,3)),((1,3),'b',(2,3)),((2,0),'a',(1,1)),
((2,0),'b',(0,0)),((2,1),'a',(1,2)),((2,1),'b',(0,0)),((2,2),'a',(1,2)),((2,2),'b',(0,3)),
((2,3),'a',(1,3)),((2,3),'b',(0,3))])
*Main> nreachable $ reverseFSM $ binopFSM (/=) end_ab avoid_aab
[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3),(2,0),(2,1),(2,2),(2,3)]
*Main> m@(qs, s, fs, d) = binopFSM (/=) end_ab odd_bs
*Main> qs
[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]
*Main> s
(0,0)
*Main> fs
[(0,1),(1,1),(2,0)]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)],(0,0),[(0,1),(1,1),(2,0)],
[((0,0),'a',(1,0)),((0,0),'b',(0,1)),((0,1),'a',(1,1)),((0,1),'b',(0,0)),((1,0),'a',(1,0)),
((1,0),'b',(2,1)),((1,1),'a',(1,1)),((1,1),'b',(2,0)),((2,0),'a',(1,0)),((2,0),'b',(0,1)),
((2,1),'a',(1,1)),((2,1),'b',(0,0))])
*Main> nreachable $ reverseFSM $ binopFSM (/=) end_ab odd_bs
[(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]
*Main> m@(qs, s, fs, d) = reverseFSM odd_bs
*Main> qs
[0,1]
*Main> s
[1]
*Main> fs
[0]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1],[1],[0],[(0,'a',[0]),(0,'b',[1]),(1,'a',[1]),(1,'b',[0])])
*Main> nreachable m
[0,1]
*Main> m@(qs, s, fs, d) = reverseFSM avoid_aab
*Main> qs
[0,1,2,3]
*Main> s
[0,1,2]
*Main> fs
[0]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1,2,3],[0,1,2],[0],[(0,'a',[]),(0,'b',[0,1]),(1,'a',[0]),(1,'b',[]),
(2,'a',[1,2]),(2,'b',[]),(3,'a',[3]),(3,'b',[2,3])])
*Main> nreachable m
[0,1,2]
*Main> m@(qs, s, fs, d) = reverseFSM end_ab
*Main> qs
[0,1,2]
*Main> s
[2]
*Main> fs
[0]
*Main>  (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1,2],[2],[0],[(0,'a',[]),(0,'b',[0,2]),(1,'a',[0,1,2]),(1,'b',[]),(2,'a',[]),(2,'b',[1])])
*Main> nreachable m
[0,1,2]
*Main> m@(qs, s, fs, d) = minimize odd_bs
*Main> qs
[0,1]
*Main> s
0
*Main> fs
[1]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1],0,[1],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)])
*Main> nreachable $ reverseFSM $ minimize odd_bs
[0,1]
*Main> m@(qs, s, fs, d) = minimize avoid_aab
*Main> qs
[0,1,2,3]
*Main> s
0
*Main> fs
[0,1,2]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1,2,3],0,[0,1,2],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),(2,'a',2),(2,'b',3),(3,'a',3),(3,'b',3)])
*Main> nreachable $ reverseFSM $ minimize avoid_aab
[0,1,2]
*Main>  m@(qs, s, fs, d) = minimize end_ab
*Main> qs
[0,1,2]
*Main> s
0
*Main> fs
[2]
*Main> (qs, s, fs, [(q,a,d q a) | q <- qs, a <- sigma])
([0,1,2],0,[2],[(0,'a',1),(0,'b',0),(1,'a',1),(1,'b',2),(2,'a',1),(2,'b',0)])
*Main> nreachable $ reverseFSM $ minimize end_ab
[0,1,2]
-}