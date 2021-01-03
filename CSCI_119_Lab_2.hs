---- CSci 119, Fall 2019, Lab 2 ----

import Data.List

-- As in Lab 1, we will be working with the finite universe U = [1..8]
u = [1..8]


----- PART 1:  Relations on u -----

-- A relation, R, on U is a list of the ordered pairs of elements of U:
type Reln = [(Int,Int)]
              
-- For example, here are the < and <= relations
less_reln :: Reln
less_reln = [(i,j) | j <- [1..8], i <- [1..j-1]]

leq_reln :: Reln
leq_reln  = [(i,j) | j <- [1..8], i <- [1..j]]
            
-- and here is the relation of equivalence mod 3:
eqmod3_reln :: Reln
eqmod3_reln = [(i,j) | i <- [1..8], j <- [1..8], (j - i) `mod` 3 == 0]


-- Write a function refl that tests whether a relation is reflexive:
-- R is reflexive if: forall a, (a,a) in R
-- Example: [(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8)] is the
-- smallest reflexive relation over u. Anything that does not contain
-- these 8 elements is not reflexive
refl :: Reln -> Bool
refl rs = and[(a,a) `elem` rs | a <- u]

-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
-- Example: [(1,1), (1,2), (2,1)] is symmetric but [(1,1), (1,2)] is not.
symm :: Reln -> Bool
symm rs = and [((a,b) `elem` rs) <= ((b,a) `elem` rs) | a <- u, b <- u]

-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, (a,b) in R /\ (b,c) in R -> (a,c) in R
-- Example: [(1,2),(2,3),(1,3),(4,4)] is transitive but [(2,3),(3,2)] is not
trans :: Reln -> Bool
trans rs = and[(((a,b) `elem` rs) && ((b,c) `elem` rs) <= ((a,c) `elem` rs)) | a <- u, b <- u, c <- u]


-- Use the functions above to check the less, leq, and eqmod3 relations for
-- relexivity, symmetry, and transitivity

--refl less_reln |-> False
-- refl leq_reln |-> True
-- refl eqmod3_reln |-> True

-- symm less_reln |-> False
-- symm leq_reln |-> False
-- symm eqmod3_reln |-> True

-- trans less_reln |-> True
-- trans leq_reln |-> True
-- trans eqmod3_reln |-> True

-- For each of the 8 possible combinations of yes/no on reflexivity,
-- symmetry, and transitivity, find a MINIMAL relation on u that has exactly
-- that combination of properties. Add a test to check whether you got the
-- properties right. (I'll do the first one as an example.)

-- refl, symm, trans
rst :: Reln
rst = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8)]
rst_test = refl rst && symm rst && trans rst

-- refl, symm, not trans
rst' :: Reln
rst' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (1,3), (3,1), (2,4), (4,2)]
rst'_test = refl rst && symm rst && not (trans rst)

-- refl, not symm, trans
rs't :: Reln
rs't = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (2,3), (3,4)]
rs't_test = refl rst && not (symm rst) && trans rst

-- refl, not symm, not trans
rs't' :: Reln
rs't' = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (1,3), (3,5)]
rs't'_test = refl rst && not (symm rst) && not (trans rst)

-- not refl, symm, trans
r'st :: Reln
r'st = []
r'st_test = not (refl rst) && symm rst && trans rst 

-- not refl, symm, not trans
r'st' :: Reln
r'st' = [(2,3), (3,2)]
r'st'_test = not (refl rst) && symm rst && not (trans rst) 

-- not refl, not symm, trans
r's't :: Reln
r's't = [(2,3)]
r's't_test = not (refl rst) && not (symm rst) && trans rst 

-- not refl, not symm, not trans
r's't' :: Reln
r's't' = [(1,2), (2,3)]
r's't'_test = not (refl rst) && not (symm rst) && not (trans rst) 


---- PART 2: Partitions of u -----

-- A partitition, P, of u is a list of blocks, which are lists of elements
-- of u, that satisfies certain these conditions:
-- nontrivial: forall X in P, exists x in U, x in X, or
--             {} not in P
-- total: forall x in U, exists X in P, x in X
-- disjoint: forall X,Y in P (exists a, a in X /\ a in Y) -> X = Y, or
--           forall X,Y in P, X /= Y -> X intersect Y = {}
-- For example, here is the partition of u corresponding to equivalence mod 3:
eqmod3_part :: [[Int]]
eqmod3_part = [[1,4,7], [2,5,8], [3,6]]



-- Write a function part that tests whether a list of lists is a partition of u
nontrivial :: [[Int]] -> Bool
nontrivial bs = and [bss /= [] | bss <- bs]

complete :: [[Int]] -> Bool
complete bs = and [or [(bss `elem` bs) && (a `elem` bss) | bss <- bs] | a <- u]

inters :: [Int] -> [Int] -> [Int]
inters xs ys = [x | x <- xs, elem x ys]

disjoint :: [[Int]] -> Bool
disjoint bs = and [((xs `elem` bs) && (ys `elem` bs)) <= ((xs == ys) || (inters xs ys == []))| xs <- bs, ys <- bs]

part :: [[Int]] -> Bool
part bs = nontrivial bs && complete bs && disjoint bs
-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u.
eq2part :: Reln -> [[Int]]
eq2part rs = eq2part' u where    -- start with elements of u
  eq2part' [] = []               -- when there's no more elements left, we're done
  eq2part' (a:as) = let block = [b | b <- u, (a,b) `elem` rs]
                    in block : eq2part' (as \\ block)


-- Write a function part2eq that takes a partition of u as input and returns
-- the associated equivalence relation on u. You can assume that the argument
-- is really a partition of u.
part2eq :: [[Int]] -> Reln
part2eq bs = [(x,y) | parts <- bs, x <- parts, y <- parts]
