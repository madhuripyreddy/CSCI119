---- CSci 119, Lab 1 ----

-- Note: you will replace all instances of "undefined" below with your answers.


---- Boolean operators

-- The following code tests whether "and" is commutative:
bools = [True, False]
and_commutes = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar definitions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and"
or_commutes = and [(p || q) == (q || p) | p <- bools, q <- bools]
and_assoc = and [(p && (q && r)) == ((p && q) && r) | p <- bools, q <- bools, r <- bools]
or_assoc = or [(p || (q || r)) == ((p || q) || r) | p <- bools, q <- bools, r <- bools]
and_dist = and [(p && (q || r)) == ((p && q) && (p && r)) | p <- bools, q <- bools, r <- bools]
or_dist = or [(p || (q && r)) == ((p || q) && (p || r)) | p <- bools, q <- bools, r <- bools]
          
-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above
xor_commutes = and [(p /= q) == (q /= p) | p <- bools, q <- bools]
xor_assoc    = and [((p /= q) /= r) == (p /= (q /= r)) | p <- bools, q <- bools, r <- bools]
xor_dist_and = and [(p /= (q /= r)) == ((p /= q) && (p /= r)) | p <- bools, q <- bools, r <- bools]
xor_dist_or  = and [(p /= (q || r)) == ((p /= q) || (p /= r)) | p <- bools, q <- bools, r <- bools]
and_dist_xor = and [(p && (q /= r)) == ((p && q) /= (p && r)) | p <- bools, q <- bools, r <- bools]
or_dist_xor  = or [(p || (q /= r)) == (( p || q) /= (p || r)) | p <- bools, q <- bools, r <- bools]
               
-- The implication operator on Bool in Haskell is equivalent to <=.
-- Check whether implication is associative or commutative:
assoc_imp = and [(p <= (q <= r)) == ((p <= q) <= r) | p <- bools, q <- bools, r <- bools]
comm_imp = and [(p <= q) == (q <= p) | p <- bools, q <- bools]


----- Evaluating statements involving quantifiers

-- Assume that the universe of discourse is the set {1,2,3,4,5,6,7,8},
-- that is, that the word "number" temporarily means 1, 2, ..., 8.
-- Your solutions to the problems below should work no matter what
-- finite list of integers u is. For example, u = [5, 2, 17, 58, 21].

u = [1..8]

-- Translate each of the following statements first, in a comment, into a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true. I'll work one example.

-- 1. "Every number that's greater than 2 is greater than 1"
-- A: forall n, (n > 2) imp (n > 1)
prob1_1 = and [(n > 2) <= (n > 1) | n <- u]   -- direct translation
prob1_2 = and [n > 1 | n <- u, n > 2]         -- using bounded quantifier

-- 2. Every number is either greater than 1 or less than 2
-- A: forall n, (n > 1) or (n < 2)
prob2 = or[(n > 1) || (n < 2) | n <- u]

-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- A: forall x, forall y, (x >= y) or (y <= x)
prob3 = and[(x >= y) || (y <= x) | x <- u, y <- u]

-- 4. There is an odd number greater than 4
-- A: exists odd x, (x > 4)
prob4 = or[x > 4 | x <- u, odd x]

-- 5: There are two odd numbers that add up to 10
-- A: exists odd x, odd y, (x + y == 10)
prob5 = or[((x + y) == 10) | y <- u, x <- u, odd x, odd y]

-- 6. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- A: exists odd x, exists even y, y > x
prob6 = and[or[y > x | y <- u, even y] | x <- u, odd x]

-- 7. For every even number, there is a greater odd number
-- A: forall even x, forall even y, y > x
prob7 = and[or[y > x | y <- u, odd y] | x <- u, even x]

-- 8. There are two odd numbers that add up to 6
-- A: exists odd x, exists odd y, x + y == 6
prob8 = and[or[x + y == 6 | y <- u, odd y] | x <- u, odd x]

-- 9. There is a number that is at least as large as every number
--    (i.e., according to >=)
-- A: forall x, exists y, y >= x
prob9 = and[or[y >= x | y <- u] | x <- u]

-- 10. For every number, there is a different number such that there are no
--    numbers between these two.
-- A: forall x, exists y, (x /= y) and (not (exists z, (x < z < y) or (y < z < x)))
prob10 = and [or [x /= y && not(or [(x<z && z<y) || (y<z && z<x) | z <- u]) | y <- u] | x <- u]