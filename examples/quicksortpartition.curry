-- Implementation of quicksort with partition
-- Use option "-e" for DSDCurry (see part'post below).

perm []     = []
perm (x:xs) = ndinsert (perm xs)
    where ndinsert [] = [x]
          ndinsert (y:ys) = (x:y:ys) ? (y:ndinsert ys)

sorted [] = success
sorted [_] = success
sorted (x:y:ys) = (x<=y)=:=True & sorted (y:ys)

-- User contract:
sort'pre _ = True
sort'post xs ys = length xs == length ys

-- Specification of sort:
-- A list is a sorted result of an input if it is a permutation and sorted.
sort'spec :: [Int] -> [Int]
sort'spec x | y =:= perm x & sorted y = y  where y free

-- Implementation of sort with quicksort and partition:
sort :: [Int] -> [Int]
sort [] = []
sort (x:xs) = let (low,high) = part x xs in sort low ++ x : sort high

-- Contract for partition: since we put no restriction on the order
-- of the partioned elements, the result can be any permutation
-- (i.e., this is not a precise but a weak specification).
-- Consequence: the postcondition is nondeterministic if the input list
-- contains multiple values. Thus, it should be checked with option "-e".
part'pre _ _ = True
part'post x xs (u,v) | (u++v) =:= perm xs = all (<x) u && all (>=x) v

part :: Int -> [Int] -> ([Int],[Int])
part _ [] = ([],[])
part x (y:ys) = if y<x then (y:u,v) else (u,y:v)
       where (u,v) = part x ys

input = [26,18,5,4,16,8,22,17]

main = sort input
