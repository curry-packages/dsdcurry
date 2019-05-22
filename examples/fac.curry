-- Defining factorial numbers:

-- Specification: the usual recursive definition
fac'spec n = if n==0 then 1 else n * fac'spec (n-1)

-- The input should be non-negative:
fac'pre n = n>=0
-- The result should be positive:
fac'post _ v = v>0

-- An implementation using Prelude operations:
fac :: Int -> Int
fac n = foldr (*) 1 [1..n]
-- ..or no implementation:
--fac = unknown
