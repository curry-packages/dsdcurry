-- Fibonacci numbers specified by traditional recursive definition
-- and computed efficiently by an infinite list.

-- Specification of Fibonacci numbers:
fib'pre x = x >= 0
fib'post _ y = (y > 0)
fib'spec x | x == 0 = 0
           | x == 1 = 1
           | otherwise = fib'spec (x-1) + fib'spec (x-2)

-- Implementation of Fibonacci numbers:
fib n = fiblist 0 1 !! n
 where
  fiblist x y = x : fiblist y (x+y)
