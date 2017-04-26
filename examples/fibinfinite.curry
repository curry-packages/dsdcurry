-- An infinite list of Fibonacci numbers specified by traditional
-- recursive definition
-- NOTE: assertion checking requires lazy assertions!

-- (Deterministic!) specification of all Fibonacci numbers:
fibs'specd = map fib [0..]
 where fib n | n == 0 = 0
             | n == 1 = 1
             | otherwise = fib (n-1) + fib (n-2)

-- A more efficient (but erroneous) implementation of all Fibonacci numbers:
fibs = fiblist 0 1
 where
  fiblist x y = x : fiblist (x+y) y

main = take 4 fibs
