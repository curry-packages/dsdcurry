-- Examples with nondeterministicm specifications

coin'spec = 0 ? 1

coin = 1 ? 0

main = coin  --> should be executed without violation

coin3'spec = coin'spec

coin3 = coin ? 2

main3 = coin3  --> violation
