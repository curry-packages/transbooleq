-- The classical last element of a list:

import Test.EasyCheck

last :: Eq a => [a] -> a
last xs | _ ++ [x] == xs = x  where x free

main :: Int
main = last [1,2,3]

test_last = last [1,2,3] -=- 3
