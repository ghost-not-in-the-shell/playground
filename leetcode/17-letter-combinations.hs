letterCombinations :: [Int] -> [String]
letterCombinations [n] =
  letterChar n >>= \ c ->
  return [c]
letterCombinations (n:ns) =
  letterChar n          >>= \ c ->
  letterCombinations ns >>= \ cs ->
  return (c:cs)

letterChar :: Int -> [Char]
letterChar 2 = "abc"
letterChar 3 = "def"
letterChar 4 = "ghi"
letterChar 5 = "jkl"
letterChar 6 = "mno"
letterChar 7 = "pqrs"
letterChar 8 = "tuv"
letterChar 9 = "wxyz"
