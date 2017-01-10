import Test.DocTest

main :: IO ()
main = doctest ["-isrc", "src/Language/Clafer/Intermediate/TypeSystem.hs"]
