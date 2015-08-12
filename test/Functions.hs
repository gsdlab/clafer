{-
 Copyright (C) 2013-2015 Luke Brown, Michal Antkiewicz <http://gsd.uwaterloo.ca>

 Permission is hereby granted, free of charge, to any person obtaining a copy of
 this software and associated documentation files (the "Software"), to deal in
 the Software without restriction, including without limitation the rights to
 use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 of the Software, and to permit persons to whom the Software is furnished to do
 so, subject to the following conditions:

 The above copyright notice and this permission notice shall be included in all
 copies or substantial portions of the Software.

 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 SOFTWARE.
-}
module Functions where

import qualified Data.List as List
import qualified Data.Map as Map
import Language.Clafer
import System.Directory

getClafers :: FilePath -> IO [(String, String)]
getClafers dir = do
                    files <- getDirectoryContents dir
                    let claferFiles = List.filter checkClaferExt files
                    claferModels <- mapM (\x -> readFile (dir++"/"++x)) claferFiles
                    return $ zip claferFiles claferModels

checkClaferExt :: String -> Bool
checkClaferExt "des.cfr" = True
checkClaferExt file' = if ((eman == "")) then False else (txe == "rfc") && (takeWhile (/='.') (tail eman) /= "esd")
    where (txe, eman) = span (/='.') (reverse file')


compileOneFragment :: ClaferArgs -> InputModel -> Either [ClaferErr] (Map.Map ClaferMode CompilerResult)
compileOneFragment args' model =
    runClafer (argsWithOPTIONS args' model) $
        do
            addModuleFragment model
            parse
            iModule <- desugar Nothing
            compile iModule
            generate

getCompilerResult :: InputModel -> CompilerResult
getCompilerResult    model = case compileOneFragment defaultClaferArgs{keep_unused=True} model of
  Left errors -> error $ show errors
  Right compilerResultMap -> case Map.lookup Alloy compilerResultMap of
    Nothing -> error "No Alloy result in the result map"
    Just compilerResult -> compilerResult

compiledCheck :: Either a b -> Bool
compiledCheck (Left _) = False
compiledCheck (Right _) = True

fromLeft :: Either a b -> a
fromLeft (Left a) = a
fromLeft (Right _) = error "Function fromLeft expects argument of the form 'Left a'"

fromRight :: Either a b -> b
fromRight (Right b) = b
fromRight (Left _) = error "Function fromLeft expects argument of the form 'Right b'"

andMap :: (a -> Bool) -> [a] -> Bool
andMap f lst = and $ map f lst
