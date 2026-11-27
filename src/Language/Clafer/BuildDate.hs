{-
 Copyright (C) 2026 Michal Antkiewicz <http://gsd.uwaterloo.ca>

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
-- | The build date of a program, @YYYY-MM-DD@, in UTC: the day the module with the splice
--   @$(buildDateQ)@ is compiled, or the day of @SOURCE_DATE_EPOCH@ (seconds since 1970) when it is
--   set, e.g., to pin the release date. clafer ("Language.Clafer.Version") and claferIG use it.
module Language.Clafer.BuildDate (buildDateQ) where

import Data.Time.Clock (getCurrentTime)
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import Data.Time.Format (defaultTimeLocale, formatTime)
import Language.Haskell.TH (Exp, Q, runIO, stringE)
import System.Environment (lookupEnv)
import Text.Read (readMaybe)

-- | The build date as a string literal.
buildDateQ :: Q Exp
buildDateQ = runIO today >>= stringE
  where
  today = do
    epoch <- (>>= readMaybe) <$> lookupEnv "SOURCE_DATE_EPOCH"
    time <- maybe getCurrentTime (pure . posixSecondsToUTCTime . fromInteger) epoch
    pure $ formatTime defaultTimeLocale "%F" time
