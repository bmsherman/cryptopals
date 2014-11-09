module Main where
import Control.Monad.IO.Class (liftIO)
import Data.Maybe (fromJust, isJust)
import Snap.Core
import Snap.Http.Server
import Control.Applicative (optional, (<$>), (<|>))
import Control.Concurrent (threadDelay)
import Crypto4 (un16, hmac, randomKey, BString, randomize, wrdB, strB, to16)
import Data.ByteString as B


--This is our server for problems 31 and 32.

--Delay for problem 31, in microseconds (=50 milliseconds)
delay31 = 50000

--Delay for problem 32, in microseconds (=10 milliseconds)
delay32 = 10000

--The delay we are using this time in the server
delay = delay32


--Our main method generates and random key, then fires up the server.
main :: IO ()
main = do
	(k,_) <- randomize (randomKey 16) 
	quickHttpServe (site k)

--And below, we implement the website as specified.
--Note that I actually return the correct tag in the body of the response. This is
--just for confirming as I watch the guessing process go in the other file. I don't
--ever use that tag, of course!

site :: BString -> Snap ()
site key = do
	file <- getParam (wrdB "file")
	signature <- fmap (un16 . strB) <$> getParam (wrdB "signature")
	valid <- liftIO $ if (isJust file && isJust signature)
		then insecure_compare key (fromJust file) (fromJust signature)
		else return False
	modifyResponse $ setResponseCode (if valid then 200 else 500)
	if (isJust file) then writeBS . wrdB . to16 . hmac key . fromJust $ file
			 else return ()


insecure_compare :: BString -> BString -> BString -> IO Bool
insecure_compare k m t = slow_equality t t' where
	t' = hmac k m

slow_equality :: BString -> BString -> IO Bool
slow_equality m1 m2 | B.null m1 && B.null m2 = return True
slow_equality m1 m2 | not (B.null m1) && not (B.null m2) = 
	if (B.head m1==B.head m2) then threadDelay delay >> slow_equality (B.tail m1) (B.tail m2) else return False
slow_equality m1 m2 | otherwise = return False
