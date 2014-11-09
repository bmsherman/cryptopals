module Crypto4 where
import SHA (sha1', SHA1State, padSHA1, initialSHA1State, sha1cc', fromState)
import Control.Applicative ((<$>))
import Data.Bits
import Data.Ord (comparing)
import Data.List (find, isInfixOf, maximumBy, sortBy)
import Data.Word (Word8)
import Data.Char (toUpper, toLower, chr, ord, isLetter)
import Data.Maybe (fromJust, catMaybes, isJust)
import Data.Time.Clock (getCurrentTime, NominalDiffTime, utctDayTime, diffUTCTime)
import Codec.Crypto.AES
import Network.HTTP
import System.Random
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as B (fromChunks, toStrict)
import qualified Codec.Binary.Base16 as B16
import qualified Codec.Binary.Base64 as B64
import qualified Crypto.Hash.MD4 as M

type BString = B.ByteString


--
--Useful functions
--

--Convert a Word8 to its ASCII character
chrB :: Word8 -> Char
chrB = chr.fromIntegral

strB = map chrB . B.unpack

toLazy str = B.fromChunks [str]

--Convert an ASCII character to Word8
ordB :: Char -> Word8
ordB x | ord x > 255 = error "Character not ASCII"
ordB x | otherwise   = fromIntegral (ord x)

wrdB = B.pack . map ordB

--Functions to encode and decode to Hex and base 64 in the proper format.
un16, un64 :: String -> BString
un16 = B.pack . fromJust . B16.decode . map toUpper
un64 = B.pack . fromJust . B64.decode

to16, to64 :: BString -> String
to16 = map toLower . B16.encode . B.unpack
to64 = B64.encode . B.unpack


--PKCS#5 padding
pad :: BString -> BString
pad m = m `B.append` B.replicate l (fromIntegral l) where
	l =  16 - snd (B.length m `divMod` 16)

--Returns Just a value if the predicate is true; otherwise Nothing
onlyIf :: a -> Bool -> Maybe a
x `onlyIf` pred = if pred then Just x else Nothing

--returns unpadded string, if the PKCS#5 padding was valid
vunpad :: BString -> Maybe BString
vunpad m = B.take (l-n) m `onlyIf` pred where
	n = fromIntegral (B.last m)
	l = B.length m
	pred = n<=l && n>0 && ( and $ map (==fromIntegral n) $ B.unpack $ (B.drop (l-n) m) )


--Break a bytestring into chunks of size n
chunksB :: Int -> BString -> [BString]
chunksB n bs | B.null bs = []
chunksB n bs | otherwise = B.take n bs : chunksB n (B.drop n bs)



--16 bytes of 0...
baseIV = B.replicate 16 0

--XOR two ByteStrings against each other
xorB :: BString -> BString -> BString
xorB x y = B.pack (B.zipWith xor x y)

--encrypt with AES in ECB mode
ecbEncrypt :: BString -> BString -> BString
ecbEncrypt key str = crypt' ECB key iv Encrypt str where
	iv = baseIV

--decrypt with AES in ECB mode
ecbDecrypt ::  BString -> BString -> BString
ecbDecrypt key str =  crypt' ECB key iv Decrypt str where
	iv = baseIV

--encrypt with AES in CBC mode
cbcEncrypt :: BString -> BString -> BString -> BString
cbcEncrypt key iv str | B.null str = B.empty
cbcEncrypt key iv str | otherwise  = fblock `B.append` cbcEncrypt key fblock (B.drop 16 str) where
	fblock = ecbEncrypt key (xorB (B.take 16 str) iv)

--decrypt with AES in CBC mode
cbcDecrypt :: BString -> BString -> BString -> BString
cbcDecrypt key iv str | B.null str = B.empty
cbcDecrypt key iv str | otherwise  = fblock `B.append` cbcDecrypt key (B.take 16 str) (B.drop 16 str) where
	fblock = xorB (ecbDecrypt key (B.take 16 str)) iv

--Here's how CBC encoding and decoding is done in practice. We simply transmit the IV
--at the beginning of the ciphertext.
cbcEIV key iv str = iv `B.append` cbcEncrypt key iv (pad str)
cbcDIV key str = cbcDecrypt key (B.take 16 str) (B.drop 16 str)
cbcDIVU key str = vunpad $ cbcDIV key str

--Convert a bytestring to an integer
strToInt str | B.length str == 1 = fromIntegral (B.last str)
strToInt str | otherwise         = fromIntegral (B.last str) + 256*(strToInt (B.init str))

--Convert an integer to a variable-length bytestring
intToStr n | n < 256 = B.singleton (fromIntegral n)
intToStr n | otherwise = intToStr quot `B.snoc` (fromIntegral remainder) where
	(quot, remainder) = n `divMod` 256

--Convert an integer to an 8-byte bytestring that represents it(mod 2^32)
intToStr8 n = m `B.append` B.replicate (8-l) 0  where
	m = B.take 8 $ intToStr n
	l = B.length m

--Encrypt using AES CTR mode
ctrEncrypt :: BString -> BString -> BString -> BString
ctrEncrypt key nonce m = ecbEncrypt key encrstring `xorB` m where
	numblocks = fst ((B.length m-1) `divMod` 16) + 1
	encrstring = B.concat $ map genIV [0..numblocks-1]
	genIV n = nonce `B.append` intToStr8 n

--Decrypting with AES CTR mode is the same as encrypting
ctrDecrypt = ctrEncrypt

--Encrypt with counter mode with a randomized nonce, and append the nonce and initial counter
ctrE key m = do 
	r <- newStdGen;
	let nonce = B.pack $ fst $ randomL 8 r
	return $ nonce `B.append` intToStr8 0 `B.append` ctrEncrypt key nonce m

--Decrypt a message encrypted with ctrE
ctrD key c = ctrDecrypt key (B.take 8 c) (B.drop 16 c)


--Gives a random seed to a function that asks for one
randomize :: (StdGen -> b) -> IO b
randomize f = f <$> newStdGen

--Creates a list of random characters of a given length, and a new random seed
randomL :: (RandomGen g, Random b) => Int -> g -> ([b], g)
randomL num rand = randomL' num ([],rand) where
	randomL' 0 (xs,r) = (xs,r)
	randomL' n (xs,r) = randomL' (n-1) ((first : xs), r2) where
		(first, r2) = random r

--Selects a random element of a list
randomList :: RandomGen g => [a] -> g -> (a, g)
randomList xs r = (xs !! val, r2) where
	(val, r2) = randomR (0, length xs-1) r

--Yields a random bytestring of length n
randomKey :: RandomGen g => Int -> g -> (BString, g)
randomKey n r = (\(k,r) -> (B.pack k, r))$ randomL n r






--
--Problem 25
--


--Our decrypted secret text for problem 25
secret :: IO BString
secret = ecbDecrypt (wrdB "YELLOW SUBMARINE") . un64 . filter (/='\n') <$> readFile "p25.txt"

--Encrypt the secret under CTR mode with a random key, and return a function which allows
--us to edit the ciphertext by decrypting, cutting off the ciphertext at the nth position,
--and adding the edit text, and then re-encrypting with the same nonce
genOracle25 :: BString -> StdGen -> (Int -> BString -> BString)
genOracle25 secret r = modify where
	(key, r2) = randomKey 16 r
	nonce = B.pack $ fst $ randomL 8 r2
	modify n str = ctrEncrypt key nonce $ editplain secret n str

--This is our implementation of the edit function (dealing all with plaintext)
editplain :: BString -> Int -> BString -> BString
editplain txt1 n txt2 = B.take n txt1 `B.append` txt2

--This function, given the edit function, allows us to recover the ciphertext by submitting
--a trivial edit
ciphertext25 :: (Int -> BString -> BString) -> BString
ciphertext25 editor = editor (2^20) B.empty

--This function, using the editor, determines the plaintext at position n
byte25 :: (Int -> BString -> BString) -> Int -> Word8
byte25 editor n = (ciphertext25 editor `B.index` n) `xor` ((editor n (B.singleton 0)) `B.index` n)

--This function uses the previous one to determine the entire plaintext
break25 :: (Int -> BString -> BString) -> BString
break25 editor = B.pack $ map (byte25 editor) [0..l-1] where
	c = ciphertext25 editor
	l = B.length c

--And here we put our entire answer together, encrypting the message under a random key,
--breaking it using our oracle and our smarts, and showing that we get the correct message.
answer25 :: IO Bool
answer25 = do
	s <- secret
	editor <- randomize (genOracle25 s)
	let broken = break25 editor
	(sequence . map putStrLn . lines . strB) broken
	return (broken==s)



--
--Problem 26
--


prepend6 =  "comment1=cooking%20MCs;userdata=" --length 32
append6 =   ";comment2=%20like%20a%20pound%20of%20bacon" --length 42


--Generates our two oracle functions. One encrypts, while the other tests to see if the user is an administrator.
--genET :: StdGen -> (IO (String -> BString), (BString -> Bool))
genET r = (encryptor, tester)  where
	encryptor m = ctrE key $ (wrdB . addstuff) m
	tester = test26 . strB . ctrD key
	(key, _) = randomKey 16 r

--Test whether the person is an admin, according to the decrypted text
test26 :: String -> Bool
test26 = isInfixOf ";admin=true"

--Prevents us from injecting the admin=true in the userdata naively
safeMap :: Char -> String
safeMap '=' = "\"=\""
safeMap '&' = "\"&\""
safeMap  c = [c]

--This function inserts our userdata inside the larger string
addstuff :: String -> String
addstuff s = prepend6 ++ concatMap safeMap s ++ append6


--And here's where our strategy will come in. We simply XOR in our edit.
toXOR = B.replicate 48 0 `B.append` (wrdB ";admin=true" `xorB` wrdB "innocenttxt")  `B.append` B.replicate 42 0

--This is the function that XORs in the edit from above
modCipherText :: BString -> BString
modCipherText c = toXOR `xorB` c

--Here's our answer to problem #26
solve26 = do
	(encryptor, tester) <- randomize genET
	c <- encryptor "innocenttxt"
	return $ tester (modCipherText c)



--
--Problem 27
--

--Here are our encryption and decryption algorithms using the key as an IV
dumbCBCE key m = cbcEncrypt key key (pad m)
dumbCBCD key c = cbcDecrypt key key c


--This function takes in a bytestring s, and returns Right s if s is valid ASCII,
--and an error that includes s otherwise.
compliant :: BString -> Either String BString
compliant s = if B.any (>127) s then Left ("Non-compliant ASCII: " ++ strB s) else Right s

--Our secret message we'll encode for this problem.
secret27 = wrdB "What did one snowman say to the other snowman? Smells like carrots."


--This generates our oracle. We take a random key, and return both the encrypted
--message, as well as our decryptor function
genOracle27 :: StdGen -> (BString, BString -> Either String BString)
genOracle27 r = (dumbCBCE key secret27, compliant . dumbCBCD key) where
	(key, _) = randomKey 16 r

--Here is the modification we make to the ciphertext, according to the recipe we're given
modify27 :: BString -> BString
modify27 c = c1 `B.append` B.replicate 16 0 `B.append` c1 where
	c1 = B.take 16 c

--If we've made the proper substitution, this looks at the results and returns our
--key, according to the recipe we're given.
recoverKey :: Either String BString -> Maybe BString
recoverKey (Right _) = Nothing
recoverKey (Left s) = Just $ (cs !! 0) `xorB` (cs !! 2) where
	cs = (chunksB 16 . wrdB . drop 21) s

--And here we put everything together, and decrypt our message under the key.
--Since we do indeed get our secret message, we know the key is correct!
solve27 :: IO BString
solve27 = do
	(c, decryptor) <- randomize genOracle27
	let rkey = (fromJust . recoverKey . decryptor) (modify27 c)
	putStrLn ( "Key: " ++ (to16 rkey) )
	return $ dumbCBCD rkey c


--
--Problem 28
--

--Naively sign a message with SHA1
sign :: BString -> BString -> SHA1State
sign k m = sha1' (toLazy (k `B.append` m))

--Verify naive signature
verify :: BString -> BString -> SHA1State -> Bool
verify k m t = sign k m == t

--This just empirically confirms that when we verify something
--that we signed and didn't modify, we indeed say True
testcorrect28step :: IO Bool
testcorrect28step = do
	(key, r2) <- randomize (randomKey 16)
	let m = fst $ randomKey 128 r2
	return $ verify key m (sign key m)

--Here we test it 1000 times and return the number of times it is correct.
--Always 1000, fortunately!
testcorrect28 :: IO Int
testcorrect28 = length . filter id <$> (sequence . replicate 1000) testcorrect28step


--
--Problem 29
--

--Our original message for this problem
message29 = wrdB "comment1=cooking%20MCs;userdata=foo;comment2=%20like%20a%20pound%20of%20bacon"

--The extension we'd like to add
extension29 = wrdB ";admin=true"

--MD paddding, according to the standard
hpad :: BString -> BString
hpad m = (partialpad m) `B.append` pad2 where
	lenbits = intToStr (8*B.length m)
	plenbits = B.replicate (8-B.length lenbits) 0 `B.append` lenbits
	words = chunksB 4 plenbits
	pad2 = (words !! (length words - 2)) `B.append` (last words)

--Here we just pad a 1 bit followed by 0 bits to get the proper size,
--before appending the length of the message.
partialpad :: BString -> BString
partialpad m = m `B.append` pad1 where
	(n, k) = B.length m `divMod` 64
	pad1 = (0 `setBit` 7) `B.cons` B.replicate ((55-k) `mod` 64) 0

--Given a message and its hash, we add the glue padding, add an extension message,
--and use the previous hash to compute the hash of the extend message.
--All we really need from the first message is its length; not its actual contents.
extendHash :: BString -> SHA1State -> BString -> (BString, SHA1State)
extendHash message tag extension = (newm, sha1cc' tag toHash) where
	newm = hpad message `B.append` extension
	l = B.length (hpad message)
	toHash = (toLazy . B.drop l . hpad) newm


--Return a list of all the words in our dictionary!
getWordbank :: IO [String]
getWordbank = lines <$> readFile "/usr/share/dict/words"

--select a random word from a list of words!
randomWord ws = newStdGen >>= return . fst . randomList ws

--Our oracle picks a random word. Then it gives us the tag (signature) for our message,
--as well as a function that takes a message/tag pair, sees if it is valid, and returns
--true only if it is both valid and the message indicates the person is an admin.
genOracle29 = do
	w <- wrdB <$> (getWordbank >>= randomWord)
	return ( sign w message29, (\m t -> verify w m t && test26 (strB m)) )

--Given a hash extension function, the tag from the previous hash, and our verifier function,
--we make a forged message/tag pair with our desired extension.
forge extendf tag verifier = (message, newtag, valid) where
	prefixes = [ B.replicate l 0 | l <- [0..100] ]
	extendeds = [(\(m,t) -> (B.drop (B.length p) m, t)) $ extendf (p `B.append` message29) tag extension29 | p <- prefixes ]
	(message, newtag) = fromJust $ find (\(m, t) -> verifier m t) extendeds
	valid = verifier message newtag

--Here we put it all together to solve the problem
solve29 = do
	(tag, verifier) <- genOracle29
	return $ forge extendHash tag verifier

--
--Problem 30
--

--Adding Show and Eq instances for our MD4 contexts so that we can use
--these as message tags.
instance Show M.Ctx where
	show ctx = to16 $ M.finalize ctx

instance Eq M.Ctx where
	ctx1 == ctx2 = M.finalize ctx1==M.finalize ctx2

--Sign a message using naive MD4 MAC.
sign2 k m = M.update M.init (k `B.append` m)

--Verify a message using naive MD4 MAC
verify2 k m t = t == sign2 k m

--Here is our extension algorithm for the naive MD4
extendHash2 message tag extension = (newm, M.update tag toHash) where
	newm = hpad message `B.append` extension
	l = B.length message
	toHash = B.drop l newm

--And our oracle is almost the same, but this time it uses MD4.
genOracle30 = do
	w <- wrdB <$> (getWordbank >>= randomWord)
	return ( sign2 w message29, (\m t -> verify2 w m t && test26 (strB m)) )

--And our solution returns the forged message/tag pair
solve30 = do
	(tag, verifier) <- genOracle30
	return $ forge extendHash2 tag verifier


--
--Problem 31
--

--Convert a SHA1State to a bytestring
state2BS :: SHA1State -> BString
state2BS state = B.concat $ map intToStr (fromState state) where

--More conventional SHA1 hash algorithm
sha1 :: BString -> BString
sha1 = state2BS . sha1' . toLazy

--Given a key of any length, returns a key with a suitable length for the
--SHA1 HMAC algorithm
properLen k = if l <= 64 then (k `B.append` B.replicate (64-l) 0) else sha1 k where
	l = B.length k

--HMAC using SHA1
hmac :: BString -> BString -> BString
hmac k m = sha1 (o_key_pad `B.append` sha1 (i_key_pad `B.append` m) ) where
	o_key_pad = B.replicate 64 0x5c `xorB` (properLen k)
	i_key_pad = B.replicate 64 0x36 `xorB` (properLen k)


--Given a file and its signature, gives us the appropriate URL
urlFor :: BString -> BString -> String
urlFor file signature = "http://localhost:8000/?file=" ++ (strB file) ++ "&signature=" ++ to16 signature

--Converts a time difference to a number, which represents the number
--of nanoseconds between the two times
timeToMicroS :: NominalDiffTime -> Int
timeToMicroS = truncate . (fromIntegral 10000000000 * ) . toRational

--Our oracle now takes a file and its putative signature, and returns
--the amount of time it took us to do our HTTP request, along with
--the HTTP response code.
oracle :: BString -> BString -> IO (Int, ResponseCode)
oracle file signature = do
	t1 <- getCurrentTime
	result <- simpleHTTP (getRequest (urlFor file signature))
	t2 <- getCurrentTime
	let dt = timeToMicroS (t2 `diffUTCTime` t1)
	return $ (dt, either (error "") rspCode result)
	
is500 :: ResponseCode -> Bool
is500 (5,0,0) = True
is500 (_,_,_) = False

--Our evil message that we would like to be able to sign with HMAC
message31 = wrdB "do-the-dastardly-deed"

--Given a prefix, tries appending all the bytes and querying the oracle.
tryAll prefix = sequence [ (\x -> ((prefix `B.snoc` c), x)) <$> oracle message31 (prefix `B.snoc` c) | c <- [0..255] ]

--This method takes a prefix known to be correct, and tries to use a timing attack
--to produce a correct MAC. It simply tries appending all of the different bytes,
--and it believes that the query that took the most amount of time was correct.
solveMessage prefix = do
	putStrLn (to16 prefix)
	results <- tryAll prefix
	let correct = find (not.is500.snd.snd) results
	if isJust correct
		then return $ (fst . fromJust) correct
		else solveMessage $ (fst . maximumBy (comparing (fst.snd))) results


--Our solution to problem 31
solve31 = solveMessage B.empty


--
--Problem 32
--

--Given a function f which takes a list and returns a number, and a threshold n,
--and a list xs, returns Just the element of xs which has evaluates to the maximum of the list
--under f, if that element leads the next best by n. Otherwise, returns Nothing.
clearLeader :: (Num b, Ord b) => (a -> b) -> b -> [a] -> Maybe a
clearLeader f n xs = if (f (sorted !! 0) - f (sorted !! 1)) > n then Just (head sorted) else Nothing where
	sorted = (reverse . sortBy (comparing f)) xs

--Given two lists of our full queries to the oracle, zips them together
--by adding the cumulative response time. This allows us to do some averaging, and get
-- a more correct answer.
addResults :: [(BString, (Int, ResponseCode))] -> [(BString, (Int, ResponseCode))] -> [(BString, (Int, ResponseCode))]
addResults = zipWith (\(a, (b, c)) (d, (e, f)) -> (a, (b+e, c)))


--Here's our new method to solve the message, where in this case, we keep querying bytes
--until we get results in which one byte clearly is better than the rest. Only once we know that
--do we assume that byte is correct and continue forwards
solveMessage2 :: BString -> IO BString
solveMessage2 prefix = do
	putStrLn (to16 prefix)
	results <- tryAll prefix
	let correct = find (not.is500.snd.snd) results
	if isJust correct
		then return $ (fst . fromJust) correct
		else goodResults 1 prefix results >>= solveMessage2

--Here's the critical part of solveMessage2 where we keep going until we have good results.
goodResults n prefix results = if (isJust leader) then (return . fst . fromJust) leader else elsecond where
	elsecond = goodResults (n+1) prefix . addResults results =<< tryAll prefix
	leader = clearLeader (fst.snd) (round $ (fromIntegral 50000000)*(sqrt (fromIntegral n))) results

--And here's our solution for problem 32.
solve32 = solveMessage2 B.empty
