module Crypto2 where
import Control.Applicative (liftA2)
import Data.Bits
import Data.List (maximumBy, sortBy, nub, find, findIndex, intercalate, isInfixOf)
import Data.List.Split (chunksOf, splitOn)
import Data.Ord (comparing)
import Data.Word (Word8)
import Data.Char (toUpper, toLower, chr, ord, isLetter)
import Data.Maybe (fromJust, catMaybes, isJust)
import Codec.Crypto.AES
import System.Random
import qualified Data.ByteString as B
import qualified Codec.Binary.Base16 as B16
import qualified Codec.Binary.Base64 as B64

type BString = B.ByteString


--Convert a Word8 to its ASCII character
chrB :: Word8 -> Char
chrB = chr.fromIntegral

--Convert an ASCII character to Word8
ordB :: Char -> Word8
ordB x | ord x > 255 = error "Character not ASCII"
ordB x | otherwise   = fromIntegral (ord x)


--Functions to encode and decode to Hex and base 64 in the proper format.
un16, un64 :: String -> [Word8]
un16 = fromJust . B16.decode . map toUpper
un64 = fromJust . B64.decode

to16, to64 :: [Word8] -> String
to16 = map toLower . B16.encode
to64 = B64.encode


maxWith f = maximumBy (comparing f)

fixedXOR = zipWith xor

singleXOR = fixedXOR . repeat


--Frequencies of the letters A through Z
letterFreq = [6.09,1.05,2.84,2.92,11.36,1.79,1.38,3.41,5.44,0.24,0.41,2.92,2.76,5.44,6.00,1.95,0.24,4.95,5.68,8.03,2.43,0.97,1.38,0.24,1.30,0.03]
--Frequency of the space character.
spaceFreq = 12.17
--Frequency of other punctuation marks
otherFreq = 6.57

--Convert our ASCII characters to their frequency
charFreq :: Word8 -> Double
charFreq x | x == 32         = spaceFreq
charFreq x | x>64 && x < 91  = letterFreq !! (fromIntegral x-65)
charFreq x | x>96 && x < 123 = letterFreq !! (fromIntegral x-97)
charFreq x | x>32 && x < 128 = otherFreq/10
charFreq x | x==10	     = otherFreq/10  --new line feed!
charFreq x | x < 32          = otherFreq/100 --weird stuff
charFreq x | otherwise       = 0


--Returns the logarithm of the probability (roughly speaking) that a random English string
--of a given length will be the string that is input.
logProbEnglish :: [Word8] -> Double
logProbEnglish = sum . map (log.charFreq)


--Returns the cipher that would result in the most probable English string
getSingleCipher :: [Word8] -> Word8
getSingleCipher str = maxWith (\x-> logProbEnglish (singleXOR x str)) [0..255]

--Decodes the ciphertext using getSingleCipher
decodeSingleCipher str = singleXOR (getSingleCipher str) str


stringXOR :: [Word8] -> [Word8] -> [Word8]
stringXOR key = fixedXOR (cycle key)
 
--Calculates the sum of the bits in a byte.
bitsum :: Integral a => Word8 -> a
bitsum 0 = 0
bitsum w = fromIntegral (w `mod` 2) + bitsum (shiftR w 1)

--Calculates the hamming distance between lists of bytes.
hamming :: [Word8] -> [Word8] -> Int
hamming x y = sum $ map bitsum $ fixedXOR x y

--Removes NewLine characters from a string
removeNL :: String -> String
removeNL ('\n':str) = removeNL str
removeNL    (c:str) = c : removeNL str
removeNL       []   = []

switchList :: [[a]] -> [[a]]
switchList ls = if null nls then [] else map head nls : switchList (map tail nls) where
	nls = filter (not.null) ls

getCipher :: Int -> [Word8] -> [Word8]
getCipher n str = map (getSingleCipher) (switchList (chunksOf n str))






--
--Problem 9
--

--Pads using PKCS#7 to n bytes
pad :: Int -> BString -> BString
pad n str = B.concat [str, B.replicate (n-B.length str) 4]

--Pads using PKCS#7 so that the byte length is amultiple of n
padmult :: Int -> BString -> BString
padmult n str = pad (n*((fst $ divMod (B.length str - 1) n)+1)) str

--Removes PKCS#7 padding
unpad :: BString -> BString
unpad = B.takeWhile (/=4)


--this gives the properly padded Yellow Submarine text
padded9 = pad 20 (B.pack $ map ordB "YELLOW SUBMARINE")

--
--Problem 10
--

--16 bytes of 0...
baseIV = B.pack $ replicate 16 0

--XOR two ByteStrings against each other
xorB :: BString -> BString -> BString
xorB x y = B.pack (B.zipWith xor x y)

--encrypt with AES in ECB mode
ecbEncrypt :: BString -> BString -> BString
ecbEncrypt key str = crypt' ECB key iv Encrypt (padmult 16 str) where
	iv = baseIV

--decrypt with AES in ECB mode
ecbDecrypt ::  BString -> BString -> BString
ecbDecrypt key str =  crypt' ECB key iv Decrypt str where
	iv = baseIV

--encrypt with AES in CBC mode
cbcEncrypt :: BString -> BString -> BString -> BString
cbcEncrypt key iv str | B.null str = B.empty
cbcEncrypt key iv str | otherwise  = fblock `B.append` cbcEncrypt key fblock (B.drop 16 str) where
	fblock = ecbEncrypt key (xorB (padmult 16 $ B.take 16 str) iv)


--decrypt with AES in CBC mode
cbcDecrypt :: BString -> BString -> BString -> BString
cbcDecrypt key iv str | B.null str = B.empty
cbcDecrypt key iv str | otherwise  = fblock `B.append` cbcDecrypt key (B.take 16 str) (B.drop 16 str) where
	fblock = xorB (ecbDecrypt key (B.take 16 str)) iv

--Properly decrypts the buffer
message10 :: IO String
message10 = readFile "p10.txt" >>= return . map chrB . B.unpack . cbcDecrypt key iv . B.pack . un64 . removeNL where
	key = B.pack (map ordB "YELLOW SUBMARINE")
	iv = baseIV

--
--Problem 11
--

--Gives a random seed to a function that asks for one
randomize :: (StdGen -> b) -> IO b
randomize f = newStdGen >>= return . f

--Creates a list of random characters of a given length, and a new random seed
randomL :: (RandomGen g, Random b) => Int -> g -> ([b], g)
randomL num rand = randomL' num ([],rand) where
	randomL' 0 (xs,r) = (xs,r)
	randomL' n (xs,r) = randomL' (n-1) ((first : xs), r2) where
		(first, r2) = random r

testkey = B.pack (map ordB "YELLOW SUBMARINE")


--The Oracle for Problem 11
oracle :: BString -> StdGen -> BString
oracle m r = func paddedm where
	(len1, r2) = randomR (5,10) r
	(padding1, r3) = randomL len1 r2
	(len2, r4) = randomR (5,10) r3
	(padding2, r5) = randomL len2 r4
	paddedm = B.concat [B.pack padding1, m, B.pack padding2]
	(ecb, r6) = random r5 :: (Bool, StdGen)
	(key, r7) = randomL 16 r6
	func = if ecb then ecbEncrypt (B.pack key) else cbcEncrypt (B.pack key) (B.pack $ fst $ randomL 16 r6)


--Detects whether two encrypted blocks are the same, meaning that 
ecbResult :: BString -> Bool
ecbResult c = (length . chunksOf 16 . B.unpack) c /= (length . nub. chunksOf 16 . B.unpack) c 

--Our adversary who says TRUE if the message was encrypted with ECB mode, and false otherwise.
adversary :: BString -> IO Bool
adversary m = randomize (oracle m) >>= return . ecbResult

--Statistical test to see if we do indeed say TRUE half the time...
--We expect to see about 5000 +/- 100
test11 :: IO Int
test11 = fmap (length . filter id) $ sequence $ map f[1..10000] where
	f = const $ adversary $ B.pack $ take 160 $ cycle $ map ordB "test"

--
--Problem 12
--

appendix = B.pack $ un64 "Um9sbGluJyBpbiBteSA1LjAKV2l0aCBteSByYWctdG9wIGRvd24gc28gbXkgaGFpciBjYW4gYmxvdwpUaGUgZ2lybGllcyBvbiBzdGFuZGJ5IHdhdmluZyBqdXN0IHRvIHNheSBoaQpEaWQgeW91IHN0b3A/IE5vLCBJIGp1c3QgZHJvdmUgYnkK"

type Oracle = BString -> BString

--Randomly generates an oracle for problem 12
genOracle :: StdGen -> Oracle
genOracle r m = ecbEncrypt (B.pack $ fst $ randomL 16 r) $ B.concat [m, appendix]

--Given a list of numbers that is eventually not constant, gives the first non-zero change from element to element.
firstDiff :: (Num a, Eq a) => [a] -> a
firstDiff [] = error "List must not be null"
firstDiff (x:xs) = fd x xs where
	fd y (x:xs) = if x==y then fd y xs else x-y

--This function determines the block size from any oracle
detectBlockSize :: Oracle -> Int
detectBlockSize o = firstDiff $ [ B.length ( o $ B.pack $ replicate x $ ordB 'A') |x <-[1..]]

--Changes the nth element of a list to a new value
replaceNth :: Int -> a -> [a] -> [a]
replaceNth 0 newVal (x:xs) = newVal:xs
replaceNth n newVal (x:xs) = x:replaceNth (n-1) newVal xs

--Changes the last element of a list to a new value
replaceLast :: a -> [a] -> [a]
replaceLast x [] = []
replaceLast x (y:[]) = [x]
replaceLast x (y:zs) = y:replaceLast x zs


--The following 3 functions do our byte-by-byte breakdown of ECB mode.
breakByte :: Oracle -> Int -> BString -> Maybe BString
breakByte o n str = fmap fst $ find (ecbResult.snd) list where
	list = [ (B.take 16 $ strsubbed c, o (strsubbed c) ) | c <- [0..255] ]
	strsubbed c = B.pack $ drop 1 (B.unpack str) ++ c:(replicate n (ordB 'A'))

breakBlock :: Oracle -> BString -> Maybe BString
breakBlock o init = foldr (\n str -> str >>= breakByte o n) (Just $ init) [0..15]

breakString :: Oracle -> BString
breakString o = B.concat $ map fromJust $ takeWhile isJust $ map str [1..] where 
	str 0 = Just $ B.pack $ replicate 16 (ordB 'A')
	str n = breakBlock o =<< (str (n-1))

--Our solution to problem #12!
solve12 :: IO BString
solve12 = randomize genOracle >>= return.breakString

--
--Problem 13
--

type Hash = [(String, String)]

profile_for :: String -> Hash
prfile_for s | '&' `elem` s || '=' `elem` s = error "Disallowed"
profile_for s = [("email", s), ("uid", "10"), ("role", "user")]


encodeHash :: Hash -> String
encodeHash h = intercalate "&" $ map (\(k,v)-> k++'=':v) h

--If a list has at least two elements, it converts the first two elements to a tuple
listToTuple :: [a] -> Maybe (a,a)
listToTuple (x:y:zs) = Just (x,y)
listToTuple [] = Nothing
listToTuple (_:[]) = Nothing

decodeHash :: String -> Hash
decodeHash s = catMaybes $ map ( listToTuple . splitOn "=") $ splitOn "&" s

--Our email address has just the right number of characters for this to work!
break_email = "johnny.counts.chars@gmail.com"
break_prefix = (replicate 10 (chrB 4)) ++ "admin" ++ (replicate 11 (chrB 4))

--Generates our oracle encryptor and decryptor algorithms for problem 13
genED :: StdGen -> ((String -> BString), (BString -> Hash))
genED r = (encryptor, decryptor)  where
	encryptor = ecbEncrypt key . B.pack . map ordB .  encodeHash . profile_for
	decryptor = decodeHash . map chrB . B.unpack . unpad . ecbDecrypt key
	key = (B.pack $ fst $ randomL 16 r)

--And here is our adversary who swiftly makes himself and administrator.
adminerator :: (String -> BString) -> (BString -> Hash) -> Hash
adminerator e d = d (B.pack $ concat swappedblocks) where
	adminchunk = (chunksOf 16 $ B.unpack $  e (break_prefix ++ break_email)) !! 1
	swappedblocks = replaceLast adminchunk (chunksOf 16 $ B.unpack $ e break_email)

--And here we see who wins problem 13... the adversary!
solve13 :: IO Hash
solve13 = do 
	(e,d) <- randomize genED
	return (adminerator e d)


--
--Problem 14
--

--Our oracle for problem 14
genOracle14 :: StdGen -> IO Oracle
genOracle14 r = do
	r2 <- newStdGen
	let (len, r3) = randomR (0,0) r2
	let prefix = B.pack $ fst $ randomL len r3
	return $ (\m -> ecbEncrypt (B.pack $ fst $ randomL 16 r) $ B.concat [ prefix, m, appendix])


--Our new strategy that takes into account the random padding
breakByte2 :: IO Oracle -> StdGen -> Int -> BString -> IO (Maybe Word8)
breakByte2 ogen r n str = do
	o <- ogen
	let c = o strsubbed
	if ecbResult c then return (Just char) else return Nothing where
		(char, r2) = randomR (0,254) r
		(length, r3) = randomR (0,15) r2
		replen = (16-n) `mod` 16
		strsubbed = B.pack $ replicate length 255 ++ drop 1 (B.unpack str) ++ char:(replicate replen (ordB 'A'))

tryByte2 :: IO Oracle -> Int -> BString -> Int -> IO (Maybe Word8)
tryByte2 ogen n str 0 = return Nothing
tryByte2 ogen n str m = do
	r <- newStdGen
	result <- breakByte2 ogen r n str
	if (isJust result) then return result else tryByte2 ogen n str (m-1)

breakString2 :: IO Oracle -> StdGen -> IO BString
breakString2 ogen r = fmap ( B.pack .  map (B.last . fromJust) . takeWhile isJust) $ sequence $ map str [1..] where
	str :: Int -> IO (Maybe BString)
	str 0 = return $ Just $ B.pack $ replicate 16 (ordB 'A')
	str n = do 
		prev <- str (n-1)
		char <- if isJust prev then tryByte2 ogen n (fromJust prev) (2^16) else return Nothing
		return $ if isJust char 
			then Just $ (B.drop 1 (fromJust prev)) `B.append` B.singleton (fromJust char)
			else Nothing

--And here's our solution... Unfortunately, everything's probabilistic, and I have a time cutoff
--to keep it from running forever, so sometimes it fails.
solve14 :: IO BString
solve14 = do
	ogen <- randomize genOracle14
	newStdGen >>= breakString2 ogen


--
--Problem 15
--


--Unpads PKCS#7 padding if it is valid; otherwise, returns Nothing.
validunpad :: BString -> Maybe BString
validunpad s = if valid then Just (B.takeWhile (not.pred) s) else Nothing where
	pred x = x/=10 && (x<32 || x>128)
	valid = ending == B.filter (==4) ending
	ending = (B.takeWhile pred . B.reverse) s


--The following three check that we indeed check padding properly.
res15a = validunpad $ B.pack $ map ordB $ "ICE ICE BABY\x04\x04\x04\x04"
res15b = validunpad $ B.pack $ map ordB $ "ICE ICE BABY\x05\x05\x05\x05"
res15c = validunpad $ B.pack $ map ordB $ "ICE ICE BABY\x01\x02\x03\x04"


--
--Problem 16
--


prepend6 =  "comment1=cooking%20MCs;userdata=" --length 32
append6 =   ";comment2=%20like%20a%20pound%20of%20bacon" --length 42

--Here's how CBC encoding and decoding is done in practice. We simply transmit the IV
--at the beginning of the ciphertext.
cbcEIV key iv str = iv `B.append` cbcEncrypt key iv str
cbcDIV key str = cbcDecrypt key (B.take 16 str) (B.drop 16 str)

--Generates our two oracle functions. One encrypts, while the other tests to see if the user is an administrator.
genET :: StdGen -> (IO (String -> BString), (BString -> Bool))
genET r = (encryptor, tester)  where
	encryptor = do r<-newStdGen; return $ cbcEIV key (B.pack $ fst $ randomL 16 r) . B.pack . map ordB . addstuff
	tester = test16 . map chrB . B.unpack . unpad . cbcDIV key
	key = (B.pack $ fst $ randomL 16 r)

test16 :: String -> Bool
test16 = isInfixOf ";admin=true;"

safeMap :: Char -> String
safeMap '=' = "\"=\""
safeMap '&' = "\"&\""
safeMap  c = [c]

addstuff :: String -> String
addstuff s = prepend6 ++ concatMap safeMap s ++ append6


--And here's where our strategy will come in.
insides = B.pack $ map ordB ";admin=true;----"

toXOR = insides `xorB` (B.pack $ map ordB $ take 16 $ drop 16 $ addstuff "")

modCipherText :: BString -> BString
modCipherText c = B.take 16 c `B.append` block `B.append` B.drop 32 c where
	center = (B.take 16 (B.drop 16 c))
	block = center `xorB`toXOR

--Here's our answer to problem #16
solve16 = do
	(encryptor, tester) <- randomize genET
	enc <- encryptor
	let c = enc ""
	return $ tester (modCipherText c)
