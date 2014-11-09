module Crypto3 where
import Control.Applicative ((<$>))
import Data.Bits
import Data.List (maximumBy, sortBy, nub, find, findIndex, intercalate, isInfixOf)
import Data.List.Split (chunksOf, splitOn)
import Data.Ord (comparing)
import Data.Word (Word8)
import Data.Char (toUpper, toLower, chr, ord, isLetter)
import Data.Maybe (fromJust, catMaybes, isJust)
import Codec.Crypto.AES
import Control.Concurrent (threadDelay)
import System.Random
import Data.Serialize
import Data.Int (Int16, Int32)
import Data.UnixTime (getUnixTime, utSeconds)
import qualified Data.ByteString as B
import qualified Codec.Binary.Base16 as B16
import qualified Codec.Binary.Base64 as B64

type BString = B.ByteString


--
--Useful functions
--

--Convert a Word8 to its ASCII character
chrB :: Word8 -> Char
chrB = chr.fromIntegral

strB = map chrB . B.unpack

--Convert an ASCII character to Word8
ordB :: Char -> Word8
ordB x | ord x > 255 = error "Character not ASCII"
ordB x | otherwise   = fromIntegral (ord x)

wrdB = B.pack . map ordB

--Functions to encode and decode to Hex and base 64 in the proper format.
un16, un64 :: String -> [Word8]
un16 = fromJust . B16.decode . map toUpper
un64 = fromJust . B64.decode

to16, to64 :: [Word8] -> String
to16 = map toLower . B16.encode
to64 = B64.encode


fixedXOR = zipWith xor

singleXOR = fixedXOR . repeat

stringXOR :: [Word8] -> [Word8] -> [Word8]
stringXOR key = fixedXOR (cycle key)

onlyIf :: a -> Bool -> Maybe a
value `onlyIf` condition = if condition then Just value else Nothing

--PKCS#5 padding
pad :: BString -> BString
pad m = m `B.append` B.replicate l (fromIntegral l) where
	l =  16 - snd (B.length m `divMod` 16)

--returns unpadded string, if the PKCS#5 padding was valid
vunpad :: BString -> Maybe BString
vunpad m = B.take (l-n) m `onlyIf` pred where
	n = fromIntegral (B.last m)
	l = B.length m
	pred = n<=l && n>0 && ( and $ map (==fromIntegral n) $ B.unpack $ (B.drop (l-n) m) )


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

--Gives a random seed to a function that asks for one
randomize :: (StdGen -> b) -> IO b
randomize f = f <$> newStdGen

--Creates a list of random characters of a given length, and a new random seed
randomL :: (RandomGen g, Random b) => Int -> g -> ([b], g)
randomL num rand = randomL' num ([],rand) where
	randomL' 0 (xs,r) = (xs,r)
	randomL' n (xs,r) = randomL' (n-1) ((first : xs), r2) where
		(first, r2) = random r

randomList :: RandomGen g => [a] -> g -> (a, g)
randomList xs r = (xs !! val, r2) where
	(val, r2) = randomR (0, length xs-1) r

--Changes the nth element of a list to a new value
replaceNth :: Int -> a -> [a] -> [a]
replaceNth 0 newVal (x:xs) = newVal:xs
replaceNth n newVal (x:xs) = x:replaceNth (n-1) newVal xs

--Changes the last element of a list to a new value
replaceLast :: a -> [a] -> [a]
replaceLast x [] = []
replaceLast x (y:[]) = [x]
replaceLast x (y:zs) = y:replaceLast x zs


--Calculates the sum of the bits in a byte.
bitsum :: Integral a => Word8 -> a
bitsum 0 = 0
bitsum w = fromIntegral (w `mod` 2) + bitsum (shiftR w 1)

--Calculates the hamming distance between lists of bytes.
hamming :: BString -> BString -> Int
hamming x y = sum $ map bitsum $ B.unpack $ x `xorB` y

bytify f = B.pack . f . B.unpack

randomKey :: RandomGen g => g -> (BString, g)
randomKey r = (\(k,r) -> (B.pack k, r))$ randomL 16 r







--
--Problem 17
--

--Possible messages for this problem
messages = map wrdB ["MDAwMDAwTm93IHRoYXQgdGhlIHBhcnR5IGlzIGp1bXBpbmc=",
	"MDAwMDAxV2l0aCB0aGUgYmFzcyBraWNrZWQgaW4gYW5kIHRoZSBWZWdhJ3MgYXJlIHB1bXBpbic=",
	"MDAwMDAyUXVpY2sgdG8gdGhlIHBvaW50LCB0byB0aGUgcG9pbnQsIG5vIGZha2luZw==",
	"MDAwMDAzQ29va2luZyBNQydzIGxpa2UgYSBwb3VuZCBvZiBiYWNvbg==",
	"MDAwMDA0QnVybmluZyAnZW0sIGlmIHlvdSBhaW4ndCBxdWljayBhbmQgbmltYmxl",
	"MDAwMDA1SSBnbyBjcmF6eSB3aGVuIEkgaGVhciBhIGN5bWJhbA==",
	"MDAwMDA2QW5kIGEgaGlnaCBoYXQgd2l0aCBhIHNvdXBlZCB1cCB0ZW1wbw==",
	"MDAwMDA3SSdtIG9uIGEgcm9sbCwgaXQncyB0aW1lIHRvIGdvIHNvbG8=",
	"MDAwMDA4b2xsaW4nIGluIG15IGZpdmUgcG9pbnQgb2g=",
	"MDAwMDA5aXRoIG15IHJhZy10b3AgZG93biBzbyBteSBoYWlyIGNhbiBibG93"]


type Oracle17 = (BString , BString -> Bool, BString -> Bool)

--The oracle consists of the ciphertext, a validator that will decrypt arbitrary
--ciphertexts and say whether or not they have valid padding, and a validator
--that will indicate if I've figured out the message properly
genOracle17 :: StdGen -> Oracle17
genOracle17 r = (ciphertext, decryptvalidator, validator) where
	(key, r2) = randomKey r
	(iv, r3) = randomKey r2
	message = fst $ randomList messages r3
	ciphertext = cbcEIV key iv message
	decryptvalidator = isJust . cbcDIVU key
	validator m = isJust $ (m==) <$> cbcDIVU key message 


--This function discovers the answer using the padding attack. It will fail
--with probability of something near 1/128 (in the unlikely event that we randomly
--get proper paddings of extra length, but that's okay
solve17 :: Oracle17 -> Bool
solve17 (c, dv, v) = isJust $ v <$> vunpad answer where
	chunks = chunksB 16 c
	brokenblocks = map (breakBlock dv c) [1..length chunks-1]
	answer = B.concat [ b `xorB` B.replicate 16 16 | b <- zipWith xorB brokenblocks chunks ]


breakBlock :: (BString -> Bool) -> BString -> Int -> BString
breakBlock dv c k = prev 16 where
	chunks = chunksB 16 c
	replaced bs = B.concat (replaceNth (k-1) bs (take (k+1) chunks))
	string 0 = B.replicate 16 0
	string n = (prev n) `xorB` mod where
		mod = B.replicate (16-n) 0 `B.append` B.replicate n (fromIntegral n `xor` fromIntegral (n+1))
	strings = map string [0..]
	prev n = head $ filter (dv.replaced) [ bytify (replaceNth (16-n) c) (strings !! (n-1)) | c<-[0..255]] 


--This returns true almost all the time, showing we solved this problem correctly
answer17 = solve17 <$> randomize genOracle17



--
--Problem 18
--

--"Increment" a bytestring, thinking of it as a large integer
increment :: BString -> BString
increment str | B.null str       = B.empty
increment str | B.last str ==255 = increment (B.init str) `B.append` B.singleton 0
increment str | otherwise        = B.init str `B.append` B.singleton (B.last str+1)

--intToStr :: Int -> BString
intToStr n | n < 256 = B.singleton (fromIntegral n)
intToStr n | otherwise = (fromIntegral remainder) `B.cons` intToStr quot where
	(quot, remainder) = n `divMod` 256

--intToStr8 :: Int -> BString
intToStr8 n = m `B.append` B.replicate (8-l) 0  where
	m = B.take 8 $ intToStr n
	l = B.length m


--Encrypt using AES CTR mode
ctrEncrypt :: BString -> BString -> BString -> BString
ctrEncrypt key nonce m = ecbEncrypt key encrstring `xorB` m where
	numblocks = fst ((B.length m-1) `divMod` 16) + 1
	encrstring = B.concat $ map (\n -> nonce `B.append` intToStr8 n) [0..numblocks-1]

--Decrypting with AES CTR mode is the same as encrypting
ctrDecrypt = ctrEncrypt

--Here is our ciphertext for problem 18
ciphertext18 = B.pack $ un64 "L77na/nrFsKvynd6HzOoG7GHTLXsTVu9qvY/2syLXzhPweyyMTJULu/6/kXX0KSvoOLSFQ=="

--And here we correctly
message18 = ctrDecrypt (wrdB "YELLOW SUBMARINE") (intToStr8 0) ciphertext18


--
--Problem 19
--


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

--Our oracle here just returns a list of all the ciphertexts
genOracle19 :: IO [BString]
genOracle19 = do 
	r <- newStdGen; 
	file <- readFile "p19.txt"
	let encryptor = ctrEncrypt (fst $ randomKey r) (intToStr8 0)
	let ciphertexts = map (encryptor . B.pack . un64) . lines $ file
	return ciphertexts

--This function tries to decode a list of ciphertexts against a given stream
trystream :: [BString] -> BString -> [String]
trystream cts str = map (strB . xorB str) cts

--This function prints the trystream results, so they're easier to visualize
puttrystream cts str = mapM_ putStrLn (trystream cts str)

--This function suggests what the most probable character of the stream is at the nth position
suggest :: [BString] -> Int -> [Word8]
suggest cts n = take 10 $ sortBy (comparing f) [0..255] where
	f c = 0- (logProbEnglish $ map (xor c . flip B.index n) cts)

--This function takes the ciphertexts from the oracle, and returns what it thinks
--is the stream that it was encrypted against
breakcts :: [BString] -> BString
breakcts cts = B.pack $ map (head . suggest cts) [0..l-1] where
	l = (minimum $ map B.length cts)


--And here's our answer, where we'll output the messages we think we got!
answer19 = do cts <- genOracle19; puttrystream cts (breakcts cts)


--
--Problem 20
--

--Here are our ciphertexts to break this time
ciphertexts20 :: IO [BString]
ciphertexts20 = map (B.pack . un64) . lines <$> readFile "p20.txt"

--And here's our answer for problem 20!
answer20 = do cts <- ciphertexts20; puttrystream cts (breakcts cts)


--
--Problem 21
--

--the type MTState holds our state information for the encryptor
type MTState = ([Int32], Int)
initState = (0, replicate 624 0)


initialize_generator :: Int32 -> MTState
initialize_generator seed = (mts,0) where
	mts = map mt [0..623]
	mt 0 = seed
	mt n = (1812433253 * ( (mts !! (n-1)) `xor` shiftR ( (mts !! (n-1))) 30) + fromIntegral n)::Int32


xorShiftR k v mask = v `xor` ( (shiftR v k) .&. mask )
xorShiftL k v mask = v `xor` ( (shiftL v k) .&. mask )

temper :: Int32 -> Int32
temper = (\(a,b,c,d,e) -> e) . temper'

--temper' :: Int -> Int
temper' y1 = (y1,y2,y3,y4,y5) where
	y2 = xorShiftR 11 y1 (complement (0::Int32))
	y3 = xorShiftL 7  y2 (2636928640::Int32)
	y4 = xorShiftL 15 y3 (4022730752::Int32)
	y5 = xorShiftR 18 y4 (complement (0::Int32))

--This is the function that gets the next pseudo-random number from the generator,
--and returns the modified state
extract_number :: MTState -> (Int32, MTState)
extract_number (mts, idx) = (y, (newmts, newidx)) where
	newidx = (idx + 1) `mod` 624
	newmts = if idx==0 then fst (regenerate (mts,idx)) else mts
	y = temper $ newmts !! idx

--One step in the algorithm to regenerate the array
regenerate_step :: Int -> MTState -> MTState
regenerate_step i (mts,idx) = (replaceNth i newval mts, idx) where
	y = (bit 31 .&. (mts !! i)) .|. ( complement (bit 31) .&. (mts !! ((i+1) `mod` 624)) )
	possval = ( mts !! (((i+397) `mod` 624)) ) `xor` shiftR y 30
	newval = if even y then possval else (possval `xor` 2567483615)

--Here we compose all the steps together for the regeneration algorithm, which we run every 624 times
--we ask for a random number
regenerate :: MTState -> MTState
regenerate = foldr1 (.) $ map regenerate_step [623,622..0]

--This function just takes a sequence of actions using MTStates and compiles together the results.
--I'm sure there's a monad for this...
seque :: [s -> (a, s)] -> ([a], s) -> ([a], s)
seque []     (as, state) = (as, state)
seque (f:fs) (as, state) = (\(a, s) -> seque fs (as++[a], s)) $ f state

--And here's 624 random numbers from a very boringly-chosen seed.
nums = fst $ seque (replicate 624 extract_number) $ ([], initialize_generator 1)


--
--Problem 22
--


--Given a seed, we get the first random number from that PRNG
firstrand :: Int32 -> Int32
firstrand seed = fst $ extract_number $ initialize_generator seed

--This just gives us a seed from the current time
timeSeed :: Num a => IO a
timeSeed = fromIntegral . fromEnum . utSeconds <$> getUnixTime

--Our oracle, which returns the first random number that it generated from its seed,
--and a validator that will tell us if the seed we guess is correct.
oracle22 :: IO (Int32, Int32 -> Bool)
oracle22 = do
	r <- newStdGen
	let (wait,r2) = randomR (40*10^6,100*10^6) r
	let wait2 = fst (randomR (40*10^6,100*10^6) r2)
	() <- threadDelay wait
	seed <- timeSeed
	() <- threadDelay wait2
	return (firstrand seed, (seed==))

--Here I take our oracle, and I find the seed the generated the number.
break22 :: (Int32, Int32 -> Bool) -> IO (Maybe Int32)
break22 (rand, validator) = do
	time <- getUnixTime
	let timeint = fromIntegral $ fromEnum (utSeconds time)	
	let list = [timeint-2^8..timeint+2^8] 
	return ( fst <$> ( find ((rand==).snd) $ map (\x -> (x, firstrand x)) list ))

--And here I put it together. Generate a random oracle, find the seed,
--and probe the oracle to prove that I'm correct!
solve22 = do
	(r, v) <- oracle22
	ans <- break22 (r, v)
	return (v <$> ans)


--
--Problem 23
--

--Inverse of the tempering function
untemper :: Int32 -> Int32
untemper = (\(a,b,c,d,e) -> a) . untemper'

untemper' y5 = (y1,y2,y3,y4,y5) where
	y4 = y5 `xor` (shiftR y5 18)
	y3 = unxorShiftL 15 y4 (4022730752::Int32)
	y2 = unxorShiftL 7  y3 (2636928640::Int32)
	y1 = unxorShiftR 11 y2 (complement (0::Int32))


--Composes a function with itself n times
pow :: Int -> (a -> a) -> a -> a
pow 0 f = id
pow n f = f . (pow (n-1) f)

--Inverts our xorShift with masks
unxorShiftR n v mask = (pow 32 fun) v where
	fun x = v `xor` ( (shiftR x n) .&. mask)

unxorShiftL n v mask = (pow 32 fun) v where
	fun x = v `xor` ( (shiftL x n) .&. mask)


--Generates a putative state of our PRNG, given a list of exactly 624 outputs
generate_prng :: [Int32] -> MTState
generate_prng outputs = (map untemper outputs, 0)

--Tells us if two PRNG states will produce the same random numbers
compare_prng :: MTState -> MTState -> Bool
compare_prng (mt1, idx1) (mt2, idx2) = idx1==idx2 && map temper mt1==map temper mt2

--And here's our test, which returns true, showing that I can recover the state of the PRNG
problem23test = do
	r <- randomIO
	let (output, state) = seque (replicate 624 extract_number) $ ([], initialize_generator r)
	let recoveredstate = generate_prng output
	return $ compare_prng state recoveredstate

--
--Problem 24
--

--Generate a bytestream of length n bytes from our PRNG
mtStream :: Int16 -> Int -> BString
mtStream key n = B.concat $ map encode output where
	(output, state) = seque (replicate n extract_number) $ ([], initialize_generator (fromIntegral key))
	
--Encrypt using our PRNG's bytstream, using CTR mode
mtEncrypt :: Int16 -> BString -> BString
mtEncrypt key m = m `xorB` mtStream key n where
	n = (fst $ (B.length m) `divMod` 4)+1

--Decryption is the same as encryption
mtDecrypt = mtEncrypt

--The secret that I want to convey. Fortunately, I know that multiple layers of
--cryptography work best. You don't know what this is code for...
secret24 = wrdB "The eagle flies at midnight!"


--Our oracle packs 5 to 10 random characters before our secret, and then encrypts
--using our PRNG's stream cipher under a random key. All it gives us is the ciphertext
oracle24 :: IO BString
oracle24 = do 
	key <- randomIO;
	length <- randomRIO (5,10)
	r <- newStdGen
	let prefix = fst (randomL length r)
	return $ mtEncrypt key (B.pack prefix `B.append` secret24)

--The key is only 16 bits! I'm patient enough to try 'em all...
break24 :: BString -> Maybe Int16
break24 c = find f [-32768..32767] where
	f key = isJust $ secret24 `B.findSubstring` (mtDecrypt key c)

--And here's our answer; here we can recover the key, since we know
--the message and the ciphertext, and recovered the key by brute force.
answer24 = break24 <$> oracle24

--Generates a password-reset token using the current time as the seed for our PRNG.
--It restricts output to only decent ASCII characters (33-96).
password_reset :: IO BString
password_reset = B.map ((+33).(`mod` 64)) . (\key -> mtStream key 32) <$> timeSeed

--If we have a recent password reset token, we can do the same trick as we did in a previous question
--to just try time seeds from around now, and see if any match
was_password_seeded :: BString -> IO Bool
was_password_seeded c = do
	seed <- timeSeed
	let list = [seed-2^8..seed+2^8]
	return $ isJust $ find (==c) $ [ B.map ((+33).(`mod` 64)) $ mtStream key 32 | key <- list ]

--And here we check to see if our password-reset token that we generated with the PRNG
--was indeed generated with the PRNG. Fortunately this returns True, as desired.
checkpwseeded = password_reset >>= was_password_seeded
