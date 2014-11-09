module Main where
import Control.Applicative ((<$>),(<*>))
import Data.Bits
import Data.Char (toUpper, toLower, chr, ord, isLetter)
import Data.List (find, sort, sortBy, dropWhile)
import Data.List.Split (chunksOf)
import Data.Maybe (fromJust, isJust, catMaybes)
import Data.Ratio ((%))
import Data.Word (Word8)
import System.Random
import qualified Codec.Binary.Base16 as B16
import qualified Codec.Binary.Base64 as B64
import qualified Crypto.Hash.SHA256 as H (hash)
import qualified Crypto.Hash.SHA1 as H1 (hash)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as B (fromChunks, toChunks)

import Debug.Trace


type BString = B.ByteString


--
--Useful functions
--

--Convert a Word8 to its ASCII character
chrB :: Word8 -> Char
chrB = chr.fromIntegral

strB = map chrB . B.unpack


--Convert between lazy and strict bytestrings
lazy = B.fromChunks . (:[])
strict = B.concat . B.toChunks


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


--Break a bytestring into chunks of size n
chunksB :: Int -> BString -> [BString]
chunksB n bs | B.null bs = []
chunksB n bs | otherwise = B.take n bs : chunksB n (B.drop n bs)



--16 bytes of 0...
baseIV = B.replicate 16 0

--XOR two ByteStrings against each other
xorB :: BString -> BString -> BString
xorB x y = B.pack (B.zipWith xor x y)

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
--Number theory/RSA related-functions
--

type RSAKey = (Integer, Integer)

--Generate a random number mod p
randomMod :: (RandomGen g, Integral i, Random i) => i -> g -> (i, g)
randomMod p r = randomR (0,p-1) r


--Convert a bytestring to an integer
strToInt str | B.length str == 1 = fromIntegral (B.last str)
strToInt str | otherwise         = fromIntegral (B.last str) + 256*(strToInt (B.init str))

--Convert an integer to a variable-length bytestring
intToStr n | n < 256 = B.singleton (fromIntegral n)
intToStr n | otherwise = intToStr quot `B.snoc` (fromIntegral remainder) where
	(quot, remainder) = n `divMod` 256


--Perform a binary function f in the ring Z/p
--modd f p x y = ((x `mod` p) `f` (y `mod` p)) `mod` p


--Efficiently calculate a^b (mod p)
pow :: (Integral a, Integral b) => a -> a -> b -> a
pow p a b | b==0      = 1
pow p a b | otherwise = ( (if k==1 then a' else 1) * (pow p a2 n) ) `mod` p where
	(n, k) = b `divMod` 2
	a' = a `mod` p
	a2 = (a' * a') `mod` p

--Generate an n-bit number that is probably prime; I saw someone call these
--"industrial grade" primes!
industrialPrime :: Int -> StdGen -> (Integer, StdGen)
industrialPrime n r = if probablyPrime p then (p,r2) else industrialPrime n r2 where
	(p, r2) = randomR (2^(n-1), 2^n - 1) r

--Given an integer, we detect whether it's probably prime by using the probabilistic converse
--of Fermat's Little Theorem.
probablyPrime :: Integer -> Bool
probablyPrime p = and . map ((==1) . flip (pow p) (p-1) ) . filter (<p) $ [2,3,5,7]


-- Extended Euclidean algorithm.  Given non-negative a and b, return x, y and g
-- such that ax + by = g, where g = gcd(a,b).  Note that x or y may be negative.
gcdExt a 0 = (1, 0, a)
gcdExt a b = let (q, r) = a `quotRem` b
                 (s, t, g) = gcdExt b r
             in (t, s - q * t, g)
 
-- Given a and m, return Just x such that ax = 1 mod m.  If there is no such x
-- return Nothing.
modInv a m = let (i, _, g) = gcdExt a m
             in if g == 1 then Just (mkPos i) else Nothing
  where mkPos x = if x < 0 then x + m else x


--Generate an RSA key pair using primes of size k bits
genRSA :: Int -> StdGen -> (RSAKey, RSAKey)
genRSA k r = (case maybed of Just d -> ((e,n), (d,n)); Nothing -> genRSA k r3 ) where
	(p, r2) = industrialPrime k r
	(q, r3) = industrialPrime k r2
	n = p*q
	et = (p-1)*(q-1)
	e = 3
	maybed = modInv e et

--RSA functions
rsaApply, rsaInvert :: RSAKey -> Integer -> Integer
rsaApply  (e, n) m = pow n m e
rsaInvert = rsaApply

--Convert a function on integers to one on bytestrings
bytify :: (Integer -> Integer) -> BString -> BString
bytify f = intToStr . f . strToInt

--Convert a function on bytestrings to one on integers
intify :: (BString -> BString) -> Integer -> Integer
intify f = strToInt . f . intToStr

--Bytified versions of RSA application and inversion. Note that this is NOT a secure
--public key encryption scheme
rsaEncrypt pub = bytify (rsaApply pub)
rsaDecrypt priv = bytify (rsaInvert priv)






--
--Problem 41
--

secret41 = wrdB "Execute Plan C!"

--Our oracle randomly generates a 320-bit RSA key and encrypts secret41 under the key.
--It gives us the ciphertext, the public key, and a function which will decrypt any
--message except the ciphertext.
genOracle41 :: StdGen -> (RSAKey, BString, BString -> Maybe BString)
genOracle41 r = (pub,ctxt, decryptor) where
	(pub, priv) = genRSA 160 r
	ctxt = rsaEncrypt pub secret41
	decryptor c = if c==ctxt then Nothing else Just (rsaDecrypt priv c)

--Here we take any oracle, and run a randomize algorithm that implements the attack
--described in the email to discover the plaintext
attacker41 :: (RSAKey, BString, BString -> Maybe BString) -> StdGen -> Maybe BString
attacker41 ((e, n), ctxt, decryptor) r = p where
	s = (+2) . fst . randomMod (n-2) $ r
	c' = ((pow n s e) * (strToInt ctxt)) `mod` n
	p =  bytify (`mod` n) <$> ( (bytify . (*) <$> (modInv s n)) <*> decryptor (intToStr c') )

--And here we implement the attack.
break41 = do
	oracle <- randomize genOracle41
	randomize $ attacker41 oracle


--
--Problem 42
--

--Computes the ceiling of log_b (number). I needed this because we don't have an
--arbitrary-precision integer logarithm without this.
lgBase :: Integer -> Integer -> Int
lgBase b number = byteLength' 1 (abs number) where
	byteLength' k n = case n `quot` b of 0 -> k; n' -> byteLength' (k+1) n'

--Determine how many bits or bytes an integer will occupy as a bytestring
bitLength, byteLength :: Integer -> Int
bitLength = lgBase 2
byteLength = lgBase 256

--Implement a version of the PKCS1.5 hashing
padHash :: Integer -> BString -> BString
padHash n tag = B.concat [ B.pack [0,1], ffs, B.singleton 0, tag] where
	ffs = B.replicate len 255
	len = byteLength n - 3 - B.length tag

--Sign a message using RSA encryption of the padded hash of the message
sign (d, n) m = (m, rsaDecrypt (d,n) . padHash n . H.hash $ m)

--Our "BROKEN" verify function
verify (e, n) (m,t) = (case hash2 of Just h -> h==hash1; Nothing -> False) where
	paddedhash = rsaEncrypt (e,n) t
	hash2 = B.take 32 <$> parsePadding paddedhash
	hash1 = H.hash m

--If the padding is valid, returns Just the unpadded value. Otherwise, returns Nothing.	
parsePadding :: BString -> Maybe BString
parsePadding =  fmap (B.pack) . parsePadding' False . B.unpack

--Our state machine for parsing the padding. The system has two states, encoded with
--True/False.
parsePadding' :: Bool -> [Word8] -> Maybe [Word8]
parsePadding' False (w:ws) = if w==1 then parsePadding' True ws else Nothing
parsePadding' True  (w:ws) = case w of 
	0         -> Just ws
	255       -> parsePadding' True ws
	otherwise -> Nothing
parsePadding' _ [] = Nothing

--Given an RSA public key and a message we would like to sign, returns the message
--with a valid tag by computing a cube root. This ONLY works if e==3. This forged tag
--will only verify with verifiers which do not ensure that the hash value is right-aligned.
forgeMessage :: RSAKey -> BString -> (BString, BString)
forgeMessage (3, n) m = (m,tag) where
	hsh = H.hash m
	vague = B.pack [1,255,0] `B.append` hsh `B.append` B.replicate padlen 180
	padlen = byteLength n - B.length hsh - 3
	tag = bytify cuberoot vague


--Generate a sequence of values approaching the cube root of y, starting with our approximate
--guess x0. Uses the Newton-Raphson method.
newton_cubert :: Fractional a => a -> a -> [a]
newton_cubert y x0 = x1 : (newton_cubert y x1) where
	x1 = (1/3) * ( 2*x0 + y/(x0*x0) )

--Looks at a sequence of values, and takes a value once the difference between subsequent
--values in the sequence becomes less than eps.
converge_to :: (Num a, Ord a) => a-> [a] -> a
converge_to eps [] = error "Empty list"
converge_to eps [x] = x
converge_to eps (x:y:zs) = if abs (x-y)<eps then y else converge_to eps (y:zs)

--Given a cubic integer, calculates the (integral) cube root. This needs to be exact, so it uses
--exact rational numbers in the Newton-Raphson method. It takes a LONG time to converge for very large numbers!
--Unfortunately, I think this is a fact of life. Newton's method has quadratic convergence, but our numbers
--grow exponentially with bitsize, so the cube root takes O ( 2^(n/2)) time to compute, I believe.
cuberoot :: Integer -> Integer
cuberoot y =  round . converge_to (1/2) $ newton_cubert (fromIntegral y) start where
	start = round (fromIntegral y**(1/3)) % 1


--Implement the entire attack. Generate an RSA keypair, and then forge a signature
--of the message "hi mom" using only the public key. We then verify that our verifier function
--accepts this signed message.
break42 = do
	(pub, _) <- randomize $ genRSA 512
	let taggedm = forgeMessage pub (wrdB "hi mom")
	print taggedm
	return (verify pub taggedm)


--
--Problem 43
--

pDSA = strToInt $ un16 "800000000000000089e1855218a0e7dac38136ffafa72eda7859f2171e25e65eac698c1702578b07dc2a1076da241c76c62d374d8389ea5aeffd3226a0530cc565f3bf6b50929139ebeac04f48c3c84afb796d61e5a4f9a8fda812ab59494232c7d2b4deb50aa18ee9e132bfa85ac4374d7f9091abc3d015efc871a584471bb1"

qDSA = strToInt $ un16 "f4f47f05794b256174bba6e9b396a7707e563c5b"

gDSA = strToInt $ un16 "5958c9d3898b224b12672c0b98e06c60df923cb8bc999d119458fef538b8fa4046c8db53039db620c094c9fa077ef389b5322a559946a71903f990f1f7e0e025e2d7f7cf494aff1a0470f5b64c36b625a097f1651fe775323556fe00b3608c887892878480e99041be601a62166ca6894bdd41a7054ec89f756ba9fc95302291"

type DSATaggedM = (BString, (Integer, Integer))

--Generate a DSA public/private keypair with g as the generator (using values pDSA, qDSA)
genDSAG :: Integer -> StdGen -> (Integer, Integer)
genDSAG g r = (y, x) where
	(x, _) = randomR (1, qDSA-1) r
	y = pow pDSA g x

--Sign a message m using generator g, private key x (randomized algorithm)
signDSAG :: Integer -> Integer -> BString -> StdGen -> DSATaggedM
signDSAG g x m rand = (case signDSAG' g x k m of Just tm -> tm; Nothing -> signDSAG g x m rand2) where
	(k, rand2) = randomR (1, qDSA-1) rand
	taggedm = signDSAG' g x k m

--Sign a message m using generator g, private key x, and nonce k. If k is a suitable nonce,
--we return Just the signature; otherwise, we return Nothing.
signDSAG' :: Integer -> Integer -> Integer -> BString -> Maybe DSATaggedM
signDSAG' g x k m = if isJust s then Just (m,(r, fromJust s)) else Nothing where
	hsh = strToInt (H1.hash m) `mod` qDSA
	r = (pow pDSA g k) `mod` qDSA
	s = (`mod` qDSA) . (((hsh + x*r) `mod` qDSA)*) <$> modInv k qDSA
	--cond = case s of Just s' -> r/=0 && s'/=0; Nothing -> False
	
--Verify a signed message with the DSA standard, given generator g and public key y.
verifyDSAG :: Integer -> Integer -> DSATaggedM -> Bool
verifyDSAG g y (m, (r,s)) = v==r where
	cond1 = r>0 && r<qDSA && s>0 && s<qDSA
	w = fromJust $ modInv s qDSA
	hsh = strToInt (H1.hash m) `mod` qDSA
	u1 = (hsh * w) `mod` qDSA
	u2 = (r * w) `mod` qDSA
	v = (((pow pDSA g u1) * (pow pDSA y u2)) `mod` pDSA) `mod` qDSA


--Versions of the DSA function with generator g fixed as gDSA.
genDSA = genDSAG gDSA
signDSA = signDSAG gDSA
signDSA' = signDSAG' gDSA 
verifyDSA = verifyDSAG gDSA


--We do a test to make sure our DSA algorithms are consistent
testDSA :: IO Bool
testDSA = do
	(pub, priv) <- randomize genDSA
	taggedm <- randomize $ signDSA priv secret41
	return (verifyDSA pub taggedm)


--If we somehow know the nonce, we use this to recover the private key x
--from a signed message.
recoverPrivKey :: Integer -> DSATaggedM -> Maybe Integer
recoverPrivKey k (m, (r,s)) = (`mod` qDSA) . (num *) <$> denom where
	hsh = strToInt (H1.hash m) `mod` qDSA
	num = (s*k - hsh) `mod` qDSA
	denom = modInv r qDSA

--This only returns the recovered private key if it is actually correct.
correctPrivKey :: Integer -> Integer -> DSATaggedM -> Maybe Integer
correctPrivKey y k tm = do
	x <- recoverPrivKey k tm 
	let y' = pow pDSA gDSA x
	if y==y' then Just x else Nothing



y43 = 0x84ad4719d044495496a3201c8ff484feb45b962e7302e56a392aee4abab3e4bdebf2955b4736012f21a08084056b19bcd7fee56048e004e44984e2f411788efdc837a0d2e5abb7b555039fd243ac01f0fb2ed1dec568280ce678e931868d23eb095fde9d3779191b8c0299d6e07bbb283e6633451e535c45513b2d33c99ea17

m43 = wrdB "For those that envy a MC it can be hazardous to your health\nSo be friendly, a matter of life and death, just like a etch-a-sketch\n"

r43 = 548099063082341131477253921760299949438196259240 :: Integer
s43 = 857042759984254168557880549501802188789837994940 :: Integer

--Given a public key and a tagged message, return the nonce used to encrypt the message,
--as well as the private key.
breakPrivKey :: Integer -> DSATaggedM -> (Integer, Integer)
breakPrivKey pub taggedm = head $ catMaybes [ (\y-> (k,y)) <$> x k | k<-[0..2^16] ] where
	x k = correctPrivKey pub k taggedm


--Our nonce and private key for problem 43.
(k43, x43) = breakPrivKey y43 (m43, (r43, s43)) 

--Here we confirm that our private key is indeed the one given in the email.
hashofx43 = to16 . H1.hash . wrdB . to16 . intToStr $ x43


--
--Problem 44
--

y44 = 0x2d026f4bf30195ede3a088da85e398ef869611d0f68f0713d51c9c1a3a26c95105d915e2d8cdf26d056b86b8a7b85519b1c23cc3ecdc6062650462e3063bd179c2a6581519f674a61f1d89a1fff27171ebc1b93d4dc57bceb7ae2430f98a6a4d83d8279ee65d71c1203d2c96d65ebbf7cce9d32971c3de5084cce04a2e147821

--Given a list of elements, return a list of all distinct (unordered) pairs of elements
pairsOf :: [a] -> [(a,a)]
pairsOf [] = []
pairsOf (x:xs) = map (\y -> (x,y)) xs ++ pairsOf xs

--Load the text file with the signed messages and get it into a format I like.
taggedms44 :: IO [DSATaggedM]
taggedms44 = do
	list <- chunksOf 4 . map (tail . dropWhile (/=' ')) . lines <$> readFile "p44.txt"
	return . map (\(m:s:r:_:[]) -> (wrdB m, (read r :: Integer,read s :: Integer)) ) $ list

--Given a pair of messages that were encrypted with the same nonce, recover the k value.
kFromNonces :: (DSATaggedM, DSATaggedM) -> Maybe Integer
kFromNonces ( (m1, (_,s1)) , (m2, (_, s2)) ) = (`mod` qDSA) . (num *) <$> denom where
	denom = modInv ((s1 - s2) `mod` qDSA) qDSA
	hsh = strToInt . H1.hash
	num = (hsh m1 - hsh m2) `mod` qDSA

--Run the repeated nonce attack. Given the public key, a list of tagged messages, this will
--return the private key IF any two of the messages shared the same nonce. Otherwise, it 
--may have undefined behavior.
repeatedNonce :: Integer -> [DSATaggedM] -> Integer
repeatedNonce y taggedms = head $ catMaybes [ flip (correctPrivKey y) tm1 =<< kFromNonces (tm1,tm2) | (tm1,tm2) <- pairsOf taggedms ]

--Our private key for problem 44
x44 = repeatedNonce y44 <$> taggedms44

--The hash of the private key, which confirms I got the right key.
hashofx44 = to16 . H1.hash . wrdB . to16 . intToStr <$> x44



--
--Problem 45
--

secret45 = wrdB "There's no combination of words I could put on the back of a postcard"

--This just shows that if we choose g=0, then any message will validate as long as r=0.
break45a = do
	(pub, priv) <- randomize $ genDSAG 0
	taggedm <- randomize $ signDSAG 0 priv secret45
	print taggedm
	print $ verifyDSAG 0 pub taggedm
	let taggedm1 = (wrdB "Jibberish!", (0, 123456789))
	print taggedm1
	print $ verifyDSAG 0 pub taggedm1

--Given a public key, we sign a message under the corresponding PRIVATE key without knowing it,
--IF the generator is 1 mod p.
magicSign :: Integer -> BString -> StdGen -> DSATaggedM
magicSign y m rand = (case s of Just s' -> (m,(r,s')); Nothing -> magicSign y m rand2) where
	(z, rand2) = randomR (0, qDSA-1) rand
	r = (pow pDSA y z) `mod` qDSA
	s = (`mod` qDSA) . (r *) <$> modInv z qDSA

--This just shows that our magic signing algorithm can sign any message we'd like.
break45b = do
	(pub, priv) <- randomize $ genDSAG (pDSA+1)
	hw <- randomize $ magicSign pub (wrdB "Hello, world")
	print hw
	print $ verifyDSAG (pDSA+1) pub hw
	gw <- randomize $ magicSign pub (wrdB "Goodbye, world")
	print gw
	print $ verifyDSAG (pDSA+1) pub gw


--
--Problem 46
--

secret46 = un64 "VGhhdCdzIHdoeSBJIGZvdW5kIHlvdSBkb24ndCBwbGF5IGFyb3VuZCB3aXRoIHRoZSBGdW5reSBDb2xkIE1lZGluYQ=="

--Generate an oracle for problem 46. Generate an RSA keypair, and tell us
--the public key, the encrypted message, and a function which tells us whether
--any ciphertext represents an even plaintext or not.
genOracle46 :: StdGen -> (RSAKey, BString -> Bool, BString)
genOracle46 r = (pub, isEven, c) where
	(pub, priv) = genRSA 512 r
	c = rsaEncrypt pub secret46
	isEven = even . strToInt . rsaDecrypt priv

--Run 1 step of the attack. We multiply our plaintext by 2, and see if the result is even
--or not, allowing us to restrict our bounds to either the lower or upper half of those bounds.
attackBounds :: RSAKey -> (BString -> Bool) -> (Integer, Rational, Rational) -> (Integer, Rational, Rational)
attackBounds (e, n) isEven (cur,l,h) = (cur',l',h') where
	cur' = (pow n 2 e * cur) `mod` n
	iseven = isEven (intToStr cur')
	halfrange = (h-l) / 2
	l' = if iseven then l else l + halfrange
	h' = if iseven then h - halfrange else h

--Iterate our attackBounds step until we have a single message left. Oh, and output
--those upper bounds so we get the "Hollywood"-style decryption-while-you-wait (cool!).
doAttack :: (RSAKey, (BString -> Bool), BString) -> IO BString
doAttack (pub,isEven,cipher) = run (strToInt cipher, li, hi) where
	step (c,l,h) = print (intToStr (round h)) >> return (attackBounds pub isEven (c,l,h))
	li = 0
	hi = (snd pub - 1) % 1
	run (c,l,h) = if h-l<=1 then return (intToStr $ (round h)) else (step (c,l,h) >>= run)


--Run the attack for problem 46
break46 = do
	oracle <- randomize genOracle46
	doAttack oracle

--
--Problem 47
--

--The type for our padding oracle for problems 47 and 48, where we do the Bleichenbacher attack.
--The oracle has an RSA public key, a function that tells us whether the plaintext of any
--ciphertext is properly padded, and the ciphertext of the secret message (conveniently in numeric form).
type OracleBB = (RSAKey, Integer -> Bool, Integer)

--Our secret for problems 47 and 48
secretBB = wrdB "kick it, CC"

--Our oracle generator for problems 47 and 48.
genOracleBB :: BString -> Int -> StdGen -> OracleBB
genOracleBB secret k r = (pub, isConformant, c) where
	(pub@(e,n), priv) = genRSA (k `quot` 2) r
	c = rsaApply pub . strToInt $ message
	message = B.concat [ B.singleton 2, B.replicate l 255, B.singleton 0, secret]
	l = byteLength n - 3 - B.length secret
	bB = 2^(8*(byteLength n - 2))
	isConformant = pkcsConformant' bB . rsaInvert priv


pkcsConformant' :: Integer -> Integer -> Bool
pkcsConformant' bB c = c>= 2*bB && c < 3*bB

pkcsConformant :: BString -> Bool
pkcsConformant m = and [c1,c2,c3] where
	c1 = B.head m == 2
	c2 = and . map (/=0) . B.unpack . B.take 8 . B.drop 1 $ m
	c3 = or . map (==0) . B.unpack . B.drop 9 $ m


--Okay, now we make a datatype for single intervals (Interval), 
--as well as unions of intervals (Intervals). The Intervals
--datatype has the ASSUMPTION that no intervals in the list overlap
--and that the intervals are sorted from low to high.
type Interval = (Integer, Integer)
type Intervals = [Interval]

-- i <==> j == True iff i and j overlap
(<==>) :: Interval -> Interval -> Ordering
(a,b) <==> (x,y) = 
	if b < x then LT else (if y < a then GT else EQ)

--Compute the union of two intervals, as an Intervals.
union :: Interval -> Interval -> Intervals
(a,b) `union` (x,y) = case (a,b) <==> (x,y) of
	EQ -> [(min a x, max b y)]
	LT -> [(a,b),(x,y)]
	GT -> [(x,y),(a,b)]

--Tells us whether an interval is valid.
ivalid :: Interval -> Bool
ivalid (a,b) = a <= b

--Computes the union of a union of intervals with one more interval.
aunion :: Intervals -> Interval -> Intervals
aunion ints tounion = aunion' ints tounion [] where
	aunion' (i:is) j list = case j <==> i of
		LT -> reverse list++(j:i:is)
		EQ -> aunion' is (head (union i j)) list
		GT -> aunion' is j (i:list)
	aunion' [] j list = reverse (j:list)

--Compute the union of two unions of intervals
sunion :: Intervals -> Intervals -> Intervals
sunion is = foldl aunion is

--Compute the union of a list of intervals
iunion :: [Interval] -> Intervals
iunion = foldr sunion [] . map (:[]) 

--Tells us the the base-2 logarithm of the number of possible
--integers in our union of intervals.
intervalssize :: Intervals -> Int
intervalssize is = bitLength $ sum [ b - a | (a,b) <- is ]



--The following are the steps of the Bleichenbacher attack.


step2a :: OracleBB -> Integer -> Integer
step2a ((e,n), isConformant, _) c0 = fromJust . find f $ [start..] where
	start = ceiling (n % (3*bB))
	bB = 2^(8*(byteLength n - 2))
	f = isConformant . (`mod` n) . (c0 *) . flip (pow n) e


step2, step2b, step2c :: OracleBB -> Integer -> Integer -> Intervals -> Integer
step2 o c0 sim mim = (if null (tail mim) then step2c else step2b) o c0 sim mim


step2b o@((e,n), isConformant, _) c0 sim mim = valids where
	start = sim+1
	modwith = (`mod` n) . (c0 *) . flip (pow n) e
	valids = fromJust $ find (isConformant . modwith) [start..]

step2c o@((e,n), isConformant, _) c0 sim [(a,b)] = valids where
	lowr = ceiling $ 2*(b*sim-2*bB) % n
	lows  r = ceiling $ (2*bB + r*n) % b
	highs r = floor $ ((3*bB-1 + r*n) % a) + 1
	bB = 2^(8*(byteLength n - 2))
	modwith = (`mod` n) . (c0 *) . flip (pow n) e
	list = [ s | r <- [lowr..] , s <- [lows r..highs r] ]
	valids = fromJust $ find (isConformant . modwith) list

step3 :: OracleBB -> Integer -> Intervals -> Intervals
step3 ((e,n), _, _) si mim = iunion $ filter ivalid intervals where
	lowr (a,b) = ceiling $ (a*si-3*bB+1) % n
	highr (a,b) = floor $ (b*si - 2*bB) % n + 1
	low (a,b,r) = max a $ ceiling ( (2*bB + r*n) % si )
	high (a,b,r) = min b $ floor ( (3*bB - 1 + r*n) % si )
	intervals = [ (low (a,b,r), high (a,b,r)) | (a,b) <- mim, r <- [lowr (a,b)..highr(a,b)] ]
	bB = 2^(8*(byteLength n - 2))


--This iterates steps 2b,c and 3 over and over again
iteration :: OracleBB -> (Integer, Intervals) -> (Integer, Intervals)
iteration o@(_, _, c)  (sim, mim) | trace (show (length mim) ++ ", " ++ show (intervalssize mim)) False = undefined
iteration o@(_, _, c)  (sim, mim) = (si, step3 o si mim) where
	si = (step2 o c sim mim)

--Here is our concluding step
step4 :: [(Integer, Intervals)] -> Integer
step4 ((_, ints):ys) = 
	if null (tail ints) && fst (head ints) == snd (head ints)
		then fst (head ints) else step4 ys
step4 [] = error "We never got a valid answer!"


--Run the Bleichenbacher attack on any padding oracle.
solveBB :: OracleBB -> BString
solveBB o@((e,n), isConformant, c) = intToStr . step4 $ iterate (iteration o) (s1,m1) where
	s1 = step2a o c
	m1 = step3 o s1 m0
	bB = 2^(8*(byteLength n - 2))
	m0 = [(2*bB, 3*bB-1)]


--Run the Bleichenbacher attack for problem 47.
break47 = solveBB <$> randomize (genOracleBB secretBB 256)

--
--Problem 48
--

--The Bleichenbacher attack with the larger modulus for problem 48.
break48 = solveBB <$> randomize (genOracleBB secretBB 768)




main = break47 >>= print
