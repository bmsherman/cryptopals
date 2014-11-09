module Crypto5 where
import Codec.Crypto.AES (crypt', Mode( CBC ), Direction( Encrypt, Decrypt ))
import Crypto.Hash.SHA1 as H1 (hash)
import qualified Crypto.Hash.SHA256 as H256 (hash)
import qualified Crypto.Hash as H (hash, hmac, SHA256, HMAC, HashFunctionBS)
import Control.Applicative ((<$>))
import Data.Binary (Binary, encode, decode)
import Data.Bits
import Data.Byteable (toBytes)
import Data.Char (toUpper, toLower, chr, ord, isLetter)
import Data.List (intercalate, find)
import Data.Word (Word8)
import Data.Maybe (fromJust)
import Data.Ratio ((%), Ratio)
import GHC.TypeLits
import System.Random
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as B (fromChunks, toChunks)
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



--
--Problem 33
--

--Perform a binary function f in the ring Z/p
modd f p x y = ((x `mod` p) `f` (y `mod` p)) `mod` p


--Efficiently calculate a^b (mod p)
pow :: (Integral a, Integral b) => a -> a -> b -> a
pow p a b | b==0      = 1
pow p a b | otherwise = (if k==1 then a else 1) >* (pow p (a >* a) n) where
	(n, k) = b `divMod` 2
	(>*) = (*) `modd` p


--Given a prime p, "generator" g, and secret key sk, return the corresponding public
--key for the DH secret key
publicKey p g sk = pow p g sk

--Given a prime p, the public key of the other person pk, and our own secret key sk,
--return a session key that is shared between the two parties
sessionKey p pk sk = pow p pk sk

--Generate random DH secret/public key pairs
generateKeys p g = do
	a <- fst <$> randomize (randomMod p)
	return (a, publicKey p g a)



p33a = 37 :: Integer
g33a = 5

pn = strToInt . un16 $ "ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca237327ffffffffffffffff" :: Integer
gn = 2


--In this example, two different parties generate DH public/secret keypairs. This function
--returns the pair of the session keys that each party generates using his own secret key
--and the other's public key. We see that it generates the same session key, fortunately!
example33 = do
	(sk1, pk1) <- generateKeys pn gn
	(sk2, pk2) <- generateKeys pn gn
	return (sessionKey pn pk1 sk2, sessionKey pn pk2 sk1)


--
--Problem 34
--


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


--Encrypt using AES-CBC (no paddding implemented)
cbcEncrypt k m r = (crypt' CBC k iv Encrypt m, iv) where
	iv = (fst $ randomKey 16 r)

--Decrypt using AES-CBC (no padding implemented)
cbcDecrypt k (c, iv) = crypt' CBC k iv Decrypt c

--AES-CBC encryption and decryption, where we send along the IV with the ciphertext,
--and we also add proper padding while encrypting and check for proper padding while decrypting.
cbcE k m r = cbcEncrypt k (pad m) r
cbcD k (c, iv) = fromJust . vunpad $ cbcDecrypt k (c, iv)

--Generate a 16-byte bytestring from any binary data, such as an Integer. 
keyFrom :: (Binary n) => n -> BString
keyFrom = B.take 16 . H1.hash . strict . encode


--Display message m as being sent from f, to t
dm f t m = putStrLn . concat $ [f,"->",t,"\t",m,"\n"]

--Print a string with an extra newline
printm = putStrLn . (++"\n")

--Method to display an encrypted message
showEnc (c, iv) = "Encrypted message: " ++ show (to16 c, to16 iv)


--Send message m through protocol
protocol m = do
	let (p,g) = (pn,gn)
        (skA, pkA) <- generateKeys p g
	dm "A" "B" (concat ["p: ", show p, ", g: ", show g, ", A: ", show pkA])
	(skB, pkB) <- generateKeys p g
	dm "B" "A" ("B: " ++ show pkB)
	let kAb = keyFrom $ sessionKey p pkB skA
	cA <- randomize (cbcE kAb m)
	dm "A" "B" (showEnc cA)
	let kaB = keyFrom $ sessionKey p pkA skB
	let mB = cbcD kaB cA
	cB <- randomize (cbcE kaB mB)
	dm "B" "A" (showEnc cB)


--Here we show the same protocol, but with a man in the middle.
--We output to the screen the things that M can decrypt.
mitmprotocol m = do
	let (p,g) = (pn,gn)
        (skA, pkA) <- generateKeys p g
	dm "A" "M" (concat ["p: ", show p, ", g: ", show g, ", A: ", show pkA])
        let pkM = p
	dm "M" "B" (concat ["p: ", show p, ", g: ", show g, ", A: ", show pkM])
	(skB, pkB) <- generateKeys p g
	dm "B" "M" ("B: " ++ show pkB)
	dm "M" "A" (concat ["B: ", show pkM])

	let kAM = keyFrom $ sessionKey p pkM skA
	cAM <- randomize (cbcE kAM m)
	dm "A" "M" (showEnc cAM )

	let kM = keyFrom (0::Integer)
	printm ("M sees: " ++ show (cbcD kM cAM))

	dm "M" "B" (showEnc cAM )

	let kBM = keyFrom $ sessionKey p pkM skB
	let mB = cbcD kBM cAM
	cBM <- randomize (cbcE kBM m)

	dm "B" "M" (showEnc cBM )

	printm ("M sees: " ++ show (cbcD kM cBM))



--
--Problem 35
--

--Here's our standard protocol for this problem.
protocol35 m = do
	let (p,g) = (pn,gn)
	dm "A" "B" (concat ["p: ", show p, ", g: ", show g])
	dm "B" "A" "Okay!"

        (skA, pkA) <- generateKeys p g
	dm "A" "B" ("A: " ++ show pkA)

	(skB, pkB) <- generateKeys p g
	dm "B" "A" ("B: " ++ show pkB)

	let kAB = keyFrom $ sessionKey p pkB skA
	cA <- randomize (cbcE kAB m)
	dm "A" "B" (showEnc cA)

	let kBA = keyFrom $ sessionKey p pkA skB
	let mB = cbcD kBA cA
	cB <- randomize (cbcE kBA mB)
	dm "B" "A" (showEnc cB)


--And here's what a man in the middle can do.
mitmprotocol35 :: Integer -> BString -> IO ()
mitmprotocol35 g m = do
	let p = pn
	dm "A" "M" (concat ["p: ", show p, ", g: ", show g])
	dm "M" "A" "Okay!"
	dm "M" "B" (concat ["p: ", show p, ", g: ", show g])
	dm "B" "M" "Okay!"

        (skA, pkA) <- generateKeys p g
	dm "A" "M" ("A: " ++ show pkA)
	(skMA, pkMA) <- generateKeys p g
	dm "M" "B" ("A: " ++ show pkMA)

	(skB, pkB) <- generateKeys p g
	dm "B" "M" ("B: " ++ show pkB)
	(skMB, pkMB) <- generateKeys p g
	dm "M" "A" ("B: " ++ show pkMB)

	let kAM = keyFrom $ sessionKey p pkMB skA
	cA <- randomize (cbcE kAM m)
	dm "A" "M" (showEnc cA )

	let kMA = keyFrom $ sessionKey p pkA skMB
	let kMB = keyFrom $ sessionKey p pkB skMA

	let mAM = cbcD kMA cA
	printm ("M sees: " ++ show mAM)
	cMB <- randomize (cbcE kMB mAM)
	dm "M" "B" (showEnc cMB)

	let kBM = keyFrom $ sessionKey p pkMA skB
	let mB = cbcD kBM cMB
	cBM <- randomize (cbcE kBM mB)
	dm "B" "M" (showEnc cBM)

	let mBM = cbcD kMB cBM
	printm ("M sees: " ++ show mBM)
	cMA <- randomize (cbcE kMA mBM)
	dm "M" "A" (showEnc cMA)

secretmessage = wrdB "How dare we speak of the laws of chance? Is not chance the antithesis of all law?"


--This executes the man-in-the-middle attack three times, each with a different value of g: 1, p, and p-1
doMITMdifferentGs = sequence_ $ map (\g -> putStrLn ("g: " ++ show g) >> mitmprotocol35 g secretmessage) [1,pn,pn-1]


--When g=1, we are assured that our session key g^(a*b) = 1
--When g=p, really we mean that g=0 (mod p). And so as long as a and b
--are both nonzero, then g^(a*b) = 0.
--When g=p-1, really we mean g=-1 (mod p). Therefore we are assured
--that the session key g^(a*b) is either 1 or (-1) mod p, since
--in this case g is of order 2.



--
--Problem 36
--

--SHAH-256 HMAC function that works with the datatypes we like
hmac' :: BString -> BString -> BString
hmac' k m = toBytes (H.hmac (H.hash :: H.HashFunctionBS H.SHA256) 256 k m)

--Generate an instance of our server for the secure remote password.
genServer :: BString -> BString -> StdGen -> (BString, Integer, Integer -> BString -> Bool)
genServer email pass r = (salt, bB, validator) where
	(salt, r2) = randomKey 16 r
	(b, _) = randomMod bN r2
	bN = pn
	g = 2
	k = 3
	xH = H256.hash (salt `B.append` pass)
	x = toInt xH
	v = pow' g x
	bB = (k >* v + pow' g b) `mod` bN
	uH bA = H256.hash ((toBS bA) `B.append` (toBS bB))
	u =  toInt . uH
	bS bA = pow' (bA >* pow' v (u bA)) b
	bK bA = H256.hash . toBS $ bS bA
	hmactag bA = hmac' (bK bA) salt
	validator bA = (hmactag bA==)
	(>*) = (*) `modd` bN
	pow' = pow bN
	toBS = intToStr
	toInt = strToInt

--Given the information the server has sent, and an email/password we'd like to try,
--we generate a client. We return whether the server accepted our information (True) or not (False).
genClient :: BString -> BString -> (BString, Integer, Integer -> BString -> Bool) -> StdGen -> Bool
genClient email pass (salt, bB, validator) r = valid where
	bN = pn
	g = 2
	k = 3
	(a, _) = randomMod bN r
	bA = pow' g a
	uH = H256.hash ((toBS bA) `B.append` (toBS bB))
	u = toInt uH
	xH = H256.hash (salt `B.append` pass)
	x = toInt xH
	bS = pow' (bB - (k >* (pow' g x))) (a+(u>*x))
	bK = H256.hash (toBS bS)
	hmactag = hmac' bK salt
	valid = validator bA hmactag

	(>*) = (*) `modd` bN
	pow' = pow bN
	toBS = intToStr
	toInt = strToInt

--Here we just do a sample run of the SRP protocol. Since client returns True,
--we see that our client is able to connect when he has the proper password.
test36 = do
	let password = wrdB "abcd1234"
	let email = wrdB "joe@aol.com"
	oracle <- randomize $ genServer email password
	client <- randomize $ genClient email password oracle
	return client



--
--Problem 37
--

--Our attacker acts like a client, but sends A=0 (which should be impossible if
--he generated the A value honestly, since it's an exponential). This means
--that the server ends up computing S=0.

--Of course, we can choose any A=0 (mod N), and we'd be okay. So our attacker
--chooses a value n to set A=n*N. For any n, we have A=0 (mod N)
attacker :: BString -> Integer -> (BString, Integer, Integer -> BString -> Bool) -> Bool
attacker email n (salt, bB, validator) = valid where
	bN = pn
	bA = n*bN :: Integer
	bS = 0 :: Integer
	bK = H256.hash (toBS bS)
	hmactag = hmac' bK salt
	valid = validator bA hmactag

	(>*) = (*) `modd` bN
	pow' = pow bN
	toBS = intToStr
	toInt = strToInt

--For a given little n, we successfully login (since it returns True) using a bogus
--A value.
break37 n = do
	let email = wrdB "joe@aol.com"
	let password = wrdB "superdupersecure"
	oracle <- randomize $ genServer email password
	return $ attacker email n oracle

--Here we use several bogus A values: 0, N, 2*N, ..., 10*N.
--And it works every time :).
break37all = sequence $ map break37 [0..10]


--
--Problem 38
--


--Here's a valid server with the simplified SRP.
genServer38 pass r = ((salt, u, bB), validator) where
	bN = pn
	g = 2
	pow' = pow bN
	(>*) = (*) `modd` bN
	(salt, r2) = randomKey 16 r
	(b, r3) = randomMod bN r2
	u = fst $ randomR (2^127, 2^128-1) r :: Integer
	x = strToInt $ H256.hash (salt `B.append` pass)
	v = pow' g x
	bB = pow' g b
	bS bA = pow' (bA >* pow' v u) b
	bK bA = H256.hash . intToStr $ bS bA
	hmactag bA = hmac' (bK bA) salt
	validator (bA,tag) = hmactag bA==tag

--And here's an honest ol' client for the simplified SRP
genClient38 pass (salt, u, bB) r = (bA, hmactag) where
	bN = pn
	g = 2
	pow' = pow bN
	(>*) = (*) `modd` bN
	(a, _) = randomMod bN r
	bA = pow' g a
	x = strToInt $ H256.hash (salt `B.append` pass)
	v = pow' g x
	bS = pow' bB (a + u >* x)
	bK = H256.hash . intToStr $ bS
	hmactag = hmac' bK salt

--Here is our attacker which impersonates the client.
attacker38 dictionary = ((salt, u, bB), cracker) where
	bN = pn
	g = 2
	pow' = pow bN
	salt = wrdB ""
	(>*) = (*) `modd` bN
	u = 1 :: Integer
	b = 1
	bB = pow' g b
	f :: Integer -> BString -> BString
	f bA pass =
	    let x pass = strToInt . H256.hash $ pass
		v x = pow' g x
		bS bA v = pow' (bA >* pow' v u) b
		bK bS = H256.hash $ intToStr bS
		tagfor bK = hmac' bK salt
	     in tagfor . bK . bS bA . v . x $ pass
	cracker (bA,tag) = dictionaryAttack (f bA) dictionary tag

--This just shows that our standard simplified SRP protocol works
--with a valid server and client.
correct38 = do
	let password = wrdB "superdupersecure"
	(server, validator) <- randomize $ genServer38 password
	client <- randomize $ genClient38 password server
	return (validator client)


--Return a list of all the words in our dictionary!
getWordbank :: IO [BString]
getWordbank = map wrdB . lines <$> readFile "/usr/share/dict/words"

--Generic dictionary attack
dictionaryAttack :: Eq b => (a -> b) -> [a] -> b -> Maybe a
dictionaryAttack f xs y = find ((y==).f) xs

--Here, we are using our computer's dictionary as our dictionary.
--Fortunately, the client's password is in the dictionary (and it's
--early on so I can save some CPU cycles!) We set up our fake server,
--and give our information to the client. The client then gives us
--his A value and his HMAC tag, which we promptly feed into our 'cracker'
--function, which runs the dictionary attack. And we recover the password!
attack38 = do
	let pass = wrdB "Aetobatidae"
	wordbank <- getWordbank
	let (fakeServer, cracker) = attacker38 wordbank
	clientInfo <- randomize $ genClient38 pass fakeServer
	return (cracker clientInfo)



--
--Problem 39
--

--Generate an n-byte number that is probably prime; I saw someone call these
--"industrial grade" primes!
industrialPrime :: Int -> StdGen -> (Integer, StdGen)
industrialPrime n r = if probablyPrime p then (p,r2) else industrialPrime n r2 where
	(p, r2) = randomR (2^(8*(n-1)), 2^(8*n)-1) r

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


--Generate an RSA key pair using primes of size k bytes
genRSA :: Int -> StdGen -> ((Integer, Integer), (Integer, Integer))
genRSA k r = (case maybed of Just d -> ((e,n), (d,n)); Nothing -> genRSA k r3 ) where
	(p, r2) = industrialPrime k r
	(q, r3) = industrialPrime k r2
	n = p*q
	et = (p-1)*(q-1)
	e = 3
	maybed = modInv e et


--Encrypt a message using an RSA public key
rsaEncrypt :: (Integer, Integer) -> BString -> BString
rsaEncrypt (e, n) m = intToStr $ pow n (strToInt m) e

--Decrypt a message using an RSA private key
rsaDecrypt :: (Integer, Integer) -> BString -> BString
rsaDecrypt (d, n) c = intToStr $ pow n (strToInt c) d


--Here we do a simple test that we can encrypt and decrypt using our RSA encryption algorithm
example39 = do
	(public, private) <- randomize (genRSA 50)
	let c = rsaEncrypt public secretmessage
	return $ rsaDecrypt private c


--
--Problem 40
--

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

--Given a list [(c_i,n_i)] of required congruences of the form x=c_i (mod n_i), we solve for the unique
--x modulo (product [n_i]) such that this holds for all i. Gauss' algorithm for the Chinese Remainder Theorem
gauss :: [(Integer, Integer)] -> Integer
gauss list = (`mod` bN) . sum $ [ let ni=(bN `quot` n) in c*ni*fromJust (modInv ni n) | (c,n) <- list] where
	bN = product . snd . unzip $ list	

--Given a cubic integer, calculates the (integral) cube root. This needs to be exact, so it uses
--exact rational numbers in the Newton-Raphson method. It takes a LONG time to converge for very large numbers!
--Unfortunately, I think this is a fact of life. Newton's method has quadratic convergence, but our numbers
--grow exponentially with bitsize, so the cube root takes O ( 2^(n/2)) time to compute, I believe.
cuberoot :: Integer -> Integer
cuberoot y =  round . converge_to (1/2) $ newton_cubert (fromIntegral y) start where
	start = round (fromIntegral y**(1/3)) % 1

--We can't compute the cube root for numbers that get too big, so we need a short message to encode.
short_secret = wrdB "Rook to E6"

--Our oracle generates an public/private RSA keypair, and tells us his public key,
--along with the encryption of his short_secret.
oracle :: IO ((Integer, Integer), BString)
oracle = do
	(public, private) <- randomize (genRSA 20)
	return (public, rsaEncrypt public short_secret)

--And we decrypt the short_secret, without knowing the public key, using the method we were told.
break40 = do
	list <- sequence $ replicate 3 probe
	let res = gauss list
	return . intToStr . cuberoot . gauss $ list
	where
	probe = do ((_,n), c) <- oracle; return (strToInt c,n)
