module Crypto1 where
import Data.Bits
import Data.List (maximumBy, sortBy, nub, findIndex)
import Data.List.Split (chunksOf)
import Data.Ord (comparing)
import Data.Word (Word8)
import Data.Char (toUpper, toLower, chr, ord, isLetter)
import Data.Maybe (fromJust)
import Codec.Crypto.AES
import qualified Data.ByteString as B
import qualified Codec.Binary.Base16 as B16
import qualified Codec.Binary.Base64 as B64


--Convert a Word8 to its ASCII character
chrB :: Word8 -> Char
chrB = chr.fromIntegral

--Convert an ASCII character to Word8
ordB :: Char -> Word8
ordB x | ord x > 255 = error "Character not ASCII"
ordB x | otherwise   = fromIntegral (ord x)

maxWith f = maximumBy (comparing f)

--
--Problem 1
--

str116 = "49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d"

str164 = "SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t"

--Functions to encode and decode to Hex and base 64 in the proper format.
un16, un64 :: String -> [Word8]
un16 = fromJust . B16.decode . map toUpper
un64 = fromJust . B64.decode

to16, to64 :: [Word8] -> String
to16 = map toLower . B16.encode
to64 = B64.encode

--These tests show that these encoding mechanisms work on the test case.
test1a = (to64.un16) str116 == str164
test1b = (to16.un64) str164 == str116

--Problem 2

b2a = un16 "1c0111001f010100061a024b53535009181c"
b2b = un16 "686974207468652062756c6c277320657965"
b2c = un16 "746865206b696420646f6e277420706c6179"

fixedXOR = zipWith xor

--This test shows that our fixedXOR function works.
test2 = fixedXOR b2a b2b == b2c

--Problem 3

--function to XOR against a single repeated character
singleXOR = fixedXOR . repeat

str3 = un16 "1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736"


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


--Our answer to problem 3!
key3 = chrB $ getSingleCipher str3
message3 = map chrB $ decodeSingleCipher str3


--
--Problem 4
--

allResults4 = readFile "p4.txt" >>= return . map (decodeSingleCipher.un16) . lines

--Our answer to problem 4!
message4 = allResults4 >>= return . map chrB . maxWith logProbEnglish

--
--Problem 5
--

stringXOR :: [Word8] -> [Word8] -> [Word8]
stringXOR key = fixedXOR (cycle key)
 
key5 = map ordB "ICE"
str5 = map ordB "Burning 'em, if you ain't quick and nimble\nI go crazy when I hear a cymbal"

result5 = to16 $ stringXOR key5 str5

--
--Problem 6
--


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


str6 :: IO [Word8]
str6 = readFile "p6.txt" >>= return . un64 . removeNL

toPairs :: [a] -> [(a,a)]
toPairs (x:y:ls) = (x,y):toPairs ls
toPairs      ls  = []

average ls = fromIntegral (sum ls) / fromIntegral (length ls)

editDistance :: Fractional a => [Word8] -> Int -> a
editDistance str n = (average $ map (\(x,y)-> (hamming x y)) ls) / fromIntegral n where
	ls = toPairs (chunksOf n str)

keysize :: IO Int
keysize = do x <- str6; return $ maxWith ((0-).editDistance x) [2..40]

switchList :: [[a]] -> [[a]]
switchList ls = if null nls then [] else map head nls : switchList (map tail nls) where
	nls = filter (not.null) ls


getCipher :: Int -> [Word8] -> [Word8]
getCipher n str = map (getSingleCipher) (switchList (chunksOf n str))


--Our answer to problem 6!
key6 = do n <- keysize; str <- str6; return $ map chrB $ getCipher n str
message6 = do str <- str6; key <- key6; return $ map chrB $ stringXOR (map ordB key) str


--
--Problem 7
--

str7 :: IO B.ByteString
str7 = readFile "p7.txt" >>= return . B.pack . un64 . removeNL

aesDecrypt :: B.ByteString -> B.ByteString
aesDecrypt bs = crypt' ECB (B.pack $ map ordB "YELLOW SUBMARINE") iv Decrypt bs where
	iv = B.pack $ take 16 $ repeat 0

--Our answer to problem 7!
message7 = str7 >>= return . aesDecrypt

--
--Problem 8
--

str8 :: IO [[Word8]]
str8 = readFile "p8.txt" >>= return . map un16 . lines

testChunks :: [Word8] -> Int
testChunks = length . nub . chunksOf 16

--Our answer to problem 8!
line8 = str8 >>= return . fromJust . findIndex (<10) . map testChunks
num8 = do strs <- str8; line <- line8; return $ testChunks $ strs !! line
encryptedMessage8 = do strs <- str8; line <- line8; return $ map chrB $ strs !! line
