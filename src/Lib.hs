{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE TemplateHaskell#-}

-- Other Parsers
-- https://github.com/J-mie6/ParsleyHaskell
-- https://hackage.haskell.org/package/Cabal-3.6.1.0/docs/Distribution-Parsec.html#t:ParsecParser


module Lib
  ( unf,
    HeaderInfo (..),
    getHeaderInfo,
    packages,
    headerCount
  )
where

import Crypto.Hash (hashFinalize, hashInit, hashUpdate)
import Crypto.Hash.Algorithms (SHA256)
import Data.ByteString (ByteString)
import Data.Either (isRight)
import Data.Function ((&))
import Data.Maybe (fromJust, fromMaybe)
import Data.Void (Void)
import Streamly.External.Archive
import Streamly.Internal.Data.Fold.Type (Fold (Fold), Step (Partial))
import Streamly.Internal.Data.Unfold.Type (Unfold)
import qualified Streamly.Internal.Data.Unfold as Unfold
import qualified Streamly.Prelude as S
import Data.Functor.Identity
import Data.Bifunctor
import qualified Data.Map.Strict as Map
import qualified Data.ByteString as B
import Data.ByteString (ByteString)
import FlatParse.Basic
import qualified Data.List as List
import qualified Data.ByteString.Char8 as C
import Data.Either
import Data.Char (ord)
import Distribution.Fields
import Distribution.Fields.Field
import Data.Bool
import Data.Maybe
import Control.Applicative (liftA2)
import Distribution.Parsec.Position (Position)
import qualified Data.Graph.Inductive.Graph as G
import Data.Graph.Inductive.PatriciaTree (Gr)
import qualified Data.IntMap.Strict as IntMap
import Data.Graph.Inductive.Query.DFS

unf :: Unfold IO Void (Either Header ByteString)
unf = readArchive "/Users/tonyday/.cabal/packages/hackage.haskell.org/01-index.tar"

data HeaderInfo =
  HeaderInfo
  { fileType :: Maybe FileType,
    pathName :: Maybe ByteString,
    pathNameUtf8 :: Maybe ByteString,
    size :: Maybe Int} deriving (Eq, Show)

getHeaderInfo :: Header -> IO HeaderInfo
getHeaderInfo h = do
  ft <- headerFileType h
  pn <- headerPathName h
  pnu <- headerPathNameUtf8 h
  s <- headerSize h
  pure (HeaderInfo ft pn pnu s)

rollHeader :: Fold IO (Either Header ByteString) (Maybe HeaderInfo, Maybe ByteString)
rollHeader = Fold step initial done
  where
    step ::
      (Maybe HeaderInfo, Maybe ByteString) ->
      (Either Header ByteString) ->
      IO (Step (Maybe HeaderInfo, Maybe ByteString) (Maybe HeaderInfo, Maybe ByteString))
    step (minfo, mctx) e =
      case e of
        Left h -> do
          minfo' <- getHeaderInfo h
          pure $ Partial (Just minfo', mctx)
        Right bs -> pure $ Partial (minfo, mctx <> Just bs)

    initial :: IO (Step (Maybe HeaderInfo, Maybe ByteString) (Maybe HeaderInfo, Maybe ByteString))
    initial = pure (Partial (Nothing, Nothing))

    done :: (Maybe HeaderInfo, Maybe ByteString) -> IO (Maybe HeaderInfo, Maybe ByteString)
    done = pure


-- Execute the stream, grouping at the headers (the Lefts).
packages :: S.IsStream t =>
                  Unfold IO a (Either Header ByteString)
                  -> t IO (Maybe HeaderInfo, Maybe ByteString)
packages arc =
    S.unfold arc undefined
        & S.groupsBy (\e _ -> isRight e) rollHeader

-- | count total packages
--
-- >>> S.unfold unf undefined & S.fold headerCount
-- 276177
headerCount :: (Applicative m) => Fold m (Either Header ByteString) Int
headerCount = Fold step initial done where
  step x e = case e of
    Left _ -> pure $ Partial $ x + 1
    Right _ -> pure $ Partial x
  initial = pure $ Partial 0
  done = pure

-- | all pathNAmes exist, all file types are regular and there are no utf8 issues with pathNames
--
-- >>> S.toList $ S.filter ((/= Just (Just FileTypeRegular)) . fmap fileType) $ S.take 10 $ fmap fst $ packages (Unfold.take 10000000 unf)
-- []
-- >>> S.toList $ S.filter (\x -> fmap pathName x /= fmap pathNameUtf8 x) $ S.take 10 $ fmap fst $ packages (Unfold.take 10000000 unf)
-- []
--
-- >>> S.toList $ S.filter (\x -> fmap pathName x == Nothing) $ S.take 10 $ fmap fst $ packages (Unfold.take 10000000 unf)
-- []

-- So we can switch to pathName
rollName :: Fold IO (Either Header ByteString) (ByteString, ByteString)
rollName = Fold step initial done
  where
    step ::
      (Maybe ByteString, Maybe ByteString) ->
      (Either Header ByteString) ->
      IO (Step (Maybe ByteString, Maybe ByteString) (ByteString, ByteString))
    step (name, bs) e =
      case e of
        Left h -> do
          name' <- headerPathName h
          pure $ Partial (name', bs)
        Right bs' -> pure $ Partial (name, bs <> Just bs')

    initial :: IO (Step (Maybe ByteString, Maybe ByteString) (ByteString, ByteString))
    initial = pure (Partial (Nothing, Nothing))

    done :: (Maybe ByteString, Maybe ByteString) -> IO (ByteString, ByteString)
    done = pure . bimap (maybe mempty id) (maybe mempty id)

-- Execute the stream, grouping by pathName (the Lefts).
packages' :: S.IsStream t =>
                  Unfold IO a (Either Header ByteString)
                  -> t IO (ByteString, ByteString)
packages' arc =
    S.unfold arc undefined
        & S.groupsBy (\e _ -> isRight e) rollName

-- none of the package contents are empty
-- >>> S.toList $ S.take 10 $ S.filter ((=="") . snd) $ packages' unf
-- []

-- package path names are either preferred-versions, .cabal or package.json
-- >>> S.toList $ fmap fst $ S.filter (not . (\x -> B.isSuffixOf "preferred-versions" x || B.isSuffixOf ".cabal" x || B.isSuffixOf "package.json" x) . fst) $ packages' (Unfold.take 10000000 unf)
-- []

data NameType = CabalName | PreferredVersions | PackageJson | BadlyNamed deriving (Show, Ord, Eq)

toNameType :: ByteString -> NameType
toNameType bs
 | B.isSuffixOf "preferred-versions" bs = PreferredVersions
 | B.isSuffixOf "package.json" bs = PackageJson
 | B.isSuffixOf ".cabal" bs = CabalName
 | otherwise = BadlyNamed

count :: (Applicative m, Ord a) => Fold m a (Map.Map a Int)
count = Fold step initial done where
  step x a = pure $ Partial $ Map.insertWith (+) a 1 x
  initial = pure $ Partial Map.empty
  done = pure

-- >>> S.fold Lib.count $ fmap (bimap toNameType (=="")) $ packages' (Unfold.take 10000000 unf)
-- fromList [((CabalName,False),151738),((PreferredVersions,False),2592),((PreferredVersions,True),40),((PackageJson,False),121807)]

-- https://hackage.haskell.org/package/flatparse

slash :: Parser () ()
slash = $(char '/')

notslash :: Parser () String
notslash = chainr (:) (satisfy (/='/')) (fmap (const []) slash)

cabalSuffix :: Parser () ()
cabalSuffix = $(string ".cabal")

notcabal :: Parser () String
notcabal = chainr (:) anyChar (fmap (const []) cabalSuffix)

--
-- >>> runParser paths "1/2/3.cabal"
-- OK ["1","2","3.cabal"] ""
paths :: Parser () [String]
paths = (\xs e -> xs <> [e]) <$> many notslash <*> takeRest

-- |
--
-- >>> S.toList $ S.take 100 $ S.filter isLeft $ fmap (parsePath . fst) $ S.filter ((==CabalName) . toNameType . fst) (packages' (Unfold.take 10000000 unf))
-- []
parsePath :: ByteString -> Either ByteString (String, String)
parsePath bs = case runParser paths bs of
  OK (a:b:c:[]) "" -> case Just (C.pack a) == B.stripSuffix ".cabal" (C.pack c) of
    True -> Right (a,b)
    False -> Left bs
  _ -> Left bs

-- S.toList $ S.take 100 $ fmap (fromRight undefined) $ S.filter isRight $ fmap (parsePath . fst) $ S.filter ((==CabalName) . toNameType . fst) (packages' (Unfold.take 10000000 unf))

-- >>> m1 <- S.fold (collect fst snd) $ fmap (fromRight undefined) $ S.filter isRight $ fmap (parsePath . fst) $ S.filter ((==CabalName) . toNameType . fst) (packages' (Unfold.take 10000000 unf))
-- >>> :t m1
collect :: (Applicative m, Ord k) => (a -> k) -> (a -> v) -> Fold m a (Map.Map k [v])
collect k v = Fold step initial done where
  step x a = pure $ Partial $ Map.insertWith (<>) (k a) [v a] x
  initial = pure $ Partial Map.empty
  done = pure

parseVersion :: ByteString -> Either ByteString [Int]
parseVersion bs = case runParser ints' bs of
  OK [] _ -> Left bs
  OK xs "" -> Right xs
  _ -> Left bs

toVer :: [Int] -> ByteString
toVer xs = B.intercalate "." (C.pack . show <$> xs)

digit :: Parser () Int
digit = (\c -> ord c - ord '0') <$> satisfyASCII isDigit

int :: Parser () Int
int = do
  (place, n) <- chainr (\n (!place, !acc) -> (place*10,acc+place*n)) digit (pure (1, 0))
  case place of
    1 -> empty
    _ -> pure n

--
-- >>> runParser paths "1/2/3.cabal"
-- OK ["1","2","3.cabal"] ""
ints' :: Parser () [Int]
ints' = (\xs e -> xs <> [e]) <$> many ((\x _ -> x) <$> int <*> vdot) <*> int

vdot :: Parser () ()
vdot = $(char '.')

-- | malformed versions
--
-- mErrs <- S.fold (collect fst snd) $ S.filter (isLeft . snd) $ fmap (second (parseVersion . C.pack)) $ fmap (fromRight undefined) $ S.filter isRight $ fmap (parsePath . fst) $ S.filter ((==CabalName) . toNameType . fst) (packages' (Unfold.take 10000000 unf))
-- mErrs
-- fromList []
--
-- >>> m2 <- S.fold (collect fst snd) $ fmap (second (fromRight undefined)) $ S.filter (isRight . snd) $ fmap (second (parseVersion . C.pack)) $ fmap (fromRight undefined) $ S.filter isRight $ fmap (parsePath . fst) $ S.filter ((==CabalName) . toNameType . fst) (packages' (Unfold.take 10000000 unf))
-- >>> length $ Map.toList $ Map.filter (==[]) $ Map.map maximum m2
-- 0

-- >>> take 100 $ List.sortOn (Down . snd) $ Map.toList $ Map.map length m2
-- [("ats-pkg",576),("lens",531),("warp",453),("purescript",391),("hspec",368),("yesod-core",357),("http-conduit",302),("wai-extra",302),("http-client",293),("persistent",291),("tidal",282),("pandoc",277),("hlint",262),("git-annex",253),("haskoin-store",251),("madlang",248),("yaml",240),("text",238),("hspec-core",237),("happstack-server",234),("tls",232),("ghc-mod",226),("fay",220),("pandoc-citeproc",217),("shake-ats",217),("aeson",215),("conduit",208),("vty",207),("hakyll",199),("linear",197),("egison",189),("hpack",189),("shelly",187),("relational-query",186),("attoparsec",183),("haskell-src-exts",181),("shake",176),("shake-ext",176),("conduit-extra",174),("yesod-auth",171),("acid-state",170),("brick",164),("language-ats",163),("QuickCheck",162),("stack",161),("yesod-form",161),("tasty",158),("hOpenPGP",157),("tweet-hs",157),("HsOpenSSL",156),("mono-traversable",156),("propellor",156),("amazonka-core",152),("trifecta",149),("dns",147),("postgresql-simple",147),("shakespeare",147),("cabal2nix",143),("hw-prim",142),("esqueleto",141),("hindent",141),("http2",141),("binary",139),("criterion",138),("persistent-template",138),("fast-logger",137),("yesod-bin",134),("texmath",133),("yesod",133),("fast-arithmetic",132),("snap-server",130),("hoogle",129),("persistent-sqlite",129),("clash-ghc",128),("hedis",127),("classy-prelude",126),("xml-conduit",126),("hsdev",124),("cpkg",123),("hamlet",123),("wai-app-static",123),("keter",122),("text-show",122),("semigroupoids",121),("hledger",120),("websockets",115),("JuicyPixels",113),("snap",113),("snap-core",111),("diagrams-lib",110),("aws",108),("persistent-postgresql",108),("swagger2",108),("cabal-install",107),("hledger-lib",107),("network",107),("ginger",106),("sbv",106),("ad",105),("influxdb",105)]

-- Adding in the cabal file and keeping just the latest
-- >>> m4 <- S.fold (keep (fst . fst) (\((_,v),c) -> (v,c)) (\x y -> bool x y ((fst x) > (fst y)))) $ fmap (first (second (fromRight undefined))) $ S.filter (isRight . snd . fst) $ fmap (first (second (parseVersion . C.pack))) $ fmap (first (fromRight undefined)) $ S.filter (isRight . fst) $ fmap (first parsePath) $ S.filter ((==CabalName) . toNameType . fst) (packages' (Unfold.take 10000000 unf))
--
keep :: (Applicative m, Ord k) => (a -> k) -> (a -> v) -> (v -> v -> v) -> Fold m a (Map.Map k v)
keep k v c = Fold step initial done where
  step x a = pure $ Partial $ Map.insertWith c (k a) (v a) x
  initial = pure $ Partial Map.empty
  done = pure

latestCabalFiles :: IO (Map.Map String ([Int], ByteString))
latestCabalFiles =
  S.fold
  (keep
   (fst . fst)
   (\((_,v),c) -> (v,c))
   (\x y -> bool x y ((fst x) < (fst y)))) $
  fmap (first (second (fromRight undefined))) $
  S.filter (isRight . snd . fst) $
  fmap (first (second (parseVersion . C.pack))) $
  fmap (first (fromRight undefined)) $
  S.filter (isRight . fst) $
  fmap (first parsePath) $
  S.filter
  ((==CabalName) . toNameType . fst)
  (packages' (Unfold.take 10000000 unf))

-- Field (Name (Position 9 1) "author") [FieldLine (Position 9 16) "Matthias Reisner"],Field (Name (Position 10 1) "maintainer") [FieldLine (Position 10 16) "wolfgang@cs.ioc.ee"],Field (Name (Position 11 1) "stability") [FieldLine (Position 11 16) "provisional"]

-- bad fields
-- fmap (\x -> C.pack (fst x) <> "-" <> toVer (fst (snd x))) $ Map.toList $ Map.filter (isLeft . readFields . snd) lcf
-- ["DSTM-0.1.2","control-monad-exception-mtl-0.10.3","ds-kanren-0.2.0.1","metric-0.2.0","phasechange-0.1","smartword-0.0.0.5"]

-- valid cabal files that parse ok
-- >>> length $ Map.toList $ fmap (second (fromRight undefined)) $ Map.filter (isRight . snd) $ fmap (second readFields) lcf
-- 16094
validLatestCabals :: IO (Map.Map String ([Int], [Field Position]))
validLatestCabals = do
  lcf <- latestCabalFiles
  pure $
    fmap (second (fromRight undefined)) $
    Map.filter (isRight . snd) $
    fmap (second readFields) lcf

topnames :: Field a -> ByteString
topnames (Field (Name _ n) _) = n
topnames (Section (Name _ n) _ _) = n

author :: Field a -> [ByteString]
author (Field (Name _ "author") xs) = fieldLineBS <$> xs
author _ = []

authors :: [Field a] -> [ByteString]
authors xs = mconcat $ fmap author xs

fieldValue :: ByteString -> Field a -> [ByteString]
fieldValue f (Field (Name _ n) xs) = case f == n of
  True -> fieldLineBS <$> xs
  False -> []
fieldValue _ _ = []

vs :: ByteString -> [Field a] -> [ByteString]
vs v xs = mconcat $ fmap (fieldValue v) xs


-- top 20 field names
-- >>> fmap (take 20 . List.sortOn (Down . snd) . Map.toList) $ S.fold Lib.count $ S.fromList $ fmap topnames $ mconcat $ fmap snd $ Map.toList $ fmap snd vlcs
-- [("license",16098),("name",16095),("version",16094),("maintainer",16023),("synopsis",15936),("cabal-version",15828),("build-type",15769),("category",15743),("author",15633),("license-file",15512),("description",14958),("library",14483),("source-repository",12623),("homepage",12095),("extra-source-files",9600),("copyright",9148),("test-suite",7531),("executable",6913),("bug-reports",6122),("tested-with",3954)]


-- top 10 authors
-- >>> fmap (take 10 . List.sortOn (Down . snd) . Map.toList) $ S.fold Lib.count $ S.fromList $ mconcat $ fmap authors $ fmap snd $ Map.toList $ fmap snd vlcs
-- [("Brendan Hay",333),("Nikita Volkov <nikita.y.volkov@mail.ru>",142),("Henning Thielemann <haskell@henning-thielemann.de>",102),("Edward A. Kmett",98),("Andrew Martin",97),("Tom Sydney Kerckhove",96),("Michael Snoyman",88),("M Farkas-Dyck",78),("OleksandrZhabenko",75),("Vanessa McHale",75)]


-- library
sec :: FieldName -> Field ann -> Maybe ([SectionArg ann], [Field ann])
sec f (Section (Name _ n) sargs fs) = case f == n of
  True -> Just (sargs, fs)
  False -> Nothing
sec _ (Field _ _) = Nothing


-- not-a-library
-- >>> Map.size $ Map.filter ((0==) . length) $ fmap (catMaybes . fmap (sec "library") . snd) vlcs
-- 1715
--
-- multiple libraries
-- Map.size $ Map.filter ((>1) . length) $ fmap (catMaybes . fmap (sec "library") . snd) vlcs
-- 58

-- Multiple libraries are usually "internal" libraries that can only be used inside the cabal file.
--
-- take 10 $ Map.toList $ Map.filter (\x -> x/=[[]] && x/=[] && listToMaybe x /= Just []) $ fmap (fmap (fmap secName) . fmap fst . catMaybes . fmap (sec "library") . snd) vlcs
-- [("LiterateMarkdown",[[("name","converter")]]),("buffet",[[("name","buffet-internal")]]),("cabal-fmt",[[("name","cabal-fmt-internal")]]),("cuckoo",[[("name","random-internal")],[]]),("dhrun",[[("name","dhrun-lib")]]),("dns",[[("name","dns-internal")],[]]),("escoger",[[("name","escoger-lib")]]),("ghc-plugs-out",[[("name","no-op-plugin")],[("name","undefined-init-plugin")],[("name","undefined-solve-plugin")],[("name","undefined-stop-plugin")],[("name","call-count-plugin")]]),("haskell-ci",[[("name","haskell-ci-internal")]]),("hid-examples",[[("name","ipgen-lib")],[("name","iplookup-lib")]])]

-- number of libraries
-- >>> length $ Map.toList $ Map.filter (/=[]) $ fmap (catMaybes . fmap (sec "library")) $ fmap snd vlcs
-- 14379

-- common stanzas
-- >>> length $ Map.toList $ Map.filter (/=[]) $ fmap (catMaybes . fmap (sec "common")) $ fmap snd vlcs
-- 429
--
secName :: SectionArg a -> (ByteString, ByteString)
secName (SecArgName _ n) = ("name", n)
secName (SecArgStr _ n) = ("str", n)
secName (SecArgOther _ n) = ("other", n)

-- multiple libraries are possible
--
-- >>> cls <- S.fold count $ fmap snd $ S.fromList $ Map.toList $ fmap length $ Map.filter (/=[]) $ fmap (catMaybes . fmap (sec "library")) $ fmap snd vlcs
-- >>> cls
-- fromList [(1,14321),(2,49),(3,3),(4,1),(5,1),(6,1),(7,1),(11,1),(22,1)]
--
-- raaz is the 22

-- take 10 $ List.sortOn (Down . snd) $ Map.toList $ fmap (sum . fmap length) $ fmap (fmap (vs "build-depends")) $ Map.filter (/=[]) $ fmap (fmap snd . catMaybes . fmap (sec "library") . snd) vlcs
-- [("acme-everything",7533),("yesod-platform",132),("planet-mitchell",109),("sockets",83),("ghcide",69),("sprinkles",67),("too-many-cells",67),("pandoc",65),("pantry-tmp",64),("purescript",62)]
-- sum $ fmap snd $ Map.toList $ fmap (sum . fmap length) $ fmap (fmap (vs "build-depends")) $ Map.filter (/=[]) $ fmap (fmap snd . catMaybes . fmap (sec "library") . snd) vlcs
-- 102270
-- >>> sum $ fmap snd $ Map.toList $ fmap (sum . fmap length) $ fmap (fmap (vs "build-depends")) $ Map.filter (/=[]) $ fmap (fmap snd . catMaybes . fmap (sec "common") . snd) vlcs
-- 2725

-- build-depends
-- >>> take 3 $ Map.toList $ Map.map (fmap (vs "build-depends" . snd)) $ Map.filter (/=[]) $ fmap (catMaybes . fmap (sec "library")) $ fmap snd vlcs
-- [("3dmodels",[["base >=4.7 && <4.8, attoparsec >=0.12 && <0.13, bytestring >=0.10 && <0.11, linear >=1.10 && <1.11, packer >=0.1 && <0.2"]]),("AAI",[["base >=4.8 && <4.9"]]),("ABList",[["base < 5 && >= 3,","linear,","newtype"]])]

-- find common build-deps imported to a library section
-- take 3 $ Map.toList $ Map.filter (/= [[]]) $ Map.map (fmap (vs "import" . snd)) $ Map.filter (/=[]) $ fmap (catMaybes . fmap (sec "library")) $ fmap snd vlcs[("ADPfusion",[["deps"]]),("Allure",[["options"]]),("BiobaseENA",[["deps"]])]
--
-- | take a list of Fields which is an entire cabal file and find the raw build-depend rows for the library sections, if there are any.
--
-- >>> length $ Map.toList $ Map.filter (/=[]) $ fmap (fmap mconcat . rawBuildDeps . snd) vlcs
-- 14379
--
-- >>> sum $ fmap sum $ fmap snd $ Map.toList $ Map.filter (/=[]) $ fmap (fmap length . rawBuildDeps . snd) vlcs
-- 103941
--
-- >>> take 5 $ Map.toList $ Map.filter (/=[]) $ fmap (rawBuildDeps . snd) vlcs
-- [("3dmodels",[["base >=4.7 && <4.8, attoparsec >=0.12 && <0.13, bytestring >=0.10 && <0.11, linear >=1.10 && <1.11, packer >=0.1 && <0.2"]]),("AAI",[["base >=4.8 && <4.9"]]),("ABList",[["base < 5 && >= 3,","linear,","newtype"]]),("AC-Angle",[["base >= 4 && < 5"]]),("AC-Boolean",[["base >= 4 && < 5"]])]
rawBuildDeps :: [Field a] ->  [[ByteString]]
rawBuildDeps xs =
  bdeps <> bdepImports
  where
    libs = fmap snd . catMaybes . fmap (sec "library") $ xs
    bdeps = fmap (vs "build-depends") libs
    libImports = fmap (vs "import") libs
    common = catMaybes . fmap (sec "common") $ xs
    cbdMap =
      Map.fromList $
      fmap (second (vs "build-depends") .
            first (fromJust . listToMaybe . fmap (snd . secName)))
      common
    bdepImports =
      fmap (mconcat .
            fmap (\x -> fromMaybe [] $ Map.lookup x cbdMap))
      libImports

-- >>> vlcs <- validLatestCabals
-- >>> deps = fmap (fmap mconcat) $ Map.filter (/=[]) $ fmap (rawBuildDeps . snd) $ Map.delete "acme-everything" vlcs
-- >>> Map.size deps
-- 13378
--

-- lex check
-- >>> S.fold count $ S.concatMap S.fromList $ fmap B.unpack $ S.concatMap S.fromList $ S.concatMap S.fromList $ S.fromList $ fmap snd depss
-- [('\t',27),(' ',563886),('&',83478),('(',461),(')',461),('*',5774),(',',97071),('-',36556),('.',135649),('0',75340),('1',60877),('2',30576),('3',19604),('4',28250),('5',21803),('6',9877),('7',8704),('8',6533),('9',5997),('<',43729),('=',76150),('>',62990),('A',361),('B',312),('C',1236),('D',580),('E',127),('F',218),('G',425),('H',955),('I',148),('J',132),('K',33),('L',606),('M',515),('N',138),('O',328),('P',560),('Q',604),('R',305),('S',700),('T',650),('U',229),('V',102),('W',108),('X',115),('Y',35),('Z',25),('^',2445),('a',78255),('b',30324),('c',38163),('d',22177),('e',113793),('f',13316),('g',18050),('h',18341),('i',55866),('j',702),('k',8554),('l',37199),('m',27980),('n',56984),('o',50832),('p',30439),('q',2619),('r',70518),('s',82337),('t',92888),('u',15594),('v',7177),('w',4328),('x',10475),('y',18541),('z',1764),('{',14),('|',1496),('}',14)]

-- each ByteString should be a comma separated list of range-bound dependencies
-- commas can also occur in the {1.0, 2.0} range definition
comma :: Parser () ()
comma = $(string ",")

-- actual range work should probably use the Cabal library

-- braces
-- take 2 $ Map.toList $ Map.filter (any isRight . fmap (parseOK (many (satisfyASCII (/= '{')) *> braces <* takeLine))) deps
-- [("enummaps",["base ^>= { 4.12, 4.13, 4.14 },containers ^>= 0.6.2.1,deepseq ^>= 1.4",""]),("evdev",["","base >= 4.11 && < 5,bytestring ^>= {0.10, 0.11},containers ^>= 0.6.2,extra ^>= {1.6.18, 1.7},filepath-bytestring ^>= 1.4.2,monad-loops ^>= 0.4.3,rawfilepath ^>= 0.2.4,time ^>= {1.9.3, 1.10, 1.11},unix ^>= 2.7.2,"])]
--
--
braces :: Parser () String
braces =
  $(string "{") *>
  many (satisfyASCII (/='}')) <*
  $(string "}")

parseOK :: Parser e a -> ByteString -> Either ByteString a
parseOK p bs = case runParser p bs of
  OK a "" -> Right a
  _ -> Left bs

-- separated by commas, but not commas inside braces
--
--


initialPackageChar :: Parser () Char
initialPackageChar =
  satisfyASCII
  (`C.elem`
   (C.pack $
    ['a'..'z'] <>
    ['A' .. 'Z'] <>
    ['0' .. '9']))

packageChar :: Parser () Char
packageChar =
  satisfyASCII
  (`C.elem`
   (C.pack $
    ['a'..'z'] <>
    ['A' .. 'Z'] <>
    ['-'] <>
    ['0'..'9']))

invalidPackageChar :: Parser () Char
invalidPackageChar =
  satisfyASCII
  (`C.notElem`
   (C.pack $
    ['a'..'z'] <>
    ['A' .. 'Z'] <>
    ['-'] <>
    ['0'..'9']))

validName :: Parser () String
validName = (:) <$> initialPackageChar <*> many packageChar

-- >>> runParser (many (many invalidPackageChar *> validName <* (many (satisfyASCII (not . (`elem` [',','{']))) <* optional braces) <* (many (satisfyASCII (not . (`elem` [',','{']))) <* optional braces) <* optional comma)) "base ^>= { 4.12, 4.13, 4.14 } && == { 4.15, 4.16 } || == 5 , containers ^>= 0.6.2.1,deepseq ^>= 1.4"
-- OK ["base","5","containers","deepseq"] ""
--

depField :: Parser () ByteString
depField = fmap (C.pack . mconcat) $ many (some (satisfyASCII (not . (`elem` [',','{']))) <|> braces)

adep :: Parser () String
adep = many invalidPackageChar *> validName <* takeLine

intercalated :: Parser a item -> Parser a sep -> Parser a [item]
intercalated item sep = (:) <$> item <*> chainr (:) (sep *> item) (pure [])

intercalated' :: Parser () item -> Parser () sep -> Parser () [item]
intercalated' item sep =
  (optional comma) *>
  ((:) <$> item <*> chainr (:) (sep *> item) (pure [])) <*
  (optional comma)

-- >>> parseDeps "base ^>= { 4.12, 4.13, 4.14 } && == { 4.15, 4.16 } || == 5 , containers ^>= 0.6.2.1,deepseq ^>= 1.4"
-- Right ["base","containers","deepseq"]
--
-- >>> take 3 $ Map.toList $ Map.filter (any isLeft) $ fmap (fmap parseDeps) deps
-- []
parseDeps :: ByteString -> Either ByteString [String]
parseDeps bs = case bs of
  "" -> Right []
  bs' ->
    bool
    (fmap (fmap (fromRight undefined) . filter isRight) ds)
    (Left bs')
    (either (const True) (any isLeft) ds)
    where
      xs = parseOK (intercalated' depField comma) bs'
      ds = second (fmap (parseOK adep) . filter (/="")) xs

-- >>> sum $ fmap (length . snd) $ Map.toList $ fmap (mconcat . fmap ((fromRight undefined) . parseDeps)) deps
-- 110868

-- most dependencies
-- >>> take 40 $ List.sortOn (Down . snd) $ fmap (second length) $ Map.toList $ fmap (mconcat . fmap ((fromRight undefined) . parseDeps)) deps
-- [("acme-everything",7533),("raaz",144),("yesod-platform",132),("planet-mitchell",109),("sockets",83),("ghcide",69),("sprinkles",67),("too-many-cells",67),("pandoc",66),("pantry-tmp",64),("neuron",62),("purescript",62),("stack",59),("taffybar",59),("hermes",58),("hnix",58),("espial",56),("project-m36",56),("ghcup",55),("ribosome",55),("stackage-curator",55),("gitit",53),("leksah",53),("freckle-app",51),("hevm",51),("calamity",50),("wrecker",50),("clash-lib",49),("porcupine-core",49),("postgrest",49),("toysolver",49),("hoodle-core",48),("clckwrks",47),("dhall",47),("funflow",47),("futhark",47),("hercules-ci-cli",47),("hsdev",47),("matterhorn",47),("morley",47)]

-- top 40 dependencies
-- >>> fmap (take 40) $ fmap (List.sortOn (Down . snd)) $ fmap Map.toList $ S.fold count $ S.concatMap S.fromList $ S.fromList $ fmap snd $ Map.toList $ fmap (mconcat . fmap ((fromRight undefined) . parseDeps)) deps
-- [("base",14016),("bytestring",5045),("text",4545),("containers",4392),("mtl",3276),("transformers",2922),("aeson",1837),("time",1812),("vector",1682),("directory",1510),("filepath",1435),("template-haskell",1342),("unordered-containers",1312),("deepseq",1162),("lens",1118),("binary",900),("hashable",857),("array",851),("process",809),("exceptions",772),("attoparsec",765),("stm",762),("random",737),("parsec",718),("network",716),("http-types",714),("data-default",591),("QuickCheck",563),("conduit",472),("http-client",462),("split",456),("semigroups",446),("ghc-prim",441),("primitive",417),("monad-control",410),("async",393),("unix",391),("utf8-string",388),("resourcet",385),("scientific",370)]

-- All the build-depends found
-- >>> bdnames <- fmap (fmap fst) $ fmap Map.toList $ S.fold count $ S.concatMap S.fromList $ S.fromList $ fmap snd $ Map.toList $ fmap (mconcat . fmap ((fromRight undefined) . parseDeps)) deps
-- length bdnames
-- 5426

-- upto
-- tracking down errors
-- >>> take 10 $ filter (not . (`elem` (Map.keys vlcs))) bdnames
-- ["SDL2","UniqueLogicNP","WEditor-internal","aead-api","aesonbase","andromeda","applicative","auth-api","basebase","basebytestring"]
-- >>> length $ filter (not . (`elem` (Map.keys vlcs))) bdnames
-- 130
--
-- >>> depsExclude = filter (not . (`elem` (Map.keys vlcs))) bdnames
-- >>> vdeps' = fmap (filter (not . (`elem` depsExclude))) vdeps
-- >>> sum $ fmap snd $ Map.toList $ fmap length vdeps'
-- 103136

-- - [x] error 1 - commas can be inside braces
-- ("streamly-fsnotify","base >= 4.9 && < 5,filepath ^>= 1.4.2.1,fsnotify ^>= 0.3.0.1,semirings ^>= {0.5.2, 0.6},streamly ^>= {0.7.0, 0.8},text ^>= 1.2.3.0,time ^>= {1.6, 1.7, 1.8, 1.9, 1.10, 1.11, 1.12},")
-- error 2 - plain old dodgy depends
-- acme-everything, cabal, deprecated packages
--
-- error 3 - multiple build-depends in one stanza
-- grab
--
-- error 4 - conditionals
--
-- error 5 - packages not on Hackage
-- cardano
-- "This library requires quite a few exotic dependencies from the cardano realm which aren't necessarily on hackage nor stackage. The dependencies are listed in stack.yaml, make sure to also include those for importing cardano-transactions."
-- https://raw.githubusercontent.com/input-output-hk/cardano-haskell/d80bdbaaef560b8904a828197e3b94e667647749/snapshots/cardano-1.24.0.yaml
--
-- error 6 - internal library (only available to the main cabal library stanza)
-- yahoo-prices, vector-endian, symantic-parser


-- fgl


-- >>> vlcs <- validLatestCabals
-- >>> deps = fmap (fmap mconcat) $ Map.filter (/=[]) $ fmap (rawBuildDeps . snd) $ Map.delete "acme-everything" vlcs
-- >>> vdeps = fmap (mconcat . fmap ((fromRight undefined) . parseDeps)) deps
-- >>> bdnames <- fmap (fmap fst) $ fmap Map.toList $ S.fold count $ S.concatMap S.fromList $ S.fromList $ fmap snd $ Map.toList $ fmap (mconcat . fmap ((fromRight undefined) . parseDeps)) deps
-- >>> depsExclude = filter (not . (`elem` (Map.keys vlcs))) bdnames
-- >>> vdeps' = fmap (filter (not . (`elem` depsExclude))) vdeps
-- >>> pmap = zip [0..] (fmap fst $ Map.toList $ vlcs)
-- >>> IntMap.size pmap
-- >>> rpmap = Map.fromAscList $ zip (fmap fst $ Map.toList $ vlcs) [0..]
-- >>> les = fmap (\(x,y) -> (x,y,1)) $ mconcat $ fmap (\(k, vs) -> fmap (k,) vs) $ Map.toList $ Map.mapKeys (rpmap Map.!) $ fmap (fmap (rpmap Map.!)) vdeps'
-- >>> let g = G.mkGraph pmap les :: Gr String Int
-- >>> G.noNodes g
-- 16094
-- >>> length (G.labEdges g)
-- 103136

-- >>> take 100 $ reverse $ topsort' g
-- ["3d-graphics-examples","ghc-prim","ghc-bignum","base","array","deepseq","bytestring","containers","binary","ghc-boot-th","pretty","template-haskell","text","hashable","integer-logarithms","transformers","primitive","scientific","attoparsec","tagged","transformers-compat","comonad","contravariant","base-orphans","distributive","mtl","stm","exceptions","indexed-traversable","th-abstraction","bifunctors","semigroupoids","transformers-base","free","profunctors","semigroups","void","adjunctions","binary-orphans","cereal","time","unordered-containers","bytes","assoc","call-stack","filepath","vector","indexed-traversable-instances","StateVar","invariant","kan-extensions","parallel","reflection","these","strict","lens","splitmix","random","linear","packer","3dmodels","4Blocks","AAI","newtype","ABList","AC-Angle","AC-Boolean","AC-BuildPlatform","AC-Colour","utf8-string","cairo","glib","directory","process","pango","gtk","AC-EasyRaster-GTK","AC-HalfInteger","AC-MiniTest","AC-PPM","AC-Random","colour","ansi-terminal","AC-Terminal","AC-VanillaArray","AC-Vector","AC-Vector-Fancy","list-extras","MonadRandom","random-shuffle","ACME","QuickCheck","mmorph","pipes","pipes-parse","pipes-group","stringsearch","pipes-bytestring","logict","smallcheck"]
