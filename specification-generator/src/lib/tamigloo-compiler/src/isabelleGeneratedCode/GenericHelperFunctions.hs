{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  GenericHelperFunctions(anya, nubBy, nub, enum, scanl, isSome, fstList,
                          sndList, uncurry, zipWith, flipPair, collectThe,
                          stringOfNat, splitAndGetFst, splitAndGetSnd,
                          prependToString, sortIntoBucketsOrdered,
                          sortIntoBuckets, stringOfInteger)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified Option;
import qualified HOL;
import qualified Arith;
import qualified List;

anya :: forall a. (a -> Bool) -> [a] -> Bool;
anya f l = List.foldr (\ x -> (\ a -> f x || a)) l False;

nubBy :: forall a. (a -> a -> Bool) -> [a] -> [a];
nubBy uu [] = [];
nubBy feq (x : xs) = let {
                       filteredXs = filter (\ y -> not (feq x y)) xs;
                     } in x : nubBy feq filteredXs;

nub :: forall a. (Eq a) => [a] -> [a];
nub ls = nubBy (\ a b -> a == b) ls;

enum :: forall a. Arith.Nat -> [a] -> [(Arith.Nat, a)];
enum uu [] = [];
enum i (x : xs) = (i, x) : enum (Arith.plus_nat i Arith.one_nat) xs;

scanl :: forall a b. (a -> b -> a) -> a -> [b] -> [a];
scanl f s ls = s : (case ls of {
                     [] -> [];
                     x : a -> scanl f (f s x) a;
                   });

unzip :: forall a b. [(a, b)] -> ([a], [b]);
unzip inp = let {
              splitPair = (\ p ps -> (fst p : fst ps, snd p : snd ps));
            } in List.foldr splitPair inp ([], []);

isSome :: forall a. Maybe a -> Bool;
isSome (Just uu) = True;
isSome Nothing = False;

fstList :: forall a b. [(a, b)] -> [a];
fstList pairList = fst (unzip pairList);

sndList :: forall a b. [(a, b)] -> [b];
sndList pairList = snd (unzip pairList);

uncurry :: forall a b c. (a -> b -> c) -> (a, b) -> c;
uncurry f p = f (fst p) (snd p);

zipWith :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c];
zipWith uu [] uv = [];
zipWith uw (v : va) [] = [];
zipWith f (x : xs) (y : ys) = f x y : zipWith f xs ys;

auxSplit :: [Integer] -> [Integer] -> ([Integer], [Integer]);
auxSplit first [] = (reverse first, []);
auxSplit first (c : cs) =
  (if map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
        [c] ==
        "_"
    then (reverse first, cs) else auxSplit (c : first) cs);

flipPair :: forall a b. (a, b) -> (b, a);
flipPair (a, b) = (b, a);

retDigit :: Arith.Nat -> (Arith.Nat, Arith.Nat);
retDigit x =
  let {
    a = Arith.modulo_nat x (Arith.nat_of_integer (10 :: Integer));
  } in (Arith.divide_nat x (Arith.nat_of_integer (10 :: Integer)), a);

collectThe :: forall a. [Maybe a] -> [a];
collectThe asa =
  List.map_filter (\ x -> (if isSome x then Just (Option.the x) else Nothing))
    asa;

revDigitsOfNumber :: Arith.Nat -> [Arith.Nat];
revDigitsOfNumber i =
  let {
    ip = fst (retDigit i);
    r = snd (retDigit i);
  } in (if Arith.equal_nat i Arith.zero_nat then [Arith.zero_nat]
         else (if Arith.equal_nat ip Arith.zero_nat then [r]
                else r : revDigitsOfNumber ip));

digitsOfNumber :: Arith.Nat -> [Arith.Nat];
digitsOfNumber n = reverse (revDigitsOfNumber n);

asciiOfDigit :: Arith.Nat -> Arith.Nat;
asciiOfDigit x =
  (if Arith.less_nat (Arith.nat_of_integer (9 :: Integer)) x
    then error "undefined"
    else (if Arith.equal_nat x Arith.zero_nat
           then Arith.nat_of_integer (48 :: Integer)
           else Arith.suc (asciiOfDigit (Arith.minus_nat x Arith.one_nat))));

asciiListOfNat :: Arith.Nat -> [Integer];
asciiListOfNat n =
  map Arith.integer_of_nat (map asciiOfDigit (digitsOfNumber n));

stringOfNat :: Arith.Nat -> String;
stringOfNat n =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    (asciiListOfNat n);

splitAndGetFst :: String -> String;
splitAndGetFst s =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    ((fst . auxSplit [])
      (map (let ord k | (k < 128) = Prelude.toInteger k in ord . (Prelude.fromEnum :: Prelude.Char -> Prelude.Int))
        s));

splitAndGetSnd :: String -> String;
splitAndGetSnd s =
  map (let chr k | (0 <= k && k < 128) = Prelude.toEnum k :: Prelude.Char in chr . Prelude.fromInteger)
    ((snd . auxSplit [])
      (map (let ord k | (k < 128) = Prelude.toInteger k in ord . (Prelude.fromEnum :: Prelude.Char -> Prelude.Int))
        s));

prependToString :: String -> String -> String;
prependToString first second =
  (if not (first == "")
    then (if not (second == "") then first ++ "_" ++ second else first)
    else second);

sortIntoBucketsOrdered :: forall a b. (Eq a) => [a] -> [(a, b)] -> [(a, [b])];
sortIntoBucketsOrdered buckets ps =
  let {
    emptyBuckets =
      zip (nub buckets) (List.replicate (List.size_list buckets) []);
    sortElem =
      (\ pElem ->
        map (\ p ->
              (if fst p == fst pElem then (fst p, snd pElem : snd p) else p)));
  } in List.foldr sortElem ps emptyBuckets;

sortIntoBuckets :: forall a b. (Eq a) => [(a, b)] -> [(a, [b])];
sortIntoBuckets ps = let {
                       buckets = nub (fstList ps);
                     } in sortIntoBucketsOrdered buckets ps;

stringOfInteger :: Integer -> String;
stringOfInteger i = stringOfNat (Arith.nat_of_integer i);

}
