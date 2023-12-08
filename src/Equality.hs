module Equality
where

import qualified Data.List as List
import Data.Set (Set)
import qualified Data.Set as Set

{- | Datentyp für Variablen und nicht interpretierte Funktionen. Implementiert
sind Funktionen mit einem oder mit zwei Parametern.
-}
data Symbol
  = -- | Variablenname
    Var String
  | -- | Funktionsame Parameter
    Fun1 String Symbol
  | -- | Funktionsname Parameter1 Parameter2
    Fun2 String Symbol Symbol
  deriving (Ord, Eq)

instance Show Symbol where
  show (Var a) = a
  show (Fun1 n s) = n ++ "(" ++ show s ++ ")"
  show (Fun2 n s1 s2) = n ++ "(" ++ show s1 ++ ", " ++ show s2 ++ ")"

-- | Datentyp für Gleichheit
data Equality
  = Equal Symbol Symbol
  | NonEq Symbol Symbol
  deriving (Ord)

---------------
-- Aufgabe 1 --
---------------

compareEquality :: Equality -> Equality -> Bool
compareEquality (Equal x_1 y_1) (Equal x_2 y_2) = x_1 == y_1 && x_2 == y_2
compareEquality (Equal x_1 y_1) (NonEq x_2 y_2) = x_1 == y_1 && x_2 /= y_2
compareEquality (NonEq x_1 y_1) (Equal x_2 y_2) = x_1 /= y_1 && x_2 == y_2
compareEquality (NonEq x_1 y_1) (NonEq x_2 y_2) = x_1 /= y_1 && x_2 /= y_2

-- | Die `Eq` Instanz von 'Equality' nutzt die obige Funktion 'compareEquality'.
instance Eq Equality where
  (==) = compareEquality

instance Show Equality where
  show (Equal s1 s2) = show s1 ++ " === " ++ show s2
  show (NonEq s1 s2) = show s1 ++ " =/= " ++ show s2

-- | Eine Äquivalenzrelation wird dargestellet als Menge von Äquivalenzklassen.
data Equivalence = Equivalence (Set EqClass)
  deriving (Show, Eq)

{- | Eine Äquivalenzklasse wird dargestellt als Menge der 'Symbol' Werte die
äquivalent sind.
-}
data EqClass = EqClass (Set Symbol)
  deriving (Show, Eq, Ord)

{- | Vereinige zwei Äquivalenzklassen zu einer neuen Klasse. Die zwei Klassen
werden aus der gesamten Äquivalenzrelation entfernt und die neue, vereinigte
Klasse wird hinzugefügt.
-}
merge ::
  -- | Die Äquivalenzrelation
  Equivalence ->
  -- | Die erste Klasse der Relation
  EqClass ->
  -- | Die zweite Klasse der Relation
  EqClass ->
  -- | Die neue Äquivalenzrelation mit den vereinigten Klassen
  Equivalence
merge (Equivalence eq) ec1@(EqClass e1) ec2@(EqClass e2) =
  Equivalence (newClass `Set.insert` eq')
 where
  eq' = ec2 `Set.delete` (ec1 `Set.delete` eq)
  newClass = EqClass (e1 `Set.union` e2)

-- | Diese Funktion gibt die Äquivalenzklasse eines Wertes von 'Symbol' zurück.
getClass :: Equivalence -> Symbol -> EqClass
getClass (Equivalence eq) s =
  if matchNumber /= 1
    then error ("element " ++ show s ++ " is in " ++ show matchNumber ++ " classes")
    else Set.elemAt 0 classes
 where
  classes = Set.filter (\(EqClass c) -> s `Set.member` c) eq
  matchNumber = Set.size classes

{- | Prädikat das entscheidet, ob in einer Äquivalenzrelation zwei Elemente
gleich sind, d.h. ob sie in der selben Äquivalenzklasse liegen.
-}
equivalent :: Equivalence -> Symbol -> Symbol -> Bool
equivalent eq s1 s2 = c1 == c2
 where
  c1 = getClass eq s1
  c2 = getClass eq s2

{- | Erzeuge eine Äquivalenzklasse mit jeweils singulären Elementen.

Für Funktionsanwendungen werden auch Klassen für die Parameter angelegt.
-}
mkEqClass :: Symbol -> Set EqClass
mkEqClass s@(Var _) = Set.singleton $ EqClass (Set.singleton s)
mkEqClass s@(Fun1 _ t) = Set.insert (EqClass (Set.singleton s)) (mkEqClass t)
mkEqClass s@(Fun2 _ t1 t2) =
  Set.insert
    (EqClass (Set.singleton s))
    (mkEqClass t1 `Set.union` mkEqClass t2)

mkEquivalence :: [EqClass] -> Equivalence
mkEquivalence = Equivalence . Set.fromList

{- | Die Funktion 'consistent' entscheidet ob eine gebene Liste von Werten von
'Equality' konsistent ist.

Für jedes Atom mit dem Konstruktor 'Equal' wird analog des Vorgehens von
Shostak's "congruence closure" eine Äquivalenzklasse mit den beiden
Elementen.

Danach wird mit den Funktionsanwendungen ähnlich verfahren, wenn t_i und t_j
in iner Klasse sind, dann werden die Klassen von F(t_i) nud F(t_j)
vereinigt.

Final wird geprüft, ob es ein 'NonEq t_i t_j' Atom gibt, aber t_i und t_j in
derselben Klasse liegen müssten.
-}
consistent :: [Equality] -> Bool
consistent eqList = go eqList eq2
 where
  eqs =
    List.filter
      ( \x -> case x of
          Equal _ _ -> True
          NonEq _ _ -> False
      )
      eqList
  eq0 = initialEquivalence eqList (mkEquivalence [])
  eq1 = buildEquivalence eqs eq0
  eq2 = congruenceClosure eq1

  go [] _ = True
  go ((NonEq s1 s2) : rest) eq =
    not (equivalent eq s1 s2) && go rest eq
  go ((Equal s1 s2) : rest) eq =
    equivalent eq s1 s2 && go rest eq

{- | Congruence closure required for Shostak's decision procedure for UF.

For each pair of function symbol values we check whether the arguments are in
the same equality class, if yes, we merge the classes of the function
symbols, too.

This is done until a fix point is reached.
-}
congruenceClosure :: Equivalence -> Equivalence
congruenceClosure eq = go eq
 where
  functionSymbols = symbolsEquivalence eq

  -- Fixpunktiteration für die congruence closure
  go :: Equivalence -> Equivalence
  go eqv = if eqv == eqv' then eqv else go eqv'
   where
    eqv' = mergeFuncClasses functionSymbols functionSymbols eqv

  -- Diese lokale Funktion führt einen Schritt der congruence closure
  -- Berechnung durch.
  --
  --
  mergeFuncClasses ::
    [Symbol] ->
    -- \^ Liste von Werten vom Typ 'Symbol'
    [Symbol] ->
    -- \^ Liste von Werten vom Typ 'Symbol'
    Equivalence ->
    -- \^ die Eingabe Äquivalenzrelation
    Equivalence
  -- \^ die berechnete neue Äquivalenzrelation

  -- Basisfall, nichts zu tun
  mergeFuncClasses [] _ eqv = eqv
  -- Die zweite Liste wurde komplett abgearbeitet, das erste Element der
  -- ersten Liste wird entfernt und mit dem Rest sowie der gesamten zweite
  -- Liste rekursiv weitergemacht.
  mergeFuncClasses (_ : rest) [] eqv =
    mergeFuncClasses rest functionSymbols eqv
  -- Funktionsanwendungen sind äquivalent, wenn der Funktionsname gleich
  -- ist und der Parameter äquivalent ist.
  --
  -- In diesem Fall werden die Klassen von `s` und `s'` gemerged.
  --
  -- Wenn `s` und `s'` schon gleich sein, die Funktionsnamen nicht gleich
  -- sind oder die Parameter nicht äquivalent sind, wird die
  -- Äquivalenzrelation nicht verändert.
  mergeFuncClasses (s@(Fun1 n1 t1) : rest) (s'@(Fun1 n2 t2) : rest') eqv =
    if equivalent eqv s s' || n1 /= n2 || not (equivalent eqv t1 t2)
      then mergeFuncClasses (s : rest) rest' eqv
      else mergeFuncClasses (s : rest) rest' eqv'
   where
    eqv' = merge eqv (getClass eqv s) (getClass eqv s')

  ---------------
  -- Aufgabe 2 --
  ---------------

  mergeFuncClasses (s@(Fun2 n1 x1 y1) : rest1) (s'@(Fun2 n2 x2 y2) : rest2) eqv =
    if equivalent eqv s s' || n1 /= n2 || not (equivalent eqv x1 x2) || not (equivalent eqv y1 y2)
      then mergeFuncClasses (s : rest1) rest2 eqv
      else mergeFuncClasses (s : rest1) rest2 eqv'
   where
    eqv' = merge eqv (getClass eqv s) (getClass eqv s')
  -- Für alle Werte vom Typ 'Symbol', die keine Funktionsanwendung von
  -- nicht-interpretierten Funktionen sind, wird die Äquivalenzrelation
  -- nicht geändert und die Liste rekursiv weiter abgearbeitet.
  mergeFuncClasses symbols (_ : rest) eqv =
    mergeFuncClasses symbols rest eqv

{- | Diese Funktion Erzeugt aus einer Äquivalenzrelation die Liste der
vorkommenden Werte vom Typ 'Symbol'.
-}
symbolsEquivalence :: Equivalence -> [Symbol]
symbolsEquivalence (Equivalence eq) = concatMap symbolsClass klassen
 where
  klassen = Set.toList eq

symbolsClass :: EqClass -> [Symbol]
symbolsClass (EqClass c) = symbols
 where
  symbols = Set.toList c

initialEquivalence :: [Equality] -> Equivalence -> Equivalence
initialEquivalence [] eq = eq
initialEquivalence ((Equal s1 s2) : rest) (Equivalence eq) =
  initialEquivalence rest (Equivalence eq')
 where
  eq' = mkEqClass s1 `Set.union` (mkEqClass s2 `Set.union` eq)
initialEquivalence ((NonEq s1 s2) : rest) (Equivalence eq) =
  initialEquivalence rest (Equivalence eq')
 where
  eq' = mkEqClass s1 `Set.union` (mkEqClass s2 `Set.union` eq)

buildEquivalence :: [Equality] -> Equivalence -> Equivalence
buildEquivalence [] eq = eq
buildEquivalence ((Equal s1 s2) : rest) eq =
  buildEquivalence rest eq'
 where
  eq' = merge eq (getClass eq s1) (getClass eq s2)
buildEquivalence _ _ = error "cannot merge non-equivalences"

example :: [Equality]
example = [Equal (Var "a") (Var "b"), Equal (Var "b") (Var "c"), NonEq (Var "c") (Var "a")]
