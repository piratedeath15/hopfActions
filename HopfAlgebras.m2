newPackage("HopfAlgebras",
     Headline => "Data types for Hopf algebras",
     Version => "0.1",
     Date => "Nov 27, 2018",
     Authors => {
	  {Name => "Colin Martin",
	   HomePage => "http://www.google.com",
	   Email => "martce17@wfu.edu"},
	  {Name => "Frank Moore",
	   HomePage => "http://www.math.wfu.edu/Faculty/Moore.html",
	   Email => "moorewf@wfu.edu"}},
     PackageExports => {"NCAlgebra"},
     PackageImports => {"PrimaryDecomposition"},
     AuxiliaryFiles => true,
     DebuggingMode => true,
     CacheExampleOutput =>true
     )

export {"NCBialgebra",
    "BialgebraAction",
    "DualBialgebra",
    "DualElement",
    "ConvolutionElement",
    "bialgebra",
    "getDeltaN", --We should hide the 
    "higherCoprod",
    "tensorProductNoGB",
    "isCoassociative",
    "isCounit",
    "isBialgebra", 
    "isCocommutative",
    "totalBasis",
    "findLeftIntegral",
    "findGrouplikes", 
    "findAntipode",
    "applyAntihomomorphism",
    "bialgebraAction",
    "actOn",
    "actionInDegree",
    "invariantInDegree", 	
    "invariantAlgebraGens",
    "invariantAlgebra",
    "RelDegreeLimit",
    "GenDegreeLimit",
    "inclusion", 
    "counit",
    "dualCoprod",
    "multMatrix",
    "dualBasis",
    "dualCounit",
    "dualize",
    "dualElement",
    "weightSpaceInDegree",
    "getNextDegWeights",
    "weightSpaceGens"}

protect atlas
protect generatorAction
protect actionCache
protect leftTens
protect rightTens
protect iota1
protect iota2
protect deltas
protect deltaImg
--protect multMap
protect coMult
protect mult
protect invarGens
protect invarAlg
--protect makeMonic

NCBialgebra = new Type of HashTable
BialgebraAction = new Type of HashTable
DualBialgebra = new Type of Ring
DualElement = new Type of HashTable
ConvolutionElement = new Type of HashTable

--- we need some functions from NCAlgebra that are not exported
debug NCAlgebra

makeMonic = method()
makeMonic NCRingElement := f -> (leadCoefficient f)^(-1)*f

fastBaseChange = method()
fastBaseChange(NCRing, NCRingElement, RingMap) := (B, f, phi) -> (
   -- B should be a NCRing which only differs from the
   -- ring of f in that one may promote elements of its
   -- coefficient ring to that of B.
   if (ring f).generatorSymbols != B.generatorSymbols then error "Expected same variables.";
   retVal := new B from {(symbol ring) => B,
       (symbol cache) => new CacheTable from {("isReduced",true)},
       (symbol terms) => new HashTable from apply(pairs f.terms, (k,v) -> (new NCMonomial from {(symbol monList) => k.monList, (symbol ring) => B}, phi v))};
   retVal
)

fastBaseChange (NCRing, NCRingElement) := (B, f) -> (
   phi := map(coefficientRing B, coefficientRing ring f);
   fastBaseChange(B,f,phi)
)

createSubscriptRing = method()
createSubscriptRing (NCRing, ZZ) :=  (A, n) -> (
   -- this ring creates a `copy' of A but with the variables
   -- doubly subscripted with last entry n, and the first subscript the variable number.

   R := coefficientRing A;
   I := ideal A;
   ambA := ambient A;
   xx := getSymbol "xx";
   newVars := apply(numgens A, i -> xx_(i+1,n));   
   
   ambB := R newVars;
   phi := ncMap(ambB, ambA, gens ambB);
   newI := ncIdeal ((gens I) / phi);
   if class A === NCPolynomialRing then ambB else (
       newI.cache#gb = ncGroebnerBasis((gens (I.cache#gb)) / phi, InstallGB => true);
       ambB/newI
   )
)

createSubscriptRing (NCBialgebra, ZZ) := (B,n) -> createSubscriptRing(B.ring,n)

tensorProductNoGB = method()
tensorProductNoGB(NCRing, NCRing) := (A1,A2) -> (
   R := coefficientRing A1;
   if coefficientRing A2 =!= R then error "Expected the same coefficient ring.";
   
   A1gens := (gens A1) / baseName;
   A2gens := (gens A2) / baseName;
   newA := R (A1gens | A2gens);
   newA1gens := take(gens newA,numgens A1);
   newA2gens := drop(gens newA,numgens A1);
   phi := ncMap(newA,ambient A1,newA1gens);
   psi := ncMap(newA,ambient A2,newA2gens);
   commRules := flatten apply(newA1gens, x -> apply(newA2gens, y -> x*y - y*x));
   A1I := ideal A1;
   A2I := ideal A2;
   J := ncIdeal (((gens A1I) / phi) | ((gens A2I) / psi) | commRules);
   gbJGens := ((gens (A1I.cache#gb)) / phi) | ((gens (A2I.cache#gb)) / psi) | commRules;
  -- error "err";
   J.cache#gb = ncGroebnerBasis( gbJGens, InstallGB => true);
   A := newA/J;
   A.cache#(symbol iota1) = ncMap(A,A1,take(gens A, numgens A1));
   A.cache#(symbol iota2) = ncMap(A,A2,drop(gens A, numgens A1));
   A
)

tensorProductNoGB(NCRingMap,NCRingMap) := (f,g) -> (
   A1 := source f;
   A2 := source g;
   B1 := target f;
   B2 := target g;
   A12 := tensorProductNoGB(A1,A2);
   B12 := tensorProductNoGB(B1,B2);
   ncMap(B12,A12,((flatten entries matrix f) / B12.cache#iota1) | ((flatten entries matrix g) / B12.cache#iota2))
)

bialgebra = method()
bialgebra (NCRing, List, List) := (A, deltaOutput, augOutput) -> (
   A1 := createSubscriptRing(A,1);
   A2 := createSubscriptRing(A,2);
   tensA := tensorProductNoGB(A1,A2);
   --tensA.cache#1 = A1;
   --tensA.cache#2 = A2;
   phi1 := ncMap(tensA,A,take(gens tensA, numgens A));
   phi2 := ncMap(tensA,A,drop(gens tensA, numgens A));
   delta := ncMap(tensA, A1, apply(deltaOutput, d -> sum apply(d, t -> (phi1(t#0))*(phi2(t#1)))));
   --epsilon := ncMap(coefficientRing A, A, augOutput);
   B := new NCBialgebra from {(symbol ring) => A,
			      (symbol counit) => ncMap(A,A,augOutput),
			      (symbol deltas) => new MutableHashTable from {(1,delta)},
			      (symbol inclusion) => ncMap(A1,A,gens A1),
			      --(symbol multMap) => ncMap(A,tensA,(gens A) | (gens A)),
			      -- Do leftTens and rightTens deserve to live here? Should they have better names?
			      (symbol leftTens) => ncMap(A, tensA, gens A | apply(numgens A, i -> 1_A)),
			      (symbol rightTens) => ncMap(A, tensA, apply(numgens A, i -> 1_A) | gens A),
			      (symbol deltaImg) => deltaOutput,
			      (symbol cache) => new CacheTable from {}};
   B
)

ring NCBialgebra := B -> B.ring

counit = method()
counit NCBialgebra := B -> B.counit

inclusion = method()
inclusion NCBialgebra := B -> B.inclusion

bialgebra NCRing := A -> (
   --- This method constructs a bialgebra using the group bialgebra structure
   gensA := gens A;
   protodOutput := apply((pairs gensA), e -> apply(e, i -> e#1));
   dOutput := toList apply(protodOutput, e-> {e});
   aOutput := apply(#gensA, i -> 1_A);
   B := bialgebra(A,dOutput,aOutput);
   B
)

getDeltaN = method()
getDeltaN(NCBialgebra,ZZ) := (B,n) -> (
   --- this function returns the n^th iterate of Delta from H1 to H1\otimes H2\otimes\cdots\otimes Hn
   --- If it has already been computed, it returns it.  If not, the code stashes it (as well as all the
   --- intermediate steps)
   if n <= 0 then error "Expected positive integer"; 
   if B.deltas#?n then return B.deltas#n;
   --- if here, the map has not yet been built.
   DeltaNMinus1 := getDeltaN(B,n-1);
   Delta1 := getDeltaN(B,1);
   BNPlus1 := createSubscriptRing(B,n+1);
   --- the second factor is cached as the source of the inclusion map into B12
   B2 := source ((target B.deltas#1).cache#iota2);
   psi := ncMap(BNPlus1,B2,gens BNPlus1);
   deltaN := tensorProductNoGB(DeltaNMinus1,psi);
   DeltaN := deltaN @@ (ncMap(source deltaN, target Delta1, gens source deltaN)) @@ Delta1;
   B.deltas#n = DeltaN;
   DeltaN
)

higherCoprod = method()
higherCoprod (NCBialgebra, ZZ) := (B, n) -> (
   --- this method returns the nth coproduct as a NCRingMap from B to B^{\otimes n+1}
   --- which also involves building the rings in question
   --- it does so recursively
   DeltaN := getDeltaN(B,n);
   DeltaN @@ B.inclusion
)

isCoassociative = method()
isCoassociative NCBialgebra := B -> (
   Delta2L := getDeltaN(B,2);
   delta1 := B.deltas#1;
   B1 := source delta1;
   B2 := source ((target delta1).cache#iota2);
   B3 := source ((target B.deltas#2).cache#iota2);
   B23 := tensorProductNoGB(B2,B3);
   B12 := target delta1;
   psi3 := ncMap(B23,B12,gens B23);
   psi2inv := ncMap(B1,B2,gens B1);
   delta2R := tensorProductNoGB(ncMap(B1,B1,gens B1), psi3 @@ delta1 @@ psi2inv);
   Delta2R := delta2R @@ (ncMap(source delta2R, target delta1, gens source delta2R)) @@ delta1;
   phi := ncMap(target Delta2R, target Delta2L, gens target Delta2R);
   matrix Delta2R == phi matrix Delta2L
)

isCounit = method()
isCounit NCBialgebra := B -> (
   H := B.ring;
   H12 := target B.deltas#1;
   mu := ncMap(H,H12, gens H | gens H);
   eps12 := (values B.counit.functionHash) / B.deltas#1 @@ B.inclusion;
   epsLeft := ncMap(H12,H12, eps12 | drop(gens H12,numgens H));
   epsRight := ncMap(H12,H12, take(gens H12,numgens H) | eps12); -- requires H.counit to be elements of H!
   idH := ncMap(H,H,gens H);
   epsTimesId := mu @@ epsLeft @@ B.deltas#1 @@ B.inclusion;
   idTimesEps := mu @@ epsRight @@ B.deltas#1 @@ B.inclusion;
   (matrix epsTimesId == matrix idH) and (matrix idTimesEps == matrix idH)
   --- Checks that (id \otimes counit) \circ \Delta = id and (counit \otimes id) \circ \Delta = id.
)

isBialgebra = method()
isBialgebra NCBialgebra := B -> (
  --- isWellDefined on comultiplication
  --- isCounit and isCoassociative
  isWellDefined B.deltas#1 and isCounit B and isCoassociative B
)

isCocommutative = method()
isCocommutative NCBialgebra := B -> (
   --- to check cocommutativity only need to check generators
   H := B.ring;
   H12 := target B.deltas#1;
   twistMap := ncMap(H12,H12, drop(gens H12,numgens H) | take(gens H12,numgens H));
   comultWithTwist := twistMap @@ B.deltas#1 @@ B.inclusion;
   comultWithoutTwist := B.deltas#1 @@ B.inclusion;
   (matrix comultWithTwist) == (matrix comultWithoutTwist)
)

totalBasis = method(Options => {DegreeLimit => 10})
totalBasis NCRing := opts -> H -> (
   if H.cache#?basis then return H.cache#basis;
   basisH := ncMatrix{select(apply(opts#DegreeLimit, i -> basis(i,H)), m -> m != 0)};
   H.cache#basis = basisH;
   basisH
)

totalBasis NCBialgebra := opts -> B -> totalBasis(B.ring, opts)

coprodImg = method() 
coprodImg (List, NCBialgebra) := (eltList,B) -> (
   --- This method takes an NCBialgebra and a list of NCBialgebra elements, and returns list of their coproducts
   if any(eltList, m -> not instance(m,B.ring)) then error "Expected list of ring elements.";
   apply(eltList, m -> apply(terms (B.deltas#1 B.inclusion m), t -> (B.leftTens t, (leadCoefficient t)^(-1)*(B.rightTens t))))
)

comultMatrix = method(Options => {DegreeLimit => 10})
comultMatrix NCBialgebra := opts -> B -> (
   --- Returns a matrix representation of the coproduct with respect to the basis calculated by Macaulay
   if B.cache#?coMult then return B.cache#coMult;
   H := B.ring;
   basisH := flatten entries totalBasis(H,opts);
   coprodBasis := coprodImg(basisH, B);
   comultMat := matrix{apply(coprodBasis, coprod -> 
      sum apply(coprod, t -> sparseCoeffs(t#0, Monomials => basisH) ** sparseCoeffs(t#1, Monomials => basisH)))}; -- this line is too long and I don't know how to make it shorter
   B.cache#coMult = comultMat;
   comultMat
)

multMatrix = method(Options => {DegreeLimit => 10})
multMatrix NCBialgebra := opts -> B -> (
   if B.cache#?mult then return B.cache#mult;
   H := B.ring;
   basisH := flatten entries totalBasis(H,opts);
   matrix {apply(basisH, m -> totalLeftMultMap(m, B))}
)

dualCoprod = method(Options => {DegreeLimit => 10})
dualCoprod DualElement := opts -> a -> (
   aMat := a.matrix;
   B := a.ring.bialgebra;
   aMat * multMatrix(B,opts)
)

totalLeftMultMap = method()
totalLeftMultMap (NCRingElement, NCBialgebra) := (h,B) -> (
   basisH := flatten entries totalBasis B;
   output := apply(basisH, f -> h*f);
   sparseCoeffs(output, Monomials => basisH)
)

findLeftIntegral = method(Options => {DegreeLimit => 10}) --- Do we really use DegreeLimit here?
findLeftIntegral NCBialgebra := opts -> B -> (
   H := B.ring;
   basisH := totalBasis(B,opts);
   n := #(basisH.source);
   kk := coefficientRing H;
   matList := apply(gens H, x -> totalLeftMultMap(x,B)-leadCoefficient(B.counit x)*id_(kk^n));
   intCoeff := gens ker matrix apply(matList, m -> {m});
   leftInt := first first entries (basisH*intCoeff);
   --leftInt := sum apply(n, i-> ((keys action#atlas)#i)*(intCoeff_(i,0)));
   leftInt
)

extendCoeffRing = method() 
extendCoeffRing (NCBialgebra, ZZ, Symbol) := (B,n,c) -> (
   H := B.ring;
   I := ideal H; 
   A := ambient H;
   --n := #((totalBasis H).source);
   kk := (A.CoefficientRing)[c_1..c_n];
   newA := kk(H.generatorSymbols);
   toNewA := ncMap(newA,A,gens newA);
   newI := ncIdeal ((I.generators)/toNewA);
   newIgb := ncGroebnerBasis((gens I.cache#gb) / toNewA, InstallGB => true); -- This isn't how we should actually handle this...
   newI.cache#gb = newIgb;
   newH := newA/newI;
   toNewH := ncMap(newH,H, gens newH);
   newDeltaOutput := apply(B.deltaImg, l -> apply(l, m -> apply(m, n -> toNewH n)));
   bialgebra(newH,newDeltaOutput,(values B.counit#functionHash)/toNewH)
   )

extendCoeffRing2 = method() 
extendCoeffRing2 (NCBialgebra, ZZ, Symbol) := (B,n,c) -> (
   H := B.ring;
   I := ideal H; 
   A := ambient H;
   --n := #((totalBasis H).source);
   kk := (A.CoefficientRing)[c_1..c_n];
   newA := kk(H.generatorSymbols);
   phi := map(kk, coefficientRing A);
   toNewA := f -> fastBaseChange(newA, f, phi);
   newI := ncIdeal ((I.generators)/toNewA);
   newIgb := ncGroebnerBasis((gens I.cache#gb) / toNewA, InstallGB => true); -- This isn't how we should actually handle this...
   newI.cache#gb = newIgb;
   newH := newA/newI;
   toNewH := f -> fastBaseChange(newH, f, phi);
   newDeltaOutput := apply(B.deltaImg, l -> apply(l, m -> apply(m, n -> toNewH n)));
   bialgebra(newH,newDeltaOutput,(values B.counit#functionHash)/toNewH)
   )

addRootsOfUnity = method()
addRootsOfUnity (NCBialgebra, ZZ, Symbol) := (B,n,c) -> (
   H := B.ring;   
   I := ideal H; 
   A := ambient H;
   --n := #((totalBasis H).source);
   kk := (A.CoefficientRing);
   newA := kk(H.generatorSymbols);
   toNewA := ncMap(newA,A,gens newA);
   newI := ncIdeal ((I.generators)/toNewA);
   newIgb := ncGroebnerBasis(newI, InstallGB => true); -- This isn't how we should actually handle this...
   newH := newA/newI;
   toNewH := ncMap(newH,H, gens newH);
   newDeltaOutput := apply(B.deltaImg, l -> apply(l, m -> apply(m, n -> toNewH n)));
   bialgebra(newH,newDeltaOutput,(values B.counit#functionHash)/toNewH)
)

findGrouplikes = method(Options => {DegreeLimit => 10})
findGrouplikes NCBialgebra := opts -> H -> (
   c := getSymbol "cc";
   basisH := totalBasis(H,opts);
   Hc := extendCoeffRing(H, #(basisH.source), c);
   basisHc := totalBasis Hc;
   kk := coefficientRing Hc.ring;
   varsAmbient := transpose matrix {gens kk};
   g := first flatten entries (basisHc*varsAmbient);
   deltag := Hc.deltas#1 Hc.inclusion g;
   Hc12 := target Hc.deltas#1;
   Hc1 := source Hc12.cache#iota1;
   Hc2 := source Hc12.cache#iota2;
   phi1 := ncMap(Hc1,Hc.ring,gens Hc1);
   phi2 := ncMap(Hc2,Hc.ring,gens Hc2);
   gtensg := (Hc12.cache#iota1 phi1 g)*(Hc12.cache#iota2 phi2 g);
   basisHc12 := totalBasis Hc12;
   gpLikeCoeffs := sparseCoeffs(deltag - gtensg, Monomials => flatten entries basisHc12);
   J := (ideal gpLikeCoeffs) + ideal ((leadCoefficient Hc.counit g) - 1_kk);
   primDec := primaryDecomposition radical J;
   apply(primDec, p -> first flatten entries ((basisH)*transpose sub(matrix {gens (kk/p)}, coefficientRing H.ring)))
)

applyAntihomomorphism = method()
applyAntihomomorphism (NCRingMap, NCRingElement) := (S, f) -> (
   --- apply the function S to the element f as an antihomomorphism.
   if ring f =!= source S then error "Expected an element of the domain of S.";
   A := ring f;
   matS := flatten entries matrix S;
   genHash := hashTable apply(numgens A, i -> ((A.generatorSymbols)#i, matS#i));
   sum apply(pairs (f.terms), (m,c) -> c*(product apply(reverse m.monList, x -> genHash#x)))
)

findAntipode = method()
findAntipode NCBialgebra := H -> (
   B := H.ring;
   basisH := totalBasis H;
   n := #(flatten entries basisH);
   
   -- trying to speed things up a bit
   --elapsedTime Hbig := extendCoeffRing(H,n*(numgens B),getSymbol "xxx");
   Hbig := extendCoeffRing2(H,n*(numgens B),getSymbol "xxx");
   
   -- trying to speed things up a bit
   --phi := ncMap(Hbig.ring, H.ring, gens Hbig.ring);
   --elapsedTime basisHbig := phi basisH;
   psi := map(coefficientRing Hbig.ring, coefficientRing H.ring);
   phi := f -> fastBaseChange(Hbig.ring, f, psi);
   basisHbig := ncMatrix applyTable(entries basisH, phi);
   
   coeffRing := coefficientRing Hbig.ring;
   genericAntipodes := apply(numgens B, i -> first flatten entries (basisHbig*(transpose (vars coeffRing)_(toList((i*n)..((i+1)*n-1))))));
   S := ncMap(Hbig.ring, Hbig.ring, genericAntipodes);

   -- this is the slowest part of this function.
   convolveSId := apply(numgens B, i -> sum apply(Hbig.deltaImg#i, p -> applyAntihomomorphism(S,p#0)*(p#1)) - Hbig.counit (Hbig.ring)_i);

   convCoeffs := sparseCoeffs(convolveSId, Monomials => flatten entries basisHbig);
   --antipodeCoeffs := pack((gens (coeffRing/(first primaryDecomposition radical ideal convCoeffs)) / leadCoefficient),n);
   antipodeCoeffs := pack((gens (coeffRing/(ideal convCoeffs)) / leadCoefficient),n);
   antipodeOutput := apply(numgens B, i -> first flatten entries (basisH*(transpose matrix {antipodeCoeffs#i})));
   --error "err";
   ncMap(H.ring, H.ring, antipodeOutput)
)

--- can we write code to determine if an antipode exists?

----- Bialgebra action code

bialgebraAction = method(Options => {DegreeLimit => 10})
bialgebraAction (NCBialgebra,NCRing,List) := opts -> (B,R, mapList) -> (
   --- B bialgebra acting on R
   --- mapList is a list of either NCRingMaps or matrices over the coefficient ring of R
   --- that define the action of the generators of B on the generators of R
   --- 
   if length(mapList) =!= numgens B.ring then error "Action definition incomplete";
   if any(mapList, f -> class f =!= NCRingMap) then error "Expected a list of NCRingMaps.";
   aRing := source first mapList; --- This seems redundant. 
   basisB := flatten apply(opts#DegreeLimit, i -> flatten entries basis(i,B.ring));
   -- Can't we just use totalBasis in the line above? Maybe we hadn't written it yet...
   genActionHash := new HashTable from apply(numgens B.ring, i -> ((B.ring.generatorSymbols)#i, mapList#i));
   myAtlas := new HashTable from {(first basisB,ncMap(aRing,aRing,gens aRing))} |
                                  apply(drop(basisB,1), m -> (m, product apply((first first pairs (m.terms)).monList, a -> genActionHash#a)));
   actCache := new HashTable from apply(basisB, m-> (m,new  MutableHashTable from {}));
   A := new BialgebraAction from {(symbol bialgebra) => B,
       	       	       	       	  (symbol ring) => aRing,
				  (symbol generatorAction) => genActionHash,
				  (symbol atlas) => myAtlas,
			          (symbol actionCache) => actCache,
                 		  (symbol cache) => new CacheTable from {}};
   A
)

ambient BialgebraAction := action -> (
   --- lifts the action of action.bialgebra from action.ring to its ambient tensor algebra.
   K := action.ring;
   L := ambient K;
   phi := ncMap(L, K, gens L);
   --- not sure how this code ever worked actually - hash tables needn't be
   --- sorted, but bialgebraAction requires its input to be sorted in the appropriate order.
   --- this showed up when listing variables in non-alphabetical order when defining the algebra
   bialgebraAction(action.bialgebra, L, apply(action.bialgebra.ring.generatorSymbols, var -> phi @@ (ambient action.generatorAction#var)))
)

isWellDefined BialgebraAction := action -> (
   --- is the ideal sent to itself under the Hopf action?
   ambAction1 := ambient action;
   defIdeal := ideal action.ring;
   gbDefIdeal := ncGroebnerBasis defIdeal;
   isIdealPreserved := all(gens (action.bialgebra.ring), x -> all(gens defIdeal, f -> (actOn(x,f,ambAction1) % gbDefIdeal) == 0));
   --- is the action on the degree 1 part of action.ring a module over action.bialgebra?
   defIdealH := ideal (action.bialgebra.ring);
   genMatrices := apply(gens action.bialgebra.ring, x -> (action.atlas#x)_1);
   isHModule := all(gens defIdealH, f -> matrixSub(f,genMatrices) == 0);
   isIdealPreserved and isHModule
)

matrixSub = method()
matrixSub (NCRingElement, List) := (f, mats) -> (
   if numgens ring f != #mats then error "Expected a matrix for each generator of the ring of the first input.";
   A := ring f;
   genHash := hashTable apply(numgens A, i -> ((A.generatorSymbols)#i, mats#i));
   sum apply(pairs (f.terms), (m,c) -> c*(product apply(m.monList, x -> genHash#x)))
)

actOnDegreeOne = method()
actOnDegreeOne (NCRingElement, NCRingElement, BialgebraAction) := (h,x,action) -> (
   if degree x != 1 then error "Wrong function called for action on elements of degree greater than one.";
   hTerms := terms h;
   hCoeffs := hTerms / leadCoefficient;
   hMons := hTerms / leadMonomial;
   sum apply(#hTerms, i -> (hCoeffs#i)*((action#atlas)#(hMons#i) x))
)

factorMonomial = method()
factorMonomial NCRingElement := m -> (
   monList := (first first pairs (m.terms)).monList;
   halfOf := floor(#monList/2);
   (putInRing(take(monList,halfOf),ring m, 1), putInRing(drop(monList,halfOf),ring m, 1))
)


actOnQuadMon = method() -- Is this unnessisary at this point? 
actOnQuadMon (NCRingElement, NCRingElement, BialgebraAction) := (h,m,action) -> (
   if degree m != 2 then error "Wrong function called for action on elements of degree not two.";
   if #(terms m) != 1 then error "Wrong function called for action on non-monomial element.";
   H := action.bialgebra;
   mCoeff := leadCoefficient(m);
   mFactor := factorMonomial(m);
   dh := H.deltas#1 H.inclusion h;
   dhTerms := terms dh;
   dhCoeffs := dhTerms / leadCoefficient;
   dhMons := dhTerms / leadMonomial;
   dhMonsL := apply(dhMons, i-> H.leftTens(i));
   dhMonsR := apply(dhMons, i-> H.rightTens(i));
   sum(apply(#dhTerms, i -> (dhCoeffs#i)*actOnDegreeOne(dhMonsL#i,mFactor#0,action)*actOnDegreeOne(dhMonsR#i,mFactor#1,action)))*mCoeff
)
    
actOn = method()
actOn (NCRingElement, NCRingElement, BialgebraAction) := (h,m,action) -> (
   --- employ actOnMonomial to handle sums of elements from hopf algebra and ring, as well as coefficients from ring
   --if h.ring =!= action.bialgebra or f.ring =!= action.ring then error "Expected elements in rings defined by bialgebra action.";
   mTerms := terms m;
   mCoeffs := mTerms / leadCoefficient;
   mMons := mTerms / leadMonomial;
   hTerms := terms h;
   hCoeffs := hTerms / leadCoefficient;
   hMons := hTerms / leadMonomial;
   sum flatten apply(#hCoeffs, i -> apply(#mCoeffs, j -> hCoeffs#i*mCoeffs#j*actOnMonomial(hMons#i,mMons#j,action)))  
   --sum apply(#mTerms, i -> (mCoeffs#i)*actOnMonomial(h,mTerms#i,action))
)

actOnMonomial = method()
actOnMonomial (NCRingElement, NCRingElement, BialgebraAction) := (h,m,action) -> (
   --- assumes f is a monomial in the basis given by Macaulay2 induced by the
   --- Groebner bases computed previously.
   --- this function will be recursive based on the 'tensor length' of f.
   --- we want to restrict h to a basis element of H
   H := action.bialgebra;   
   if #(terms m) != 1 then error "Wrong function called for action on non-monomial element.";
   if (degree m) === 1 then return actOnDegreeOne(h,m,action);
   if (degree m) === 0 then return (leadCoefficient H.counit(h))*m;
   if ((action.actionCache)#h)#?m then return ((action.actionCache)#h)#m;
   --mCoeff := leadCoefficient(m);
   mFactor := factorMonomial(m);
   dh := H.deltas#1 H.inclusion h;
   dhTerms := terms dh;
   dhCoeffs := dhTerms / leadCoefficient;
   dhMons := dhTerms / leadMonomial;
   dhMonsL := apply(dhMons, i-> H.leftTens(i));
   dhMonsR := apply(dhMons, i-> H.rightTens(i));
   val:=sum(apply(#dhTerms, i -> (dhCoeffs#i)*actOnMonomial(dhMonsL#i,mFactor#0,action)*actOnMonomial(dhMonsR#i,mFactor#1,action)));   
   ((action.actionCache)#h)#m = val;
   val
)

actionInDegree = method()
actionInDegree (NCRingElement, BialgebraAction, ZZ) := (h,action,n) -> (
   K := action.ring;
   basisK := flatten entries basis(n,K);
   actOnBasis := apply(basisK, m -> actOn(h,m,action));
   sparseCoeffs(actOnBasis,Monomials=>basisK)
)


invariantInDegree = method(Options => {Strategy => 0})
invariantInDegree (BialgebraAction, ZZ) := opts -> (action, n) -> (
   --- This method computes invariants using the intersection
   --- of kernels trick
   if opts#Strategy != 0 then return invariantInDegreeAlt(action,n);
   B := action.bialgebra;
   H := B.ring;
   K := action.ring;
   basisK := basis(n,K);
   kk := coefficientRing K;
   matList := apply(gens H, x -> actionInDegree(x,action,n) - leadCoefficient(B.counit x)*id_(kk^(#(basisK.source))));
   pruneKer := prune ker matrix apply(matList, m -> {m});
   invCoeffs := gens image pruneKer.cache.pruningMap;
   flatten entries (basisK*invCoeffs)
)


invariantInDegreeAlt = method()
invariantInDegreeAlt (BialgebraAction, ZZ) := (action, n) -> (
   --- This method computes invariants using (left) integrals
   H := action.bialgebra;
   A := action.ring;
   int :=findLeftIntegral(H);
   basisA := basis(n,A);
   mat := sparseCoeffs(apply(flatten entries basisA, a -> actOn(int,a,action)),Monomials=>flatten entries basisA);
   columnBasis  := mingens image mat;
   flatten entries (basisA*columnBasis)
)

getNextDegInvar = method()
getNextDegInvar (BialgebraAction,List,ZZ) := (action, gensSoFar, n) -> (
   H := action.bialgebra;
   R := action.ring;
   B := H.ring;
   c := getSymbol "cc";
   kk := coefficientRing B;
   KK := kk{c_1..c_#gensSoFar};
   phi := ncMap(R,KK,gensSoFar);
   setWeights(KK,apply(gensSoFar, n-> degree n));
   potentialGens := invariantInDegree(action, n);
   if potentialGens == {} then return {};
   potentialGensCoeffs := sparseCoeffs(potentialGens,Monomials=> flatten entries basis(n,R));
   newGensQuot := prune ((image potentialGensCoeffs)/(image phi_n));
   if newGensQuot == 0 then return {};
   newGens := (flatten entries (basis(n,R)*(gens image newGensQuot.cache.pruningMap))) / makeMonic;
   newGens
)


invariantAlgebraGens = method((Options => {DegreeLimit => 10})) 
invariantAlgebraGens BialgebraAction := opts -> action -> (
   if action.cache#?invarGens then return action.cache.invarGens;
   i := 1;
   gensSoFar := {};
   while #gensSoFar < 1 and i <= opts#DegreeLimit do (gensSoFar = invariantInDegree(action,i); i = i+1); 
   if i == opts#DegreeLimit then return gensSoFar;
   while i <= opts#DegreeLimit do (
       gensSoFar = gensSoFar|(getNextDegInvar(action,gensSoFar,i));
       i = i+1;
       );
   action.cache.invarGens = gensSoFar;
   gensSoFar
)

invariantAlgebra = method(Options => {GenDegreeLimit => 10, RelDegreeLimit => infinity, InstallGB => false})
invariantAlgebra (BialgebraAction,Symbol) := opts -> (action,c) -> (
   if action.cache#?invarAlg then return action.cache.invarAlg;
   relDegLimit := opts#RelDegreeLimit;
   if relDegLimit == infinity then relDegLimit = 2*opts#GenDegreeLimit;
   invAlgGens := invariantAlgebraGens(action, DegreeLimit => opts#GenDegreeLimit);
   kk := coefficientRing action.ring;
   if invAlgGens == {} then return kk;
   KK := kk{c_1..c_#invAlgGens};
   setWeights(KK, invAlgGens/degree);
   phi := ncMap(action.ring, KK, invAlgGens);
   kerGens := gddKernel(relDegLimit, phi);
   I := ncIdeal(kerGens);
   Igb := ncGroebnerBasis(I, InstallGB => opts#InstallGB);
   R := if kerGens == {} then KK else KK/I;
   R.cache#(symbol presentation) = ncMap(action.ring, R, invAlgGens);
   R.cache#(symbol GenDegreeLimit) = opts#GenDegreeLimit;
   R.cache#(symbol RelDegreeLimit) = relDegLimit;
   action.cache#(symbol invarAlg) = R;
   R
)

--- Dual structure 
new DualBialgebra from List := (DualBialgebra, inits) -> new DualBialgebra of DualElement from new HashTable from inits

dualize = method(Options => {DegreeLimit => 10})
dualize NCBialgebra := opts -> B -> (
   basisA := dualBasis(B,opts);
   A := new DualBialgebra from {(symbol bialgebra) => B,
                                (symbol ring) => null,
				(symbol basis) => basisA,
                                (symbol cache) => new CacheTable from {}};
   
   A + A := (phi,psi) -> dualElement(A,(phi.matrix + psi.matrix));
   A * A := (phi,psi) -> dualProd(phi,psi);
   A ** A := (phi,psi) -> (
       R := ring (phi.matrix);
       zeroDegree := degree (1_R);
       temp := (phi.matrix)**(psi.matrix);
       map(R^{zeroDegree},R^(toList((#basisA)^2:zeroDegree)),entries temp)
   );    
   A == A := (phi,psi) -> (phi.ring == psi.ring) and (phi.matrix == psi.matrix);
   A ^ ZZ := (phi,n) -> product apply(n, i-> phi);
   k := coefficientRing ((A.bialgebra).ring);
   k*A := (c,phi) -> dualElement(A,(c*(phi.matrix)));
   A*k := (phi,c) -> dualElement(A,((phi.matrix)*c));
   ZZ*A := (c,phi) -> promote(c,k)*phi;
   A*ZZ := (phi,c) -> phi*(promote(c,k));
   QQ*A := (c,phi) -> promote(c,k)*phi;
   A*QQ := (phi,c) -> phi*(promote(c,k));
   A
)

DualBialgebra == DualBialgebra := (A,B) -> (A.bialgebra === B.bialgebra) and (#(A.basis) == #(B.basis));

dualElement = method(Options => {DegreeLimit => 10})
dualElement (DualBialgebra, Matrix) := opts -> (dualB,mat) -> (
   if (numgens target mat) != 1 then error "Expected row vector";
   B := dualB.bialgebra;
   basisB := flatten entries totalBasis(B,opts);
   if (numgens source mat) != #basisB then error "Row vector source does not match bialgebra"; -- Not sure what to actually say here
   new dualB from hashTable {(symbol matrix) => mat,
                             (symbol ring) => dualB}
)

net DualElement := de -> net de.matrix

ncMap DualElement := opts -> phi -> (
    
   H := ((phi.ring).bialgebra).ring;
   kk := coefficientRing H;
   basisH := flatten entries totalBasis H;
   gensH := gens H;
   gensAddress := apply(gensH, h -> position(basisH, j -> h == j));
   gensImage := apply(flatten entries (sub(phi.matrix_gensAddress,kk)), c -> c_H);
   ncMap(H, H, gensImage / (i -> if i === 0 then i_H else i))
)

dualBasis = method(Options => {DegreeLimit => 10}) 
dualBasis NCRing := opts -> H -> (
   --- This method takes an NCRing, computes a basis and outputs a basis of the dual, 
   --- considered as row vectors.
   basisH := flatten entries totalBasis(H,opts);
   kk := coefficientRing H;
   apply(#basisH, i -> (id_(kk^(#basisH)))^{i}) 
)

dualBasis NCBialgebra := opts -> B -> dualBasis(B.ring,opts)
   
dualCounit = method()
dualCounit DualElement := f -> (f.matrix)_(0,0)

dualUnit = method(Options => {DegreeLimit => 10})
dualUnit DualBialgebra := opts -> B -> (
   --- This method is the counit of a bialgebra, considered as a function
   basisB := flatten entries totalBasis(B,opts);
   eps := B.counit;
   imgList := apply(basisB, x -> leadCoefficient eps x);
   matrix{imgList}
)

dualProd = method()
dualProd (DualElement,DualElement) := (phi,psi) -> (
   a := phi.matrix;
   b := psi.matrix;
   if (phi.ring != psi.ring) then error "Expected elements from the same dual space.";
   ---if (not phi.ring === psi.ring) then error "Expected elements from the same dual space.";
   comultMat := comultMatrix (phi.ring).bialgebra;
   prodMat := (a**b)*comultMat;
   dualElement(phi.ring,prodMat)
)

--- oneDimensionalRepresentations
findGrouplikes DualBialgebra := opts -> H' -> (
   basisH := totalBasis(H'.bialgebra,opts);
   n := #(flatten entries basisH);
   cc := getSymbol "cc";
   bigH := extendCoeffRing(H'.bialgebra,n,cc);
   R := coefficientRing (bigH.ring);
   bigH' := dualize bigH;
   phi := ncMap(bigH.ring,H'.bialgebra.ring,gens bigH.ring);
   basisBigH := phi basisH;
   gen1 := dualElement(bigH', vars R);
   temp := dualCoprod gen1 - (gen1.matrix ** gen1.matrix);
   grouplikeList := primaryDecomposition radical (ideal sub(temp,R) + ideal sub(dualCounit gen1 - 1_R, R));
   highDegreePolys := select(flatten (grouplikeList / gens / entries / flatten), f -> first degree f > 1);
   if any(highDegreePolys, f -> first degree f > 1) then
      << "Warning: The following polynomials did not factor completely: " << highDegreePolys << "." << endl;
   grouplikeList = select(grouplikeList, f -> #(flatten entries basis (R/f)) == 1);
   oneDimRepRowVecs := apply(grouplikeList, p -> dualElement(H',sub(matrix entries sub(gen1.matrix, R/p),R)));
   --highDegreePolys
   oneDimRepRowVecs
)

weightSpaceInDegree = method()
weightSpaceInDegree (BialgebraAction, ZZ, DualElement) := (action, n, phi) -> (
   --- This method computes invariants using the intersection
   --- of kernels trick
   B := action.bialgebra;
   ---if (phi.ring).bialgebra != B then error "Expected linear functional from the dual";
   phiMap := ncMap phi;
   if not isWellDefined phiMap then error "Provided linear functional is not a valid representation.";
   H := B.ring;
   K := action.ring;
   basisK := basis(n,K);
   kk := coefficientRing K;
   matList := apply(gens H, x -> actionInDegree(x,action,n) - leadCoefficient(phiMap x)*id_(kk^(#(basisK.source))));
   pruneKer := prune ker matrix apply(matList, m -> {m});
   invCoeffs := gens image pruneKer.cache.pruningMap;
   wtGens := (flatten entries (basisK*invCoeffs)) / makeMonic;
   wtGens
)

getNextDegWeights = method()
getNextDegWeights (BialgebraAction,List,ZZ, DualElement) := (action, gensSoFar, n, phi) -> (
   H := action.bialgebra;
   R := action.ring;
   B := H.ring;
   d := getSymbol "dd";
   invAlg := invariantAlgebra(action,d);
   basesOfDeg := apply(gensSoFar/degree, d -> (flatten entries basis(n-d, invAlg))/(invAlg.cache.presentation));
   -- How should we handle when there are no elements of a given degree in
   -- the invariant algebra?
--   basesOfDeg = apply(basesOfDeg, l -> if l == {} then l = {1_R});
   spanningInDeg := flatten apply(basesOfDeg,gensSoFar, (l,f) -> apply(l, g -> f*g));
   potentialGens := weightSpaceInDegree(action, n, phi);
   if potentialGens == {} then return {};
   potentialGensCoeffs := sparseCoeffs(potentialGens,Monomials=> flatten entries basis(n,R));
   if spanningInDeg == {} then return potentialGens;
   sparseSpanningInDeg := sparseCoeffs(spanningInDeg,Monomials=> flatten entries basis(n,R));
   newGensQuot := prune ((image potentialGensCoeffs)/(image sparseSpanningInDeg));
   if newGensQuot == 0 then return {};
   newGens := (flatten entries (basis(n,R)*(gens image newGensQuot.cache.pruningMap))) / makeMonic;
   newGens
)

weightSpaceGens = method((Options => {DegreeLimit => 10})) 
weightSpaceGens (BialgebraAction,DualElement) := opts -> (action,phi) -> (
   i := 0;
   gensSoFar := {};
   while #gensSoFar < 1 and i <= opts#DegreeLimit do (gensSoFar = weightSpaceInDegree(action,i,phi); i = i+1); 
   if i == opts#DegreeLimit then return gensSoFar;
   while i <= opts#DegreeLimit do (
       gensSoFar = gensSoFar|(getNextDegWeights(action,gensSoFar,i,phi));
       i = i+1;
       );
   gensSoFar
)
--load (currentFileDirectory | "HopfAlgebras/hopfAlgebrasDoc.m2")

end

xxxx

restart
needsPackage "HopfAlgebras"
uninstallPackage "HopfAlgebras"
installPackage "HopfAlgebras"
viewHelp HopfAlgebras


restart
load "hopfActions.m2"
-- this is H8
kk = toField(QQ[a]/ideal{a^2+1})
kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
cB = toCommPolyRing(H,8)
totalBasis H
findLeftIntegral H
L = kk{u,v}
J = ncIdeal {u^2 + v^2}
K = L/J
xAction = ncMap(K,K,{-u,v})
yAction = ncMap(K,K,{u,-v})
zAction = ncMap(K,K,{v,u})
action = bialgebraAction(H,K,{xAction,yAction,zAction})
R = invariantAlgebra(action,c,GenDegreeLimit => 4) 

gensSoFar = invariantInDegree(action,4)
getNextDegInvar(action,gensSoFar,7)
getNextDegInvar(action,gensSoFar,6)
gensSoFar = gensSoFar

invariantAlgebraGens(action)

restart
load "hopfActions.m2"
kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
G = bialgebra(B)
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
Hbig = extendCoeffRing(H,24,getSymbol "c")
phi = ncMap(Hbig.ring, H.ring, gens Hbig.ring)
basisH = totalBasis H
n = #(flatten entries basisH)
basisHbig = phi basisH
coeffRing = coefficientRing Hbig.ring
genericAntipodes = apply(numgens B, i -> first flatten entries (basisHbig*(transpose (vars coeffRing)_(toList((i*n)..((i+1)*n-1))))))
S = ncMap(Hbig.ring, Hbig.ring, genericAntipodes)
convolveSId = apply(numgens B, i -> sum apply(Hbig.deltaImg#i, p -> applyAntihomomorphism(S,p#0)*(p#1)) - Hbig.counit (Hbig.ring)_i)
convCoeffs = sparseCoeffs(convolveSId, Monomials => flatten entries basisHbig)
antipodeCoeffs = pack((gens (coeffRing/(first primaryDecomposition radical ideal convCoeffs)) / leadCoefficient),8)
apply(numgens B, i -> first flatten entries (basisH*(transpose matrix {antipodeCoeffs#i})))

restart
load "hopfActions.m2"
-- this is H8
--kk = QQ[c_1..c_8]
kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
findGrouplikes H
varskk := transpose matrix {toList(c_1..c_8)}
g = first flatten entries ((totalBasis H)*varskk)
outg1 = H.deltas#1 H.inclusion g
H12 = target H.deltas#1
H1 = source H12.cache#iota1 
H2 = source H12.cache#iota2 
phi1 = ncMap(H1,H.ring,gens H1)
phi2 = ncMap(H2,H.ring,gens H2)
outg2 = (H12.cache#iota1 phi1 g)*(H12.cache#iota2 phi2 g)
basisH12 = totalBasis H12
gpLikeCoeffs = sparseCoeffs(outg1 - outg2, Monomials => flatten entries basisH12)
J = (ideal gpLikeCoeffs) + ideal ((leadCoefficient H.counit g) - 1_kk)
primDec = primaryDecomposition radical J
apply(primDec, p -> first flatten entries ((totalBasis H)*transpose sub(matrix {gens (kk/p)}, QQ)))

findGrouplikes H

restart
load "hopfActions.m2"
-- this is H8
kk = toField(QQ[a]/ideal{a^2+1})
kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
cB = toCommPolyRing(H,8)
totalBasis H
findLeftIntegral H
L = kk{u,v}
J = ncIdeal {u^2 + v^2}
K = L/J
xAction = ncMap(K,K,{-u,v})
yAction = ncMap(K,K,{u,-v})
zAction = ncMap(K,K,{v,u})
action = bialgebraAction(H,K,{xAction,yAction,zAction})
isWellDefined action
findLeftIntegral H
time invariantInDegree(action,22)
time invariantInDegree(action,22,alt=>true)
time invariantInDegree2(action,22)

--- compute algebra generating set
restart
load "HopfAlgebras.m2"
-- this is H8
kk = toField(QQ[a]/ideal{a^2+1})
kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
cB = toCommPolyRing(H,8)
totalBasis H
findLeftIntegral H
L = kk{u,v}
J = ncIdeal {u^2 + v^2}
K = L/J
xAction = ncMap(K,K,{-u,v})
yAction = ncMap(K,K,{u,-v})
zAction = ncMap(K,K,{v,u})
action = bialgebraAction(H,K,{xAction,yAction,zAction})
gensSoFar = invariantInDegree(action, 4)
c = getSymbol "cc"
C = kk{c_1..c_#gensSoFar}
setWeights(C, gensSoFar / degree)
phi = ncMap(K,C,gensSoFar)
potentialGens = invariantInDegree(action, 6)
gensSoFar = gensSoFar | potentialGens
c = getSymbol "cc"
C = kk{c_1..c_#gensSoFar}
setWeights(C, gensSoFar / degree)
phi = ncMap(K,C,gensSoFar)
potentialGens = invariantInDegree(action,8)
potentialGensCoeff = sparseCoeffs(potentialGens, Monomials => flatten entries basis(8,K))
(image potentialGensCoeff) / (image (phi_8))
mingens oo
potentialGens = invariantInDegree(action,10)
potentialGensCoeff = sparseCoeffs(potentialGens, Monomials => flatten entries basis(10,K))
(image potentialGensCoeff) / (image (phi_10))
mingens oo
ker phi_4
ker phi_6
ker8 = flatten entries (basis(8,C)*(mingens ker phi_8))
ker10 = flatten entries (basis(10,C)*(mingens ker phi_10))
D = C/ncIdeal(ker8 | ker10)
phi = ncMap(K,D,gensSoFar)
ker phi_12
flatten entries (basis(12,D)*(mingens ker phi_12))

restart
load "hopfActions.m2"
-- this is H8
kk = toField(QQ[a]/ideal{a^2+1})
kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
cB = toCommPolyRing(H,8)
totalBasis H
findLeftIntegral H
L = kk{u,v}
J = ncIdeal {u^2 - v^2}
K = L/J
xAction = ncMap(K,K,{-u,v})
yAction = ncMap(K,K,{u,-v})
zAction = ncMap(K,K,{v,u})
action = bialgebraAction(H,K,{xAction,yAction,zAction})
gensSoFar = invariantInDegree(action, 2)
c = getSymbol "cc"
C = kk{c_1..c_#gensSoFar}
setWeights(C, gensSoFar / degree)
phi = ncMap(K,C,gensSoFar)
potentialGens = invariantInDegree(action, 4)
potentialGensCoeff = sparseCoeffs(potentialGens, Monomials => flatten entries basis(4,K))
gensQuot = (image potentialGensCoeff) / (image (phi_4))
newGens = flatten entries (basis(4,K)*(mingens gensQuot))
gensSoFar = gensSoFar | newGens
c = getSymbol "cc"
C = kk{c_1..c_#gensSoFar}
setWeights(C, gensSoFar / degree)
phi = ncMap(K,C,gensSoFar)
potentialGens = invariantInDegree(action,6)
potentialGensCoeff = sparseCoeffs(potentialGens, Monomials => flatten entries basis(6,K))
(image potentialGensCoeff) / (image (phi_6))
mingens oo
potentialGens = invariantInDegree(action,8)
potentialGensCoeff = sparseCoeffs(potentialGens, Monomials => flatten entries basis(8,K))
(image potentialGensCoeff) / (image (phi_8))
mingens oo
potentialGens = invariantInDegree(action,10)
potentialGensCoeff = sparseCoeffs(potentialGens, Monomials => flatten entries basis(10,K))
(image potentialGensCoeff) / (image (phi_10))
mingens oo

ker phi_2
ker phi_4
ker6 = flatten entries (basis(6,C)*(mingens ker phi_6))
D = C/ncIdeal(ker6)
phi = ncMap(K,D,gensSoFar)
ker phi_8
ker phi_10
ker phi_12
ker phi_14

invariantInDegree(action,6)
C = skewPolynomialRing(kk,1_kk,{X,Y,Z})
setWeights(C,{4,4,6})
phi = ncMap(K,C,{u^4,(u*v)^2 - (v*u)^2, u^2*((u*v)^2 - (v*u)^2)})
isWellDefined phi
isHomogeneous phi
basis(12, C)*(gens ker phi_12)

actOnDegreeOne(z,u,action)
actOnDegreeOne(z,v,action)
actOnQuadMon(z,10000*u*u,action)
actOnQuadMon(z,(u*v),action)
actOnQuadMon(z,(v*u),action)
actOnQuadMon(z,v*v,action)
time actOnMonomial(z,(u*v)^50,action)
actOnMonomial(z,(v*u)^2,action)
actOnMonomial(z,(u*v)^2,action)
vv = (v*u)^2 + (u*v)^2
actOn(z,vv,action)
coefVec = ker ((totalLeftMultMap(x,action) - id_(QQ^8)) || (totalLeftMultMap(y,action) - id_(QQ^8)) || (totalLeftMultMap(z,action) - id_(QQ^8)))


restart
load "hopfActions.m2"
A = (ZZ/32003){t,u,v,w}
as = apply(8, i -> random(QQ))
bs = apply(8, i -> random(QQ))
f1 = (as#0)*(v^2+w^2) + (bs#0)*(u*t-t*u)
f2 = (as#1)*(v^2-w^2) + (bs#1)*(u*t+t*u)
f3 = (as#2)*(v*w+w*v) + (bs#2)*(u^2-t^2)
f4 = (as#3)*(v*w-w*v) + (bs#3)*(u^2+t^2)
f5 = (as#4)*(u*w+t*v) + (bs#4)*(v*t-w*u)
f6 = (as#5)*(u*w-t*v) + (bs#5)*(v*t+w*u)
f7 = (as#6)*(u*v+t*w) + (bs#6)*(v*u-w*t)
f8 = (as#7)*(u*v-t*w) + (bs#7)*(v*u+w*t)
allIs = apply(subsets({f1,f2,f3,f4,f5,f6,f7,f8},6), fs -> ncIdeal fs);
I = allIs#28
Igb = ncGroebnerBasis(I, DegreeLimit => 6)
B = A/I
hilbertSeries(B, Order => 6)
--allIgb = apply(allIs, I -> ncGroebnerBasis(I, DegreeLimit => 6);
--allBs = apply(allIs, I -> A/I);
--allHs = apply(allBs, B -> hilbertSeries(B, Order => 6))

restart
load "hopfActions.m2"
A = (ZZ/32003){t,u,v,w}
f1 = u*t-t*u
f2 = v^2-w^2
f3 = u^2-t^2
f4 = v*w-w*v
f5 = v*t-w*u
f6 = u*w-t*v
f7 = v*u-w*t
f8 = u*v-t*w
allIs = apply(subsets({f1,f2,f3,f4,f5,f6,f7,f8},6), fs -> ncIdeal fs);
allIgb = apply(allIs, I -> ncGroebnerBasis(I, DegreeLimit => 6));
allBs = apply(allIs, I -> A/I);
allHs = apply(allBs, B -> hilbertSeries(B, Order => 6));
netList allHs

I = ncIdeal {f2,f3,f5,f6,f7,f8}
Igb = ncGroebnerBasis(I, DegreeLimit => 6)
B = A/I
hilbertSeries(B, Order => 6)

restart
needsPackage "NCAlgebra"
A = QQ{x_1,x_2,x_3,x_4}
I = ncIdeal {x_1^2 - x_4^2, x_2^2 - x_3^2, x_4*x_1 - x_2*x_3, x_1*x_4 - x_3*x_2, x_1*x_3 - x_2*x_4, x_3*x_1-x_4*x_2}
Igb = ncGroebnerBasis(I, DegreeLimit => 6)
B = A/I
hilbertSeries(B, Order => 6)

restart
load "hopfActions.m2"
A = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z})
C = bialgebra(A,{{(x,x),(y,y)},{(y,y)},{(z,z)}},{1_A,1_A,1_A})
source ((target C.deltas#1).cache#iota2)

((target (C.deltas#1)).cache)#1 === (source C.deltas#1)

restart
load "hopfActions.m2"
-- this is H8
A = QQ{x,y,z}
-- this is a GB already
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
Igb = ncGroebnerBasis(I, InstallGB => true)
H = A/I

restart
load "hopfActions.m2"
A = fourDimSklyanin(QQ,apply(, i -> random(QQ)), {a,b,c,d})
hilbertSeries(A, Order => 6)

restart
load "hopfActions.m2"
A = skewPolynomialRing(QQ,(-1)_QQ,{x,y,z})
A1 = createSubscriptRing(A,1)
gens A1
A2 = createSubscriptRing(A,2)
gens A2
A1 ** A2

restart
load "hopfActions.m2"
A = QQ{x,y}
I = ncIdeal{x^2 - y}
Igb = ncGroebnerBasis I

restart
load "hopfActions.m2"
-- this is H8
A = QQ{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
H = A/I
--- this bit computes the tensor product without computing the GB again
H1 = createSubscriptRing(H,1)
H2 = createSubscriptRing(H,2)
H12 = tensorProductNoGB(H1,H2)
delta1 = ncMap(H12,H1,{xx_(1,1)*xx_(1,2),xx_(2,1)*xx_(2,2),(1/2)*(1_H12 + xx_(1,2) + xx_(2,1) - xx_(2,1)*xx_(1,2))*(xx_(3,1)*xx_(3,2))})
isWellDefined delta1
Delta = delta1 @@ (ncMap(H1,H,gens H1))
use H
Delta(x*y*z)
--- add on another factor.
--- need to construct another delta, this with domain H2 and codomain H2 \otimes H3
--- this is 'Delta2L' i.e. expanding on the left
H3 = createSubscriptRing(H,3)
psi = ncMap(H3,H2,gens H3)
delta2L = tensorProductNoGB(delta1,psi)
Delta2L = delta2L @@ (ncMap(source delta2L, target delta1, gens source delta2L)) @@ delta1 @@ (ncMap(H1,H,gens H1))
Delta2L(x*y*z)
--- this is 'Delta2R' i.e. expanding on the right
H23 = tensorProductNoGB(H2,H3)
psi3 = ncMap(H23,H12,gens H23)
psi2inv = ncMap(H1,H2,gens H1)
delta2R = tensorProductNoGB(ncMap(H1,H1,gens H1), psi3 @@ delta1 @@ psi2inv)
Delta2R = delta2R @@ (ncMap(source delta2R, target delta1, gens source delta2R)) @@ delta1 @@ (ncMap(H1,H,gens H1))

(ncMap(target Delta2L,target Delta2R, gens target Delta2L))(matrix Delta2R) == matrix Delta2L

restart
load "hopfActions.m2"
A = QQ{x,y,z,w}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, z^2 - 1_A, x*y - y*x, w*x - y*w, w*y - x*w, w^2 - z, x*z - z*x, y*z - z*y, w*z - z*w}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
H = A/I
sum(apply(5, i -> #(flatten entries basis(i,H))))
--- this bit computes the tensor product without computing the GB again
H1 = createSubscriptRing(H,1)
H2 = createSubscriptRing(H,2)
H12 = tensorProductNoGB(H1,H2)
Delta1' = ncMap(H12,H1,{xx_(1,1)*xx_(1,2),xx_(2,1)*xx_(2,2),xx_(3,1)*xx_(3,2),(1/2)*(1_H12 + xx_(1,2)*xx_(2,2) + xx_(3,1) - xx_(3,1)*xx_(1,2)*xx_(2,2))*(xx_(4,1)*xx_(4,2))})
isWellDefined Delta1'
Delta = Delta1' @@ (ncMap(H1,H,gens H1))
use H
Delta(x*y*z)
--- add on another factor.
--- need to construct another delta, this with domain H2 and codomain H2 \otimes H3
--- this is 'Delta2L' i.e. expanding on the left
H3 = createSubscriptRing(H,3)
psi = ncMap(H3,H2,gens H3)
delta2L = tensorProductNoGB(Delta1',psi)
Delta2L' = delta2L @@ (ncMap(source delta2L, target Delta1', gens source delta2L)) @@ Delta1'
Delta2L = Delta2L' @@ (ncMap(H1,H,gens H1))
Delta2L(x*y*z)
----
H4 = createSubscriptRing(H,4)
psi2 = ncMap(H4,H2,gens H4)
delta3L = tensorProductNoGB(Delta2L',psi2)
Delta3L' = delta3L @@ (ncMap(source delta3L, target Delta1', gens source delta3L)) @@ Delta1'
Delta3L = Delta3L' @@ (ncMap(H1,H,gens H1))
Delta3L(w)
--- this is 'Delta2R' i.e. expanding on the right
H23 = tensorProductNoGB(H2,H3)
psi3 = ncMap(H23,H12,gens H23)
psi2inv = ncMap(H1,H2,gens H1)
delta2R = tensorProductNoGB(ncMap(H1,H1,gens H1), psi3 @@ delta1 @@ psi2inv)
Delta2R = delta2R @@ (ncMap(source delta2R, target delta1, gens source delta2R)) @@ delta1 @@ (ncMap(H1,H,gens H1))

(ncMap(target Delta2L,target Delta2R, gens target Delta2L))(matrix Delta2R) == matrix Delta2L

restart
load "hopfActions.m2"
-- this is H8
A = QQ{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_QQ,1_QQ,1_QQ})
ID = ncMap(H.ring,H.ring,gens H.ring)
eps = H.counit
tensorProductNoGB(ID,eps)
getDeltaN(H,1)
getDeltaN(H,2)

time getDeltaN(H,3)
#(terms last flatten entries matrix getDeltaN(H,3))
time getDeltaN(H,4)

isCoassociative(H)

restart
needsPackage "NCAlgebra"
R = QQ{x,y,z}
S = QQ{s,t}
ncMap(R,R,{s,t})

restart
needsPackage "NCAlgebra"
R = skewPolynomialRing(QQ,(-1)_QQ,{x,y})
phi = ncMap(R,R,{x+y,x-y})
phi(x*y)
phi(x)*phi(y) + phi(y)*phi(x)
isWellDefined phi


restart
load "hopfActions.m2"
-- this is H8 Kac-Paljutkin
A = QQ{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
J = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - 1_A}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
Jgb = ncGroebnerBasis(J, InstallGB => true)
B1 = A/I
B2 = A/J
use B1
H1 = bialgebra(B1,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B1,1_B1,1_B1})
use B2
H2 = bialgebra(B2,{{(x,x)},{(y,y)},{(z,z)}},{1_B2,1_B2,1_B2})
isCounit H1
isBialgebra H1
isCocommutative H1
isCounit H2
isBialgebra H2
isCocommutative H2

iota = H.inclusion
B = H.ring
B12 = target H.deltas#1 @@ H.inclusion 
H.counit|drop(gens(B12),numgens B)
{1_B12, 1_B12, 1_B12}

epsiTensId= ncMap(B12,B12,{1_B12, 1_B12, 1_B12} |drop(gens(B12),numgens B))
matrix epsiTensId
idTensEpsi = ncMap(B12,B12,take(gens(B12),numgens B) | {1_B12, 1_B12, 1_B12} )
matrix epsiTensId 
matrix idTensEpsi
gens B12
gens B
mult = ncMap(B, B12, {x,y,z,x,y,z})
epsID = mult @@ epsiTensId
idEps = mult @@ idTensEpsi
matrix idEps == matrix epsID
matrix idEps
matrix epsID

restart
load "hopfActions.m2"
-- this is H8 Kac-Paljutkin
A = QQ{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
apply(10, i -> #(flatten entries basis(i,B)))
factorMonomial (x*y)

restart
M = matrix {{1,1},{2,3}}
N = matrix {{M},{M},{M}}

restart
load "hopfActions.m2"
-- this is Kashina 9
kk = toField(QQ[a]/ideal{a^2+1})
kk = QQ
A = kk{x,y,z}
I = ncIdeal {-y*x+x*y, y^2-1_A, z*y-y*z, z^2-y, -x*y*z+z*x, y*z*x-x*z, z*x^2-x^2*z, z*x*y-x*z, z*x*z-x, x^4-1_A, x^3*z*x-y*z}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
-- fix this
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z), (1/2*y*z,z), (1/2*z,x^2*z), (-1/2*y*z, x^2*z)}},{1_B,1_B,1_B})
findGrouplikes H
isBialgebra H
totalBasis H
findLeftIntegral H

--- more interesting antipode
restart
load "hopfActions.m2"
A = QQ{x,y,z,w}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, z^2 - 1_A, x*y - y*x, x*z - z*x, y*z - z*y, w*x - y*w, w*y - x*w, w*z - z*w, w^2 - 1_A}
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(z,z)},{((1/2)*w,w), ((1/2)*w,x*y*w), ((1/2)*z*w,w), (-(1/2)*z*w, x*y*w)}}, {1_B,1_B,1_B,1_B})
S = findAntipode H
--- here we see that S^2 is the identity
apply(gens B, v -> applyAntihomomorphism(S, S(v)))

--- can we do the Taft algebra?
restart
needsPackage "NCAlgebra"
needsPackage "HopfAlgebras"
needsPackage "Cyclotomic"
n = 6
kk = cyclotomicField(n)
w = kk_0
A = kk{c,x}
I = ncIdeal {c^n - 1_A, x^n, c*x - w^(n-1)*x*c}
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
basisB = totalBasis(B, DegreeLimit => n^2)
#(flatten entries basisB)
H = bialgebra(B,{{(c,c)},{(c,x),(x,1_B)}},{1_B,0_B})
isBialgebra H
S = findAntipode H
S2 = ncMap(B,B,apply(gens B, v -> applyAntihomomorphism(S, S(v))))
S4 = ncMap(B,B,apply(gens B, v -> applyAntihomomorphism(S2, applyAntihomomorphism(S2,v))))
S6 = ncMap(B,B,apply(gens B, v -> applyAntihomomorphism(S4, applyAntihomomorphism(S2,v))))
S8 = ncMap(B,B,apply(gens B, v -> applyAntihomomorphism(S4, applyAntihomomorphism(S4,v))))
S10 = ncMap(B,B,apply(gens B, v -> applyAntihomomorphism(S6, applyAntihomomorphism(S4,v))))
S12 = ncMap(B,B,apply(gens B, v -> applyAntihomomorphism(S8, applyAntihomomorphism(S4,v))))
findLeftIntegral H
L = kk{u,v}
J = ncIdeal {u*v - v*u}
K = L/J
xAction = ncMap(K,K,{0_K,u})
cAction = ncMap(K,K,{u,w*v})
action = bialgebraAction(H,K,{cAction,xAction})
isWellDefined action
R = invariantAlgebra(action,getSymbol "a")
matrix R.cache.presentation

restart
needsPackage "NCAlgebra"
debug needsPackage "HopfAlgebras"
-- this is H8 Kac-Paljutkin
R = QQ[a_1,a_2,b_1,b_2,c_1,c_2,d_1,d_2,e_1,e_2,f_1,f_2,g_1,g_2,h_1,h_2,zz]/ideal{zz^2+1}
R = QQ[a_1,a_2,b_1,b_2,c_1,c_2,d_1,d_2,e_1,e_2,f_1,f_2,g_1,g_2,h_1,h_2]
R = QQ[c_(1,1)..c_(8,8),zz]/ideal{zz^2+1}
kk = frac(R)
kk = R
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
basisB = flatten entries totalBasis B


x' = matrix {{0,1_QQ,0,0,0,0,0,0}}
y' = matrix {{0,0,1_QQ,0,0,0,0,0}}
xy' = matrix {{0,0,0,0,1_QQ,0,0,0}}
z' = matrix {{0,0,0,1_QQ,0,0,0,0}}
--gen1 = matrix {{a_1,b_1,c_1,d_1,e_1,f_1,g_1,h_1}}
--gen2 = matrix {{a_2,b_2,c_2,d_2,e_2,f_2,g_2,h_2}}
gen1 = matrix {toList(c_(1,1)..c_(1,8))}
genHH = matrix pack(toList(c_(1,1)..c_(8,8)),8)
ident = id_(kk^8)
--coun = matrix {{1_kk,1,1,1,1,1,1,1}}
coun = dualCounit H
--gensHdual = apply(#basisB, i -> (id_(kk^(#basisB)))^{i})
gensHdual = dualBasis H
convolUnit = matrix {apply(basisB, m -> sparseCoeffs(H.counit m, Monomials => basisB))} -- 

--- this should be its own command
coprodImage = coprodImg(basisB, H)
--coprodImage = apply(basisB, m -> apply(terms (H.deltas#1 H.inclusion m), t -> (H.leftTens t, (leadCoefficient t)^(-1)*(H.rightTens t))))
--- linear map representing the mult map H \otimes H \to H
--multMatrix = sparseCoeffs(flatten apply(basisB, m1 -> apply(basisB, m2 -> m1*m2)), Monomials => basisB)
time multMatrix = fold(apply(basisB, m -> totalLeftMultMap(m, H)), (x,y) -> x | y)
time multMatrix = matrix {apply(basisB, m -> totalLeftMultMap(m, H))}
--- linear map representing the comult map H \otimes H \to H
time comultMat = matrix {apply(coprodImage, coprod -> sum apply(coprod, t -> sparseCoeffs(t#0, Monomials => basisB) ** sparseCoeffs(t#1, Monomials => basisB)))}
time comultMat' = comultMatrix H
--- product in the dual (on the level of row vectors)
dualProd = (a,b) -> matrix {apply(#basisB, i -> sum apply(coprodImg#i, p -> (a*sparseCoeffs(p#0,Monomials => basisB))*(b*sparseCoeffs(p#1,Monomials => basisB))))}
--- different way that generalizes to convolution products
dualProd' = (a,b) -> (a**b)*comultMatrix
convolProd = (A,B) -> multMatrix*(A**B)*comultMatrix
--- coproduct in the dual (on the level of row vectors)
dualCoprod = a -> a*multMatrix
--- map sending phi to phi otimes phi from H^* to H^* \otimes H^* at the level of
--- row vectors (with the basis chosen for (H \otimes H)^* = H^* \otimes H^*)
dualDiag = a -> matrix {flatten apply(#basisB, i -> apply(#basisB, j -> (a_(0,i))*(a_(0,j))))}
--- counit of the dual
dualCounit = a -> a_(0,0)
--- unit of the dual
dualUnit = matrix {apply(#basisB, i -> leadCoefficient H.counit (basisB#i))}

dualProd(z',coun)
dualProd'(z',coun)
dualCoprod coun

--- find the grouplikes of the dual, i.e. the one dimensional representations of H.
temp = dualCoprod gen1 - dualDiag gen1
oneDimRepList = primaryDecomposition radical (ideal sub(temp,R) + ideal sub(dualCounit gen1 - 1_kk, R))
-- these are the polynomial that need roots.  Not sure how to automate this part without
-- going back to the definition of the ring with variables and adding the roots
select(flatten (oneDimRepList / gens / entries / flatten), f -> first degree f > 1)
--- these are the grouplikes of the dual, considered as row vectors
oneDimRepRowVecs = apply(oneDimRepList, p -> sub(sub(gen1, R/p),kk))
--- have not yet written code to turn the above into NCRingMaps
netList apply(oneDimRepRowVecs, a -> apply(oneDimRepRowVecs, b -> dualProd'(a,b)))
--- find 'z'
alpha = oneDimRepRowVecs#1
beta = oneDimRepRowVecs#2
eqs1 = dualProd(alpha,gen1) - dualProd(gen1, beta)
eqs2 = dualProd(beta,gen1) - dualProd(gen1, alpha)
eqs3 = dualProd(gen1,gen1) - (1/2)*(dualUnit + alpha + beta - dualProd(alpha,beta))
dualProd(alpha,xy') - dualProd(xy',beta)
gens gb (ideal eqs1 + ideal eqs2 + ideal eqs3)
sub(matrix {take(gens R, 8)}, R/(ideal gens gb (ideal eqs1 + ideal eqs2)))

--- compute antipode
matrix pack(flatten entries sub(vars R, R/(ideal (convolProd(genHH,ident) - convolUnit))), 8)

restart
needsPackage "NCAlgebra"
needsPackage "HopfAlgebras"
--- H8
---R = QQ[c_(1,1)..c_(8,8),zz]/ideal{zz^2+1}
kk = QQ[zz]/ideal{zz^2+1}
---kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
--Hdual = new DualBialgebra from {(symbol ring) => H}
Hdual = dualize H
grouplikes = findGrouplikes Hdual
phi = grouplikes#1
de = sum grouplikes
ncMap de
ncMap phi
oneDimReps = grouplikes/ncMap
all(oneDimReps,isWellDefined)
all(grouplikes, g -> dualCoprod g - g**g == 0)
de = dualElement(Hdual,matrix {toList(c_(1,1)..c_(1,8))})
net de
de + de
de*de
de^3
de*c_(1,1)
c_(1,1)*de

Hdual * Hdual := (a,b) -> dualProd(a,b)
Hdual + Hdual := (a,b) -> new Hdual from hashTable { (symbol matrix) => a.matrix + b.matrix,
                                                     (symbol ring) => Hdual }
Hdual ^ ZZ := (a,n) -> ...
ZZ * Hdual
Hdual * ZZ
QQ * Hdual
Hdual * QQ
kk * Hdual
Hdual * kk

net DualElement := de -> net de.matrix

de = new Hdual from hashTable { (symbol matrix) => matrix {toList(c_(1,1)..c_(1,8))},
	                        (symbol ring) => Hdual }

de*de
de + de

restart
needsPackage "HopfAlgebras"
needsPackage "NCAlgebra"
-- this is H8
kk = QQ[zz]/ideal{zz^2+1}
--kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
--cB = toCommPolyRing(H,8)
totalBasis H
findLeftIntegral H
L = kk{u,v}
J = ncIdeal {u^2 - v^2}
K = L/J
xAction = ncMap(K,K,{-u,v})
yAction = ncMap(K,K,{u,-v})
zAction = ncMap(K,K,{v,u})
action = bialgebraAction(H,K,{xAction,yAction,zAction})
deg2Invariants = invariantInDegree(action, 2)
deg3Invariants = invariantInDegree(action, 3)
deg4Invariants = invariantInDegree(action, 4)
deg5Invariants = invariantInDegree(action, 5)
deg6Invariants = invariantInDegree(action, 6)


hDual = dualize H
grouplikes = findGrouplikes hDual

--- find KH generators of Kchi where Kchi is the weight module
--- for the last grouplike found in the previous command
KH = invariantAlgebra(action,getSymbol "cc",GenDegreeLimit=>6,RelDegreeLimit=>6)
phi = KH.cache.presentation
--- deg 2
deg2Weights = weightSpaceInDegree(action,2,grouplikes#3)


kChiGens = deg2Weights
--- deg 3
deg3Weights = weightSpaceInDegree(action,3,grouplikes#3) -- none of these
--- deg 4
deg4Weights = weightSpaceInDegree(action,4,grouplikes#3) -- none of these
gensImage = flatten apply(kChiGens, f -> apply(flatten entries basis(2,KH), m -> f*(phi m)))
M = sparseCoeffs(deg4Weights, Monomials=>flatten entries basis(4,K))
N = sparseCoeffs(gensImage, Monomials=>flatten entries basis(4,K))
mingens ((image M) / (image N))
--- a relation on the generators in degree 4 found using ker N
-zz*kChiGens#0*(phi KH_0) + kChiGens#1*(phi KH_0)
--- deg 5
deg5Weights = weightSpaceInDegree(action,5,grouplikes#3) -- none of these
--- deg 6
deg6Weights = weightSpaceInDegree(action,6,grouplikes#3) -- none of these
gensImage = flatten apply(kChiGens, f -> apply(flatten entries basis(6-(degree f),KH), m -> f*(phi m)))
M = sparseCoeffs(deg6Weights, Monomials=>flatten entries basis(6,K))
N = sparseCoeffs(gensImage, Monomials=>flatten entries basis(6,K))
mingens ((image M) / (image N))
--- deg 7
deg7Weights = weightSpaceInDegree(action,7,grouplikes#3) -- none of these
--- deg 8
deg8Weights = weightSpaceInDegree(action,8,grouplikes#3) -- none of these
gensImage = flatten apply(kChiGens, f -> apply(flatten entries basis(8-(degree f),KH), m -> f*(phi m)))
basisK = flatten entries basis(8,K)
M = sparseCoeffs(deg8Weights, Monomials=>basisK)
N = sparseCoeffs(gensImage, Monomials=>basisK)
mingens ((image M) / (image N))

weightSpaceInDegree(action,2,grouplikes#0)
weightSpace10 = apply(10, i -> weightSpaceInDegree(action,i,grouplikes#0))

deg2Weights = weightSpaceInDegree(action,2,grouplikes#3)
(first deg2Invariants)*(first deg2Weights)

deg4Weights = weightSpaceInDegree(action,4,grouplikes#3)

weightSpace10  = apply(10, i -> weightSpaceInDegree(action,i,grouplikes#3))

sum grouplikes
ncMap oo
ncMap grouplikes#2
weightSpaceInDegree(action,2,(sum grouplikes))

restart
needsPackage "HopfAlgebras"
needsPackage "NCAlgebra"
-- this is H8
kk = QQ[zz]/ideal{zz^2+1}
--kk = QQ
A = kk{x,y,z}
I = ncIdeal {x^2 - 1_A, y^2 - 1_A, x*y - y*x, z*x - y*z, z*y - x*z, z^2 - (1/2)*(1_A + x + y - x*y)}
-- this is a GB already
Igb = ncGroebnerBasis(I, InstallGB => true)
B = A/I
H = bialgebra(B,{{(x,x)},{(y,y)},{(1/2*z,z),(1/2*z,x*z),(1/2*y*z,z),(-1/2*y*z,x*z)}},{1_B,1_B,1_B})
--cB = toCommPolyRing(H,8)
L = kk{u,v}
J = ncIdeal {u^2 - v^2}
K = L/J
xAction = ncMap(K,K,{-u,v})
yAction = ncMap(K,K,{u,-v})
zAction = ncMap(K,K,{v,u})
action = bialgebraAction(H,K,{xAction,yAction,zAction})
--time invarGens =invariantAlgebraGens(action, DegreeLimit => 10)

hDual = dualize H
grouplikes = findGrouplikes hDual

phi0 = grouplikes#0
phi1 = grouplikes#1
phi2 = grouplikes#2
phi3 = grouplikes#3

weightSpaceGens(action,phi0)
weightSpaceGens(action,phi1)
weightSpaceGens(action,phi2)
weightSpaceGens(action,phi3)

Deg2Weights = weightSpaceInDegree(action,2,phi3)
Deg3Weights = weightSpaceInDegree(action,3,phi)
DegIWeights = apply(10, i -> weightSpaceInDegree(action,(i+1),phi))
Deg3Weights = getNextDegWeights(action,Deg2Weights,3,phi)
Deg4Weights = getNextDegWeights(action,Deg2Weights,4,phi)
Deg5Weights = getNextDegWeights(action,Deg2Weights,5,phi)
Deg6Weights = getNextDegWeights(action,Deg2Weights,6,phi)
Deg7Weights = getNextDegWeights(action,Deg2Weights,7,phi)
Deg8Weights = getNextDegWeights(action,Deg2Weights,8,phi)
getNextDegWeights(action,{},2,phi)


restart
kk = QQ[zz]/(ideal {zz^2 + 1})
M = matrix {{0, 0}, {zz, 1}, {-1, zz}}
Mprune = prune image M
Mmingens = mingens image M
image Mprune.cache.pruningMap
