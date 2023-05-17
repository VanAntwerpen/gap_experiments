gap> B:=SmallSkewbrace(8,10);
<brace of size 8>
gap> IsAnnihilatorNilpotent(B);
true
gap> B:=SmallSkewbrace(16,24);
<brace of size 16>
gap> IsAnnihilatorNilpotent(B);
true
gap> Br:=SmallSkewbrace(12,24);
<skew brace of size 12>
gap> IsAnnihilatorNilpotent(Br);
false
gap> FittingBrace(Br);
<brace of size 6>
gap> Br:=SmallSkewbrace(16,85);
<brace of size 16>
gap> FittingBrace(Br);
<brace of size 16>
gap> Br:=SmallSkewbrace(24,12);
<skew brace of size 24>
gap> FittingBrace(Br);
<brace of size 12>
gap> FactorsAnnSeries(Br);
[ <skew brace of size 24>, <skew brace of size 12>, <skew brace of size 6> ]
gap> Br:=SmallSkewbrace(16,85);
<brace of size 16>
gap> FactorsAnnSeries(Br);
[ <brace of size 16>, <brace of size 8>, <brace of size 2>, <brace of size 1> ]
gap> Br:=SmallSkewbrace(12,24);
<skew brace of size 12>
gap> FactorsAnnSeries(Br);
[ <skew brace of size 12>, <skew brace of size 6> ]
gap> FittingSeries(Br);
[ <skew brace of size 12>, <brace of size 2>, <brace of size 1> ]
gap> Br:=SmallSkewbrace(16,85);
<brace of size 16>
gap> FittingSeries(Br);
[ <brace of size 16>, <brace of size 1> ]
gap> Br:=SmallSkewbrace(24,12);
<skew brace of size 24>
gap> FittingSeries(Br);
[ <skew brace of size 24>, <brace of size 2>, <brace of size 1> ]
gap> Ideals(Br);
[ <skew brace of size 24>, <brace of size 12>, <brace of size 6>, <brace of size 4>, <brace of size 2>,
  <brace of size 3>, <brace of size 1> ]
gap> l:=[last[2], last[3]];
[ <brace of size 12>, <brace of size 6> ]
gap> BraceCommutator(Br,l[1],l[2]);
<brace of size 1>
gap> BraceCommutator(Br,l[2],l[2]);
<brace of size 1>
gap> BraceCommutator(Br,l[1],l[1]);
<brace of size 1>
gap> BraceCommutator(Br,Br,l[1]);
<brace of size 6>
gap> BraceCommutator(Br,Br,Br);
<brace of size 12>
gap> DescendingCentralSeries(Br);
[ <skew brace of size 24>, <brace of size 12>, <brace of size 6>, <brace of size 3> ]
gap> Br:=SmallSkewbrace(12,25);
<skew brace of size 12>
gap> DescendingCentralSeries(Br);
[ <skew brace of size 12>, <brace of size 3> ]
gap> Br:=SmallSkewbrace(6,1);
<skew brace of size 6>
gap> DescendingCentralSeries(Br);
[ <skew brace of size 6>, <brace of size 3> ]
gap> Br:=SmallSkewbrace(5,1);
<brace of size 5>
gap> DescendingCentralSeries(Br);
[ <brace of size 5>, <brace of size 1> ]
gap> AnnSeries(Br);
[ <brace of size 5> ]
gap> Br:=SmallSkewbrace(6,1);
<skew brace of size 6>
gap> AnnSeries(Br);
[ <brace of size 1> ]
gap> Br:=SmallSkewbrace(12,25);
<skew brace of size 12>
gap> AnnSeries(Br);
[ <brace of size 2> ]
gap> Br:=SmallSkewbrace(24,12);
<skew brace of size 24>
gap> AnnSeries(Br);
[ <brace of size 2>, <brace of size 4> ]
gap> NthAnnihilator(Br,2);
<brace of size 4>
gap> NthAnnihilator(Br,1);
<brace of size 2>
gap> NthAnnihilator(Br,3);
Warning: the 2th annihilator is given, as 3 is bigger than the length of the series.
<brace of size 4>
gap> Br:=SmallSkewbrace(12,25);
<skew brace of size 12>
gap> NthAnnihilator(Br,1);
<brace of size 2>
gap> NthAnnihilator(Br,2);
Warning: the 1th annihilator is given, as 2 is bigger than the length of the series.
<brace of size 2>
gap> Br:=SmallSkewbrace(6,1);
<skew brace of size 6>
gap> NthAnnihilator(Br,1);
<brace of size 1>
gap> NthAnnihilator(Br,2);
Warning: the 1th annihilator is given, as 2 is bigger than the length of the series.
<brace of size 1>
gap> IsSolvableBrace(Br);
true
gap> Br:=SmallSkewbrace(24,12);
<skew brace of size 24>
gap> IsSolvableBrace(Br);
true
gap> Br:=SmallSkewbrace(12,24);
<skew brace of size 12>
gap> IsSolvableBrace(Br);
true
gap> Br:=SmallSkewbrace(12,22);
<skew brace of size 12>
gap> IsSimple(Br);
true
gap> IsSolvableBrace(Br);
false
gap> INFO_SSS:=InfoLevel(InfoSmallSkewbracesSearch);;
gap> SetInfoLevel( InfoSmallSkewbracesSearch, 0);
gap> ConjectureCheckerVariadic(SolvableConjectureOne, 12, [1, 38]);
Error, The 3rd argument, if present, must belong to [ 1 .. 38 ]
gap> ConjectureCheckerVariadic(SolvableConjectureOne, 12, 1, 38);
fail
gap> ConjectureCheckerVariadic(SolvableConjectureOne, 12, 1, 39);
Error, The 4th argument, if present, must belong to [ 1 .. 38 ]
gap> ConjectureCheckerVariadic(SolvableConjectureOne, 12, 10, 7);
Error, The 4th argument, if present, must be greater or equal to the 3rd
gap> ConjectureCheckerVariadic(IsSolvable, 12, 1, 7);
[ 12, 1 ]
gap> ConjectureCheckerVariadic(IsSolvableBrace, 12, 1, 7);
[ 12, 1 ]
gap> ConjectureCheckerVariadic( 12, 1, 7);
Error, The first argument must be a function
gap> ConjectureCheckerVariadic(IsSolvableBrace, -12, 1, 7);
Error, The second argument must be a positive integer
gap> SetInfoLevel( InfoSmallSkewbracesSearch, 1);
gap> ConjectureCheckerVariadic(SolvableConjectureOne, 12, 1, 38);
#I  Checking skew braces 1 ... 38 of order 12
#I  Search completed - no counterexample discovered
fail
gap> ConjectureCheckerVariadic(IsSolvableBrace, 12, 1, 38);
#I  Checking skew braces 1 ... 38 of order 12
#I  Discovered counterexample: SmallSkewbrace( 12, 1 )
[ 12, 1 ]
gap> SetInfoLevel( InfoSmallSkewbracesSearch, INFO_SSS);
