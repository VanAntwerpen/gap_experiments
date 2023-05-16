
#This  function checks  whether  a given skew brace b is annihilator nilpotent.
#Concretely, it checks if the annihilator series ends  in  $1$.
#Assumptions: the  skew brace B  is finite.
IsAnnihilatorNilpotent:=function(B)
local s, ann, quot, s2;
s:=Size(B);
ann:=Annihilator(B); #construct Annihilator
quot:=B/ann; #Construct factorbrace B/ann(B)
s2:=Size(quot);
while s2<s do
  s:=ShallowCopy(s2);
  ann:=Annihilator(quot);
  quot:=quot/ann;
  s2:=Size(quot);
od;
if  s=1 then
  return true;
else
  return false;
fi;
end;

#This function constructs the largest annihilator nilpotent ideal of  B.
#Assumptions: B is finite.
FittingBrace:=function(B)
  local lst;
  lst:=Filtered(Ideals(B),x->IsAnnihilatorNilpotent(x));
  return Iterated(lst, SumOfTwoIdeals);
end;

#This function produces a list with the  factors of the annihilator series of B.
#Assumptions: B is finite
FactorsAnnSeries:=function(B)
  local new, old, done,l;
  old:=B;
  new:=Quotient(B,Annihilator(B));
  l:=[old];
  done:=false;

  repeat

  if Size(old)<>Size(new) then
    Add(l,new);
    old:=ShallowCopy(new);
    new:=Quotient(old,Annihilator(old));
  elif Size(old)=Size(new) and Size(new)=1 then
    done:=true;
  elif Size(old)=Size(new) and Size(new)<>1 then
    done:=true;
  fi;
until done;
return l;
end;

#This function produces a list with the factors of the Fitting series of a skew brace B.
#Assumptions: B is finite
FittingSeries:=function(B)
  local new, old, done,l;
  old:=B;
  new:=Quotient(B,FittingBrace(B));
  l:=[old];
  done:=false;

  repeat

  if Size(old)<>Size(new) then
    Add(l,new);
    old:=ShallowCopy(new);
    new:=Quotient(old,FittingBrace(old));
  elif Size(old)=Size(new) and Size(new)=1 then
    done:=true;
  elif Size(old)=Size(new) and Size(new)<>1 then
    done:=true;
  fi;
until done;
return l;
end;

#This funtion constructs the commutator, as proposed by Facchini et al, for ideals I and J in a skew brace B.
BraceCommutator:=function(B,I,J)
  local tmp,tmp2,tmp3,lst,grp;
tmp:=List(List(Cartesian(I,J),x->Star(x[1],x[2])),x->x![1]);
tmp2:=List(List(Cartesian(J,I),x->Star(x[1],x[2])),x->x![1]);
tmp3:=CommutatorSubgroup(UnderlyingAdditiveGroup(I),UnderlyingAdditiveGroup(J));
lst:=Concatenation(tmp,tmp2,AsList(tmp3));
grp:=List(Group(lst));
return IdealGeneratedBy(B,SubSkewbrace(B,List(grp,y->SkewbraceElmConstructor(B,y))));
end;

#This function constructs the list with the derived series of B, using the commutator proposed by FAcchini.
SolvabilitySeries:=function(B)
  local new, old, done,l;
  old:=B;
  new:=BraceCommutator(B,B,B);
  l:=[old];
  done:=false;

  repeat

  if Size(old)<>Size(new) then
    Add(l,new);
    old:=ShallowCopy(new);
    new:=BraceCommutator(B,ShallowCopy(old),ShallowCopy(old));
  elif Size(old)=Size(new) and Size(new)=1 then
    done:=true;
  elif Size(old)=Size(new) and Size(new)<>1 then
    done:=true;
  fi;
until done;
return l;
end;

#This function returns a list of the descending central series of a skew brace B.
DescendingCentralSeries:=function(B)
  local new, old, done,l;
  old:=B;
  new:=BraceCommutator(B,B,B);
  l:=[old];
  done:=false;

  repeat

  if Size(old)<>Size(new) then
    Add(l,new);
    old:=ShallowCopy(new);
    new:=BraceCommutator(B,B,ShallowCopy(old));
  elif Size(old)=Size(new) and Size(new)=1 then
    done:=true;
  elif Size(old)=Size(new) and Size(new)<>1 then
    done:=true;
  fi;
until done;
return l;
end;

#This function produces a list of the Annihilator series of  a skew brace B.
AnnSeries:=function(B)
  local new, old, done,l, tmp, newlst,alpha,iso;
  old:=Annihilator(B);
  tmp:=Annihilator(Quotient(B,Annihilator(B)));  #Creating the 2nd annihilator
  alpha:=NaturalHomomorphismByNormalSubgroup(UnderlyingAdditiveGroup(B),UnderlyingAdditiveGroup(Annihilator(B))); #Here I try to  fix the problem that GAP does not recognize that tmp  is a sublist of  the quotient of the underlying additive groups
  iso:=IsomorphismGroups(UnderlyingAdditiveGroup(B/Annihilator(B)),Range(alpha)); #I construct an iso between the underlying additive group of the factor skew brace and the factor group of the underyling additive groups
  newlst:=PreImages(alpha ,List(Images(iso,UnderlyingAdditiveGroup(tmp)))); #I project tmp towards the factor group of underlying additives and  pull this image back  to B
  new:=SubSkewbrace(B,List(newlst,y->SkewbraceElmConstructor(B,y))); #the previously constructed list newlst gets converted to a subskewbrace of B
  l:=[old];
  done:=false;

  repeat

  if Size(old)<>Size(new) then
    Add(l,new);
    old:=ShallowCopy(new);
    tmp:=Annihilator(Quotient(B,old));
    alpha:=NaturalHomomorphismByNormalSubgroup(UnderlyingAdditiveGroup(B),UnderlyingAdditiveGroup(old));
    iso:=IsomorphismGroups(UnderlyingAdditiveGroup(Quotient(B,old)),Range(alpha));
    newlst:=PreImages(alpha ,List(Images(iso,UnderlyingAdditiveGroup(tmp))));
    new:=SubSkewbrace(B,List(newlst,y->SkewbraceElmConstructor(B,y)));
  elif Size(old)=Size(new) and Size(new)=Size(B) then
    done:=true;
  elif Size(old)=Size(new) and Size(new)<>Size(B) then
    done:=true;
  fi;
until done;
return l;
end;

#This function returns  the nth annihilator of B. Note that it calculates the full series first! (can be seriously optimized)
NthAnnihilator:=function(B,n)
  local ser, count;
  ser:=AnnSeries(B);
  count:=Minimum(Size(ser),n);
  if n>count then
    Print("Warning: the ",count, "th annihilator is given, as ", n, " is bigger than the length of the series.\n");
  fi;
  return ser[count];
end;

IsSolvableBrace:=function(B)
  local ser;
  ser:=SolvabilitySeries(B);
  return Size(ser[Size(ser)])=1;
end;

ConjectureChecker:=function(n)
  local nr, Br, conje;
  nr:=NrSmallSkewbraces(n);
  for i in [1..nr] do
    Br:=SmallSkewbrace(n,nr);
    if not(IsSolvableGroup(UnderlyingAdditiveGroup(Br))) or not(IsSolvable(Br)) then
      continue;
    fi;
    conje:=IsSolvableBrace(Br);
    Print("For skew brace ", n, " nr ", i," the conjecture is ", conje, "\n");
  od;
end;
