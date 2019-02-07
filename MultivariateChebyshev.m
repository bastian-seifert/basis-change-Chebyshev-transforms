(* Wolfram Language Package *)

(* Created by the Wolfram Workbench 28.12.2016 *)

BeginPackage["MultivariateChebyshev`"]
(* Exported symbols added here with SymbolName::usage *) 

WeylGroup::usage = 
    "WeylGroup[roots] returns the Weyl group associated to the roots given 
	in homogeneous coordinates. The Weyl group is returned in standard 
	coordinates and transposed form."
    
calculateBasisChange::usage = 
    "CalculateBasisChange[index, boundary, WeylGroup[ calculates the basis change of index with respect
	to boundary and WeylGroup"
    
ChebyshevRecurrenceRelationRightHandSideIndices::usage =
    "Gives the right hand side of the recurrence relation for indices k,l and type"

HouseholderMatrix::usage =
    "Returns a the HouseholderMatrix of vec"
    
PositivizeIndices::usage =
    "Gives the most positive index achievable to actions of the Weyl Group"
    
SimpleRoots::usage =
    "Returns a set of simple roots of type"
    
WeylGroupOrbit::usage =
    "Returns the WeylGroupOrbit of an element of the index space"

Begin["`Private`"]
(* Implementation of the package *)

   
Options[calculateBasisChange] = {Assuming -> Assumptions};
calculateBasisChange[index_, bounds_, W_, OptionsPattern[]] := 
  Module[{currIdx, tmpIdx, tmp, indshift, bndshift, i},
   currIdx = {{1, {index}}};
   While[AnyTrue[ currIdx, 
     And @@ (Not[
           Assuming[Assumptions, 
            checkIfValidIndex[#, bounds]]] &  /@ #[[2]] ) &],
    tmpIdx = {};
    For[ i = 1, i <= Length[currIdx], i++, 
     If[ Assuming[Assumptions, 
       checkIfValidIndex[currIdx[[i, 2, 1]], bounds]],
      tmpIdx = Append[tmpIdx, currIdx[[i]]],
       Assuming[Assumptions,
       (* 
       It's ok to restrict to only the first one here as if there \
were more than one the index is always valid under correct \
assumptions!*)
       {indshift, bndshift} = 
        Transpose[
         MapThread[
          Assuming[Assumptions, splitApart[#1, #2]] &, {currIdx[[i, 2,
             1]], bounds}]]];
      tmp = 
       Assuming[Assumptions, 
        replaceWithRecurrenceRelation[indshift, bndshift, W]];
      tmp =  {currIdx[[i, 1]] * #[[1]], #[[2]]} & /@ tmp;
      tmpIdx = Join[tmpIdx, tmp];
        ]
     ];
    currIdx = 
     DeleteCases[
      List[Sum[#[[ii, 1]], {ii, 1, Length[#]}], #[[1, 2]]] & /@ 
       Gather[tmpIdx, Assuming[Assumptions,Simplify[#1[[2]]==#2[[2]]]] &], x_ /; x[[1]] == 0];
    ];
   currIdx
   ];

Options[ChebyshevRecurrenceRelationRightHandSideIndices] = {Assuming -> $Assumptions}
    
ChebyshevRecurrenceRelationRightHandSideIndices[k_, l_, type_?StringQ,OptionsPattern[]] :=
    Block[ {},
        ChebyshevRecurrenceRelationRightHandSideIndices[k,l,WeylGroup[type], OptionsValue[Assuming]]
    ]
    
ChebyshevRecurrenceRelationRightHandSideIndices[k_, l_, W_,OptionsPattern[]] :=
    Block[ {i,tmp, lengths},
        tmp = Table[
            Assuming[Assumptions,
                PositivizeIndices[k+W[[i]].l,W]
                ],
             {i, Length[W]}];
        lengths =  Length /@ GatherBy[tmp, Sort[WeylGroupOrbit[#1, W]] &];
        tmp = DeleteDuplicatesBy[tmp, Sort[WeylGroupOrbit[#1, W]] &];
        Table[{lengths[[i]]/Length[W], tmp[[i]]}, {i, Length[tmp]}]
    ]
    
Options[checkIfValidIndex] = {Assuming -> Assumptions};
checkIfValidIndex[index_, bnd_, OptionsPattern[]] := Module[{},
  Or[Assuming[Assumptions, 
    FullSimplify[
     And @@ MapThread[(PolynomialRemainder[#1, #2, #3] == 
          0) &, {index, bnd, bnd}]]],
   Assuming[Assumptions, FullSimplify[And @@ Thread[bnd > index]]]]
  ]

 
Options[myCompare] = {Assuming -> $Assumptions}

 myCompare[l1_, l2_, OptionsPattern[]] :=
     Block[ {},
         Assuming[Assumptions,
         Simplify[If[ AllTrue[l1, # >= 0 &] && AllTrue[l2, # >= 0 &],
                      Max[l1] <= Max[l2],
                      If[ AllTrue[l1, # >= 0 &],
                          True,
                          False
                      ]
                  ]
         ]
         ]
     ];
    

Options[PositivizeIndices] = {Assuming -> $Assumptions}
        
PositivizeIndices[k_, type_?StringQ, OptionsPattern[]] :=
    Block[ {W},
        W = WeylGroup[type];
        Assuming[Assumptions, PositivizeIndices[k, W]]
    ]

    
PositivizeIndices[k_, W_, OptionsPattern[]] :=
    Block[ {ktmp},
        ktmp = WeylGroupOrbit[k,W];
        Assuming[Assumptions,
        Sort[ktmp, myCompare[#1,#2]&][[1]]
        ]
    ]
    
Options[replaceWithRecurrenceRelation] = {Assuming -> Assumptions};
replaceWithRecurrenceRelation[indshift_, bndshift_, W_, 
  OptionsPattern[]] := Module[{recurrenceResults, f2, tmp, tind, ind}, 
  ind = indshift + bndshift;
  recurrenceResults = 
   Assuming[Assumptions, 
    ChebyshevRecurrenceRelationRightHandSideIndices[indshift, 
     bndshift, W]];
  (*Get the index part*)  
	  f2[x_] := If[#, 0.0, 1.0]& @(x[[1, 2]] === ind);
  recurrenceResults = 
   Sort[GatherBy[recurrenceResults, #[[2]] === ind &], 
    f2[#1] > f2[#2] &];
  tmp = recurrenceResults[[1]];
  (*negative as brought on other side and divide by ind count*)
  
  tmp[[All, 1]] = (Minus@Divide[#, recurrenceResults[[2, 1, 1]]]) & /@
     tmp[[All, 1]];
  (*To match format an allow more than one chebyshev poly*)
  
  tmp[[All, 2]] = 
   List[#] & /@ Assuming[Assumptions, Simplify[tmp[[All, 2]]]];
   (*if one chebyshev poly appears more than one times*)
   tmp = {Sum[i[[1]], {i, #}], #[[1, 2]]} & /@ GatherBy[tmp, #[[2]] &];
  (*ind and bound shift become a new member*)
  
  tind = {{1/recurrenceResults[[2, 1, 1]], {indshift, bndshift}}};
  tmp = Union[tind, tmp]];

   
SimpleRoots[type_?StringQ] :=
    Block[ {roots, family, dim},
        family = Characters[type][[1]];
        dim = ToExpression[StringJoin[Characters[type][[2;;]]]];
        Switch[family,            
            "A", roots = Table[UnitVector[dim+1,i]-UnitVector[dim+1,i+1], {i,dim}],
            "B", roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]}],
            "C", roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {2*UnitVector[dim,dim]}],
            "D", roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]+UnitVector[dim,dim-1]}],
            "G", roots = {{1,-1,0},{-1,2,-1}},
            _, "Not yet implemented!"
        ];
        (* Project the roots in their least dimensional space *)
        DeleteCases[Orthogonalize[roots], ConstantArray[0, Length[roots[[1]]]]].Transpose[roots] // Transpose
    ]
    
Options[splitApart] = {Assuming -> Assumptions};

splitApart[x_, m_, OptionsPattern[]] := 
  Module[{tmpBound, tmpVar}, tmpVar = x;
   tmpBound = 0;
   While[Assuming[Assumptions, FullSimplify[tmpVar >= m]], 
    tmpVar = Simplify[tmpVar - m];
    tmpBound = tmpBound + m;];
   {tmpVar, tmpBound}
   ];

WeylGroupOrbit[k_, type_?StringQ] :=
    Block[ {i,W},
        W = WeylGroup[type];
        Table[W[[i]].k, {i, Length[W]}]
    ]


WeylGroupOrbit[k_, W_] :=
    Block[ {i},
        Table[W[[i]].k, {i, Length[W]}]
    ]

    
    
WeylGroup[type_?StringQ] :=
    Block[ {roots, family, dim},
        family = Characters[type][[1]];
        dim = ToExpression[StringJoin[Characters[type][[2;;]]]];
        Switch[family,            
            "A", (roots = Table[UnitVector[dim+1,i]-UnitVector[dim+1,i+1], {i,dim}];
                  WeylGroup[roots] ),
            "B", (roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]}];
                  WeylGroup[roots]),
            "C", (roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {2*UnitVector[dim,dim]}];
                  WeylGroup[roots]),
            "D", (roots = Union[Table[UnitVector[dim,i]-UnitVector[dim,i+1], {i,dim-1}], {UnitVector[dim,dim]+UnitVector[dim,dim-1]}];
                  WeylGroup[roots]),
            "G", (roots = {{1,-1,0},{-1,2,-1}};
                  WeylGroup[roots] ),
            _, "Not yet implemented!"
        ]
    ]

WeylGroup[roots_] :=
    Block[ {proj, gens,matrices},
        (* Project the roots in their least dimensional space *)
        proj = DeleteCases[Orthogonalize[roots], ConstantArray[0, Length[roots[[1]]]]].Transpose[roots] // Transpose; 
        (* Calculate the generators of the Weyl group *)
        gens = HouseholderMatrix /@ proj;    
        (* Base Change to Basis consisting of roots *)
        gens = Simplify[(proj.#1.Inverse[proj])] & /@ gens; 
        (* generate the group via brute force*)
        FixedPoint[Union[#, Dot @@@ Tuples[#, 2]] &, gens]
    ]
    
    
HouseholderMatrix[v_?VectorQ] :=
    Module[ {},
        IdentityMatrix[Length[v]] - 2 Transpose[{v}] . {v} / (v.v)
    ]    

    
End[]

EndPackage[]

