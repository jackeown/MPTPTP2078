%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:00 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   84 (  84 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u134,negated_conjecture,
    ( ~ ( sK1 != sK2 )
    | sK1 != sK2 )).

tff(u133,negated_conjecture,
    ( k6_waybel_0(sK0,sK1) != k6_waybel_0(sK0,sK2)
    | k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2) )).

tff(u132,negated_conjecture,
    ( ~ ~ v2_struct_0(sK0)
    | ~ v2_struct_0(sK0) )).

tff(u131,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | v3_orders_2(sK0) )).

tff(u130,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u129,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | l1_orders_2(sK0) )).

tff(u128,axiom,(
    ! [X0,X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP3(X0) ) )).

tff(u127,negated_conjecture,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u126,negated_conjecture,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u125,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r3_orders_2(sK0,X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | X0 = X1
          | ~ r3_orders_2(sK0,X0,X1)
          | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ! [X1,X0] :
        ( ~ r3_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) )).

tff(u124,axiom,(
    ! [X1,X0] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u123,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r1_orders_2(sK0,X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | X0 = X1
          | ~ r3_orders_2(sK0,X1,X0) )
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r3_orders_2(sK0,X1,X0) ) )).

tff(u122,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r1_orders_2(sK0,X0,X1)
          | ~ r1_orders_2(sK0,X1,X0)
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | X0 = X1 )
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 ) )).

tff(u121,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( ~ r1_orders_2(sK0,X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(sK0))
          | ~ m1_subset_1(X0,u1_struct_0(sK0))
          | r3_orders_2(sK0,X0,X1) )
    | ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_orders_2(sK0,X0,X1) ) )).

tff(u120,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u119,axiom,(
    ! [X1,X0,X2] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) )).

tff(u118,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | v5_orders_2(sK0) )).

tff(u117,negated_conjecture,
    ( ~ sP3(sK0)
    | sP3(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:40:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (18615)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (18623)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.48  % (18623)Refutation not found, incomplete strategy% (18623)------------------------------
% 0.20/0.48  % (18623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18606)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (18623)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18623)Memory used [KB]: 10618
% 0.20/0.49  % (18623)Time elapsed: 0.058 s
% 0.20/0.49  % (18623)------------------------------
% 0.20/0.49  % (18623)------------------------------
% 0.20/0.49  % (18606)Refutation not found, incomplete strategy% (18606)------------------------------
% 0.20/0.49  % (18606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18606)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18606)Memory used [KB]: 10618
% 0.20/0.49  % (18606)Time elapsed: 0.060 s
% 0.20/0.49  % (18606)------------------------------
% 0.20/0.49  % (18606)------------------------------
% 0.20/0.49  % (18612)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (18602)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.49  % (18612)Refutation not found, incomplete strategy% (18612)------------------------------
% 0.20/0.49  % (18612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (18612)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (18612)Memory used [KB]: 6140
% 0.20/0.49  % (18612)Time elapsed: 0.070 s
% 0.20/0.49  % (18612)------------------------------
% 0.20/0.49  % (18612)------------------------------
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (18602)# SZS output start Saturation.
% 0.20/0.50  tff(u134,negated_conjecture,
% 0.20/0.50      ((~(sK1 != sK2)) | (sK1 != sK2))).
% 0.20/0.50  
% 0.20/0.50  tff(u133,negated_conjecture,
% 0.20/0.50      ((~(k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2))) | (k6_waybel_0(sK0,sK1) = k6_waybel_0(sK0,sK2)))).
% 0.20/0.50  
% 0.20/0.50  tff(u132,negated_conjecture,
% 0.20/0.50      ((~~v2_struct_0(sK0)) | ~v2_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u131,negated_conjecture,
% 0.20/0.50      ((~v3_orders_2(sK0)) | v3_orders_2(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u130,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u129,negated_conjecture,
% 0.20/0.50      ((~l1_orders_2(sK0)) | l1_orders_2(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u128,axiom,
% 0.20/0.50      (![X0, X2] : ((~m1_subset_1(X2,u1_struct_0(X0)) | sP3(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u127,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(sK1,u1_struct_0(sK0))) | m1_subset_1(sK1,u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u126,negated_conjecture,
% 0.20/0.50      ((~m1_subset_1(sK2,u1_struct_0(sK0))) | m1_subset_1(sK2,u1_struct_0(sK0)))).
% 0.20/0.50  
% 0.20/0.50  tff(u125,negated_conjecture,
% 0.20/0.50      ((~(![X1, X0] : ((~r3_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | (X0 = X1) | ~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)))))) | (![X1, X0] : ((~r3_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | (X0 = X1) | ~r3_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))))))).
% 0.20/0.50  
% 0.20/0.50  tff(u124,axiom,
% 0.20/0.50      (![X1, X0] : ((r3_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u123,negated_conjecture,
% 0.20/0.50      ((~(![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (X0 = X1) | ~r3_orders_2(sK0,X1,X0))))) | (![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (X0 = X1) | ~r3_orders_2(sK0,X1,X0)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u122,negated_conjecture,
% 0.20/0.50      ((~(![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | (X0 = X1))))) | (![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | (X0 = X1)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u121,negated_conjecture,
% 0.20/0.50      ((~(![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X1))))) | (![X1, X0] : ((~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,X0,X1)))))).
% 0.20/0.50  
% 0.20/0.50  tff(u120,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u119,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | (X1 = X2))))).
% 0.20/0.50  
% 0.20/0.50  tff(u118,negated_conjecture,
% 0.20/0.50      ((~v5_orders_2(sK0)) | v5_orders_2(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u117,negated_conjecture,
% 0.20/0.50      ((~sP3(sK0)) | sP3(sK0))).
% 0.20/0.50  
% 0.20/0.50  % (18602)# SZS output end Saturation.
% 0.20/0.50  % (18602)------------------------------
% 0.20/0.50  % (18602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (18602)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (18602)Memory used [KB]: 6140
% 0.20/0.50  % (18602)Time elapsed: 0.093 s
% 0.20/0.50  % (18602)------------------------------
% 0.20/0.50  % (18602)------------------------------
% 0.20/0.50  % (18622)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (18618)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (18601)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (18596)Success in time 0.151 s
%------------------------------------------------------------------------------
