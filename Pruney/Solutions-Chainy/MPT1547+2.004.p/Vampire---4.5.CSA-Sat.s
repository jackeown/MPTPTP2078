%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:02 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   70 (  70 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u134,negated_conjecture,
    ( ~ ( sK1 != k12_lattice3(sK0,sK1,sK2) )
    | sK1 != k12_lattice3(sK0,sK1,sK2) )).

tff(u133,negated_conjecture,(
    k12_lattice3(sK0,sK1,sK1) = k11_lattice3(sK0,sK1,sK1) )).

tff(u132,negated_conjecture,(
    k12_lattice3(sK0,sK2,sK1) = k11_lattice3(sK0,sK2,sK1) )).

tff(u131,negated_conjecture,(
    k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2) )).

tff(u130,negated_conjecture,(
    k12_lattice3(sK0,sK2,sK2) = k11_lattice3(sK0,sK2,sK2) )).

tff(u129,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u128,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u127,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u126,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u125,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u124,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK2,X1) = k11_lattice3(sK0,sK2,X1) ) )).

tff(u123,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,sK1,X0) = k11_lattice3(sK0,sK1,X0) ) )).

tff(u122,negated_conjecture,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X1)
      | r3_orders_2(sK0,sK2,X1) ) )).

tff(u121,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0) ) )).

tff(u120,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK1,X0)
      | r3_orders_2(sK0,sK1,X0) ) )).

tff(u119,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r3_orders_2(sK0,X0,X1) ) )).

tff(u118,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u117,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u116,negated_conjecture,
    ( ~ ~ r3_orders_2(sK0,sK2,sK1)
    | ~ r3_orders_2(sK0,sK2,sK1) )).

tff(u115,negated_conjecture,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK1,sK2) )).

tff(u114,negated_conjecture,(
    r3_orders_2(sK0,sK1,sK1) )).

tff(u113,negated_conjecture,(
    r3_orders_2(sK0,sK2,sK2) )).

tff(u112,negated_conjecture,
    ( ~ ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1) )).

tff(u111,axiom,(
    ! [X1,X0] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u110,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u109,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK1) )).

tff(u108,negated_conjecture,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) )).

tff(u107,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u106,negated_conjecture,(
    v2_lattice3(sK0) )).

tff(u105,axiom,(
    ! [X1,X0,X2] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) )).

tff(u104,negated_conjecture,(
    v5_orders_2(sK0) )).

% (1308)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (1311)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (1306)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.48  % (1310)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (1319)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (1311)Refutation not found, incomplete strategy% (1311)------------------------------
% 0.21/0.49  % (1311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1328)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (1311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1311)Memory used [KB]: 10618
% 0.21/0.50  % (1311)Time elapsed: 0.089 s
% 0.21/0.50  % (1311)------------------------------
% 0.21/0.50  % (1311)------------------------------
% 0.21/0.50  % (1326)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (1325)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (1329)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (1309)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (1319)# SZS output start Saturation.
% 0.21/0.50  tff(u134,negated_conjecture,
% 0.21/0.50      ((~(sK1 != k12_lattice3(sK0,sK1,sK2))) | (sK1 != k12_lattice3(sK0,sK1,sK2)))).
% 0.21/0.50  
% 0.21/0.50  tff(u133,negated_conjecture,
% 0.21/0.50      (k12_lattice3(sK0,sK1,sK1) = k11_lattice3(sK0,sK1,sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u132,negated_conjecture,
% 0.21/0.50      (k12_lattice3(sK0,sK2,sK1) = k11_lattice3(sK0,sK2,sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u131,negated_conjecture,
% 0.21/0.50      (k12_lattice3(sK0,sK1,sK2) = k11_lattice3(sK0,sK1,sK2))).
% 0.21/0.50  
% 0.21/0.50  tff(u130,negated_conjecture,
% 0.21/0.50      (k12_lattice3(sK0,sK2,sK2) = k11_lattice3(sK0,sK2,sK2))).
% 0.21/0.50  
% 0.21/0.50  tff(u129,axiom,
% 0.21/0.50      (![X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u128,negated_conjecture,
% 0.21/0.50      ~v2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u127,negated_conjecture,
% 0.21/0.50      v3_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u126,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u125,negated_conjecture,
% 0.21/0.50      l1_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u124,negated_conjecture,
% 0.21/0.50      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | (k12_lattice3(sK0,sK2,X1) = k11_lattice3(sK0,sK2,X1)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u123,negated_conjecture,
% 0.21/0.50      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | (k12_lattice3(sK0,sK1,X0) = k11_lattice3(sK0,sK1,X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u122,negated_conjecture,
% 0.21/0.50      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X1) | r3_orders_2(sK0,sK2,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u121,negated_conjecture,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | (k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u120,negated_conjecture,
% 0.21/0.50      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | r3_orders_2(sK0,sK1,X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u119,negated_conjecture,
% 0.21/0.50      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1))))).
% 0.21/0.50  
% 0.21/0.50  tff(u118,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u117,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.50  
% 0.21/0.50  tff(u116,negated_conjecture,
% 0.21/0.50      ((~~r3_orders_2(sK0,sK2,sK1)) | ~r3_orders_2(sK0,sK2,sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u115,negated_conjecture,
% 0.21/0.50      ((~r3_orders_2(sK0,sK1,sK2)) | r3_orders_2(sK0,sK1,sK2))).
% 0.21/0.50  
% 0.21/0.50  tff(u114,negated_conjecture,
% 0.21/0.50      r3_orders_2(sK0,sK1,sK1)).
% 0.21/0.50  
% 0.21/0.50  tff(u113,negated_conjecture,
% 0.21/0.50      r3_orders_2(sK0,sK2,sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u112,negated_conjecture,
% 0.21/0.50      ((~~r1_orders_2(sK0,sK2,sK1)) | ~r1_orders_2(sK0,sK2,sK1))).
% 0.21/0.50  
% 0.21/0.50  tff(u111,axiom,
% 0.21/0.50      (![X1, X0] : ((r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u110,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.21/0.50  
% 0.21/0.50  tff(u109,negated_conjecture,
% 0.21/0.50      r1_orders_2(sK0,sK1,sK1)).
% 0.21/0.50  
% 0.21/0.50  tff(u108,negated_conjecture,
% 0.21/0.50      ((~r3_orders_2(sK0,sK1,sK2)) | r1_orders_2(sK0,sK1,sK2))).
% 0.21/0.50  
% 0.21/0.50  tff(u107,negated_conjecture,
% 0.21/0.50      r1_orders_2(sK0,sK2,sK2)).
% 0.21/0.50  
% 0.21/0.50  tff(u106,negated_conjecture,
% 0.21/0.50      v2_lattice3(sK0)).
% 0.21/0.50  
% 0.21/0.50  tff(u105,axiom,
% 0.21/0.50      (![X1, X0, X2] : ((~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)))))).
% 0.21/0.50  
% 0.21/0.50  tff(u104,negated_conjecture,
% 0.21/0.50      v5_orders_2(sK0)).
% 0.21/0.50  
% 0.21/0.50  % (1308)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (1319)# SZS output end Saturation.
% 0.21/0.50  % (1319)------------------------------
% 0.21/0.50  % (1319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1319)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (1319)Memory used [KB]: 10618
% 0.21/0.50  % (1319)Time elapsed: 0.105 s
% 0.21/0.50  % (1319)------------------------------
% 0.21/0.50  % (1319)------------------------------
% 0.21/0.50  % (1320)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (1307)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (1328)Refutation not found, incomplete strategy% (1328)------------------------------
% 0.21/0.50  % (1328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1328)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1328)Memory used [KB]: 1663
% 0.21/0.50  % (1328)Time elapsed: 0.104 s
% 0.21/0.50  % (1328)------------------------------
% 0.21/0.50  % (1328)------------------------------
% 0.21/0.50  % (1308)Refutation not found, incomplete strategy% (1308)------------------------------
% 0.21/0.50  % (1308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1305)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (1308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1308)Memory used [KB]: 10618
% 0.21/0.50  % (1308)Time elapsed: 0.092 s
% 0.21/0.50  % (1308)------------------------------
% 0.21/0.50  % (1308)------------------------------
% 0.21/0.51  % (1304)Success in time 0.148 s
%------------------------------------------------------------------------------
