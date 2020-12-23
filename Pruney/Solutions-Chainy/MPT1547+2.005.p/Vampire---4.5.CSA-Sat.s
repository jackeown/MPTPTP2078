%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:02 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u88,negated_conjecture,
    ( ~ ( sK1 != k12_lattice3(sK0,sK1,sK2) )
    | sK1 != k12_lattice3(sK0,sK1,sK2) )).

tff(u87,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) )).

tff(u86,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u85,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u84,axiom,(
    ! [X1,X0,X2] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u83,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u82,negated_conjecture,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK1,X0)
      | r3_orders_2(sK0,sK1,X0) ) )).

tff(u81,negated_conjecture,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r3_orders_2(sK0,X0,X1) ) )).

tff(u80,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u79,negated_conjecture,(
    m1_subset_1(sK2,u1_struct_0(sK0)) )).

tff(u78,negated_conjecture,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK1,sK2) )).

tff(u77,negated_conjecture,(
    r3_orders_2(sK0,sK1,sK1) )).

tff(u76,negated_conjecture,(
    r3_orders_2(sK0,sK2,sK2) )).

tff(u75,axiom,(
    ! [X1,X0] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) )).

tff(u74,negated_conjecture,(
    ! [X1] :
      ( ~ r1_orders_2(sK0,sK2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK2,X1) ) )).

tff(u73,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u72,negated_conjecture,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK1,sK2) )).

tff(u71,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK1) )).

tff(u70,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u69,negated_conjecture,(
    v2_lattice3(sK0) )).

tff(u68,negated_conjecture,(
    v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:55:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (27902)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.46  % (27902)Refutation not found, incomplete strategy% (27902)------------------------------
% 0.20/0.46  % (27902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27902)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (27902)Memory used [KB]: 10618
% 0.20/0.46  % (27902)Time elapsed: 0.045 s
% 0.20/0.46  % (27902)------------------------------
% 0.20/0.46  % (27902)------------------------------
% 0.20/0.46  % (27912)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.47  % (27894)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.47  % (27898)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  % (27901)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (27901)Refutation not found, incomplete strategy% (27901)------------------------------
% 0.20/0.48  % (27901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27901)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (27901)Memory used [KB]: 6140
% 0.20/0.48  % (27901)Time elapsed: 0.074 s
% 0.20/0.48  % (27901)------------------------------
% 0.20/0.48  % (27901)------------------------------
% 0.20/0.48  % (27914)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.48  % (27914)Refutation not found, incomplete strategy% (27914)------------------------------
% 0.20/0.48  % (27914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27914)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (27914)Memory used [KB]: 6012
% 0.20/0.48  % (27914)Time elapsed: 0.078 s
% 0.20/0.48  % (27914)------------------------------
% 0.20/0.48  % (27914)------------------------------
% 0.20/0.49  % (27916)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (27908)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (27896)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (27917)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (27908)# SZS output start Saturation.
% 0.20/0.50  tff(u88,negated_conjecture,
% 0.20/0.50      ((~(sK1 != k12_lattice3(sK0,sK1,sK2))) | (sK1 != k12_lattice3(sK0,sK1,sK2)))).
% 0.20/0.50  
% 0.20/0.50  tff(u87,axiom,
% 0.20/0.50      (![X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u86,negated_conjecture,
% 0.20/0.50      ~v2_struct_0(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u85,negated_conjecture,
% 0.20/0.50      v3_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u84,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u83,negated_conjecture,
% 0.20/0.50      l1_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u82,negated_conjecture,
% 0.20/0.50      (![X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | r3_orders_2(sK0,sK1,X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u81,negated_conjecture,
% 0.20/0.50      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u80,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u79,negated_conjecture,
% 0.20/0.50      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.20/0.50  
% 0.20/0.50  tff(u78,negated_conjecture,
% 0.20/0.50      ((~r3_orders_2(sK0,sK1,sK2)) | r3_orders_2(sK0,sK1,sK2))).
% 0.20/0.50  
% 0.20/0.50  tff(u77,negated_conjecture,
% 0.20/0.50      r3_orders_2(sK0,sK1,sK1)).
% 0.20/0.50  
% 0.20/0.50  tff(u76,negated_conjecture,
% 0.20/0.50      r3_orders_2(sK0,sK2,sK2)).
% 0.20/0.50  
% 0.20/0.50  tff(u75,axiom,
% 0.20/0.50      (![X1, X0] : ((r3_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u74,negated_conjecture,
% 0.20/0.50      (![X1] : ((~r1_orders_2(sK0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_orders_2(sK0,sK2,X1))))).
% 0.20/0.50  
% 0.20/0.50  tff(u73,axiom,
% 0.20/0.50      (![X1, X0, X2] : ((r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.20/0.50  
% 0.20/0.50  tff(u72,negated_conjecture,
% 0.20/0.50      ((~r3_orders_2(sK0,sK1,sK2)) | r1_orders_2(sK0,sK1,sK2))).
% 0.20/0.50  
% 0.20/0.50  tff(u71,negated_conjecture,
% 0.20/0.50      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.50  
% 0.20/0.50  tff(u70,negated_conjecture,
% 0.20/0.50      r1_orders_2(sK0,sK2,sK2)).
% 0.20/0.50  
% 0.20/0.50  tff(u69,negated_conjecture,
% 0.20/0.50      v2_lattice3(sK0)).
% 0.20/0.50  
% 0.20/0.50  tff(u68,negated_conjecture,
% 0.20/0.50      v5_orders_2(sK0)).
% 0.20/0.50  
% 0.20/0.50  % (27908)# SZS output end Saturation.
% 0.20/0.50  % (27908)------------------------------
% 0.20/0.50  % (27908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27908)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (27908)Memory used [KB]: 10618
% 0.20/0.50  % (27908)Time elapsed: 0.066 s
% 0.20/0.50  % (27908)------------------------------
% 0.20/0.50  % (27908)------------------------------
% 0.20/0.50  % (27893)Success in time 0.149 s
%------------------------------------------------------------------------------
