%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:00 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
    ( ~ ( sK1 != k13_lattice3(sK0,sK1,sK2) )
    | sK1 != k13_lattice3(sK0,sK1,sK2) )).

tff(u87,axiom,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
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
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK2,X1)
      | r3_orders_2(sK0,sK2,X1) ) )).

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

tff(u78,axiom,(
    ! [X1,X0] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) )).

tff(u77,negated_conjecture,(
    r3_orders_2(sK0,sK1,sK1) )).

tff(u76,negated_conjecture,(
    r3_orders_2(sK0,sK2,sK2) )).

tff(u75,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK2,sK1) )).

tff(u74,negated_conjecture,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,sK1,X0) ) )).

tff(u73,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) )).

tff(u72,negated_conjecture,(
    r1_orders_2(sK0,sK1,sK1) )).

tff(u71,negated_conjecture,(
    r1_orders_2(sK0,sK2,sK2) )).

tff(u70,axiom,(
    ! [X1,X0,X2] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) )).

tff(u69,negated_conjecture,(
    v1_lattice3(sK0) )).

tff(u68,negated_conjecture,(
    v5_orders_2(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:13:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (6280)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (6277)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (6279)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (6275)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (6297)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (6278)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (6278)Refutation not found, incomplete strategy% (6278)------------------------------
% 0.22/0.52  % (6278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6278)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6278)Memory used [KB]: 10618
% 0.22/0.52  % (6278)Time elapsed: 0.100 s
% 0.22/0.52  % (6278)------------------------------
% 0.22/0.52  % (6278)------------------------------
% 0.22/0.52  % (6281)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (6281)Refutation not found, incomplete strategy% (6281)------------------------------
% 0.22/0.52  % (6281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6281)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6281)Memory used [KB]: 10618
% 0.22/0.52  % (6281)Time elapsed: 0.102 s
% 0.22/0.52  % (6281)------------------------------
% 0.22/0.52  % (6281)------------------------------
% 0.22/0.52  % (6276)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (6293)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (6286)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (6289)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (6286)Refutation not found, incomplete strategy% (6286)------------------------------
% 0.22/0.52  % (6286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6286)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6286)Memory used [KB]: 1663
% 0.22/0.52  % (6286)Time elapsed: 0.100 s
% 0.22/0.52  % (6286)------------------------------
% 0.22/0.52  % (6286)------------------------------
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (6289)# SZS output start Saturation.
% 0.22/0.52  tff(u88,negated_conjecture,
% 0.22/0.52      ((~(sK1 != k13_lattice3(sK0,sK1,sK2))) | (sK1 != k13_lattice3(sK0,sK1,sK2)))).
% 0.22/0.52  
% 0.22/0.52  tff(u87,axiom,
% 0.22/0.52      (![X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u86,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u85,negated_conjecture,
% 0.22/0.52      v3_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u84,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u83,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u82,negated_conjecture,
% 0.22/0.52      (![X1] : ((~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2,X1) | r3_orders_2(sK0,sK2,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u81,negated_conjecture,
% 0.22/0.52      (![X1, X0] : ((~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r3_orders_2(sK0,X0,X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u80,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u79,negated_conjecture,
% 0.22/0.52      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.52  
% 0.22/0.52  tff(u78,axiom,
% 0.22/0.52      (![X1, X0] : ((r3_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))))).
% 0.22/0.52  
% 0.22/0.52  tff(u77,negated_conjecture,
% 0.22/0.52      r3_orders_2(sK0,sK1,sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u76,negated_conjecture,
% 0.22/0.52      r3_orders_2(sK0,sK2,sK2)).
% 0.22/0.52  
% 0.22/0.52  tff(u75,negated_conjecture,
% 0.22/0.52      ((~r1_orders_2(sK0,sK2,sK1)) | r3_orders_2(sK0,sK2,sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u74,negated_conjecture,
% 0.22/0.52      (![X0] : ((~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_orders_2(sK0,sK1,X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u73,negated_conjecture,
% 0.22/0.52      ((~r1_orders_2(sK0,sK2,sK1)) | r1_orders_2(sK0,sK2,sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u72,negated_conjecture,
% 0.22/0.52      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.52  
% 0.22/0.52  tff(u71,negated_conjecture,
% 0.22/0.52      r1_orders_2(sK0,sK2,sK2)).
% 0.22/0.52  
% 0.22/0.52  tff(u70,axiom,
% 0.22/0.52      (![X1, X0, X2] : ((r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))))).
% 0.22/0.52  
% 0.22/0.52  tff(u69,negated_conjecture,
% 0.22/0.52      v1_lattice3(sK0)).
% 0.22/0.52  
% 0.22/0.52  tff(u68,negated_conjecture,
% 0.22/0.52      v5_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  % (6289)# SZS output end Saturation.
% 0.22/0.52  % (6289)------------------------------
% 0.22/0.52  % (6289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6289)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (6289)Memory used [KB]: 10618
% 0.22/0.52  % (6289)Time elapsed: 0.107 s
% 0.22/0.52  % (6289)------------------------------
% 0.22/0.52  % (6289)------------------------------
% 0.22/0.52  % (6274)Success in time 0.158 s
%------------------------------------------------------------------------------
