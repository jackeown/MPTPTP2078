%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:12 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u113,negated_conjecture,
    ( ~ ( sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

tff(u112,negated_conjecture,(
    sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u111,negated_conjecture,(
    sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

tff(u110,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

tff(u109,axiom,(
    ! [X3,X2] :
      ( v1_xboole_0(k1_zfmisc_1(X3))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,X3)
      | k6_domain_1(k1_zfmisc_1(X3),k6_domain_1(X3,X2)) = k1_tarski(k6_domain_1(X3,X2)) ) )).

tff(u108,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) )).

tff(u107,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) )).

tff(u106,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u105,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) )).

tff(u104,negated_conjecture,(
    m1_subset_1(sK1,u1_struct_0(sK0)) )).

tff(u103,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) )).

tff(u102,negated_conjecture,(
    ~ v2_struct_0(sK0) )).

tff(u101,negated_conjecture,(
    v3_orders_2(sK0) )).

tff(u100,negated_conjecture,(
    v5_orders_2(sK0) )).

tff(u99,negated_conjecture,(
    l1_orders_2(sK0) )).

tff(u98,negated_conjecture,
    ( ~ ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

tff(u97,axiom,(
    ! [X1,X0] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (22374)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.47  % (22385)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.48  % (22375)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.48  % (22375)Refutation not found, incomplete strategy% (22375)------------------------------
% 0.22/0.48  % (22375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22375)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22375)Memory used [KB]: 10490
% 0.22/0.48  % (22375)Time elapsed: 0.070 s
% 0.22/0.48  % (22375)------------------------------
% 0.22/0.48  % (22375)------------------------------
% 0.22/0.48  % (22394)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.48  % (22378)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.49  % (22373)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (22382)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (22382)Refutation not found, incomplete strategy% (22382)------------------------------
% 0.22/0.49  % (22382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22382)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22382)Memory used [KB]: 10490
% 0.22/0.49  % (22382)Time elapsed: 0.002 s
% 0.22/0.49  % (22382)------------------------------
% 0.22/0.49  % (22382)------------------------------
% 0.22/0.49  % (22391)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.49  % (22376)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (22372)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.50  % (22384)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (22387)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (22384)# SZS output start Saturation.
% 0.22/0.50  tff(u113,negated_conjecture,
% 0.22/0.50      ((~(sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))) | (sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u112,negated_conjecture,
% 0.22/0.50      (sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u111,negated_conjecture,
% 0.22/0.50      (sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u110,negated_conjecture,
% 0.22/0.50      ((~v1_xboole_0(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u109,axiom,
% 0.22/0.50      (![X3, X2] : ((v1_xboole_0(k1_zfmisc_1(X3)) | v1_xboole_0(X3) | ~m1_subset_1(X2,X3) | (k6_domain_1(k1_zfmisc_1(X3),k6_domain_1(X3,X2)) = k1_tarski(k6_domain_1(X3,X2))))))).
% 0.22/0.50  
% 0.22/0.50  tff(u108,axiom,
% 0.22/0.50      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u107,axiom,
% 0.22/0.50      (![X1, X0] : ((~m1_subset_1(X1,X0) | v1_xboole_0(X0) | (k6_domain_1(X0,X1) = k1_tarski(X1)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u106,axiom,
% 0.22/0.50      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u105,axiom,
% 0.22/0.50      (![X1, X0] : ((~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | (k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u104,negated_conjecture,
% 0.22/0.50      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u103,axiom,
% 0.22/0.50      (![X1, X0] : ((m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u102,negated_conjecture,
% 0.22/0.50      ~v2_struct_0(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u101,negated_conjecture,
% 0.22/0.50      v3_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u100,negated_conjecture,
% 0.22/0.50      v5_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u99,negated_conjecture,
% 0.22/0.50      l1_orders_2(sK0)).
% 0.22/0.50  
% 0.22/0.50  tff(u98,negated_conjecture,
% 0.22/0.50      ((~~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u97,axiom,
% 0.22/0.50      (![X1, X0] : ((r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))))).
% 0.22/0.50  
% 0.22/0.50  % (22384)# SZS output end Saturation.
% 0.22/0.50  % (22384)------------------------------
% 0.22/0.50  % (22384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22384)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (22384)Memory used [KB]: 10618
% 0.22/0.50  % (22384)Time elapsed: 0.098 s
% 0.22/0.50  % (22384)------------------------------
% 0.22/0.50  % (22384)------------------------------
% 0.22/0.50  % (22378)Refutation not found, incomplete strategy% (22378)------------------------------
% 0.22/0.50  % (22378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22378)Memory used [KB]: 10618
% 0.22/0.50  % (22378)Time elapsed: 0.094 s
% 0.22/0.50  % (22378)------------------------------
% 0.22/0.50  % (22378)------------------------------
% 0.22/0.51  % (22381)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (22377)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (22396)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (22396)Refutation not found, incomplete strategy% (22396)------------------------------
% 0.22/0.51  % (22396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22396)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22396)Memory used [KB]: 10618
% 0.22/0.51  % (22396)Time elapsed: 0.102 s
% 0.22/0.51  % (22396)------------------------------
% 0.22/0.51  % (22396)------------------------------
% 0.22/0.51  % (22390)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (22393)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (22390)Refutation not found, incomplete strategy% (22390)------------------------------
% 0.22/0.51  % (22390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22390)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22390)Memory used [KB]: 1663
% 0.22/0.51  % (22390)Time elapsed: 0.105 s
% 0.22/0.51  % (22390)------------------------------
% 0.22/0.51  % (22390)------------------------------
% 0.22/0.51  % (22367)Success in time 0.156 s
%------------------------------------------------------------------------------
