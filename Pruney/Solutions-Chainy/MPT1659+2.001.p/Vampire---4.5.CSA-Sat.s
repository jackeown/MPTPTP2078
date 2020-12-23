%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:12 EST 2020

% Result     : CounterSatisfiable 1.21s
% Output     : Saturation 1.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   64 (  64 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u28,axiom,
    ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u25,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

cnf(u27,axiom,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u29,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u30,axiom,
    ( ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u22,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u32,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u34,negated_conjecture,
    ( ~ v5_orders_2(sK0)
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u20,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u33,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u38,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u19,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u31,axiom,
    ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u35,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u26,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | v1_xboole_0(X1) )).

cnf(u41,negated_conjecture,
    ( sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u37,negated_conjecture,
    ( sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (792363008)
% 0.13/0.38  ipcrm: permission denied for id (792428548)
% 0.13/0.38  ipcrm: permission denied for id (792461317)
% 0.13/0.38  ipcrm: permission denied for id (792559624)
% 0.13/0.39  ipcrm: permission denied for id (792625164)
% 0.13/0.39  ipcrm: permission denied for id (792690703)
% 0.13/0.39  ipcrm: permission denied for id (792756242)
% 0.13/0.40  ipcrm: permission denied for id (792821786)
% 0.13/0.40  ipcrm: permission denied for id (792887324)
% 0.13/0.41  ipcrm: permission denied for id (792985631)
% 0.13/0.41  ipcrm: permission denied for id (793051169)
% 0.13/0.41  ipcrm: permission denied for id (793116707)
% 0.13/0.41  ipcrm: permission denied for id (793182245)
% 0.13/0.42  ipcrm: permission denied for id (793313321)
% 0.13/0.42  ipcrm: permission denied for id (793346094)
% 0.13/0.42  ipcrm: permission denied for id (793411632)
% 0.13/0.42  ipcrm: permission denied for id (793444401)
% 0.21/0.43  ipcrm: permission denied for id (793542709)
% 0.21/0.43  ipcrm: permission denied for id (793608247)
% 0.21/0.43  ipcrm: permission denied for id (793673785)
% 0.21/0.43  ipcrm: permission denied for id (793706554)
% 0.21/0.44  ipcrm: permission denied for id (793804861)
% 0.21/0.44  ipcrm: permission denied for id (793837630)
% 0.21/0.44  ipcrm: permission denied for id (793935937)
% 0.21/0.44  ipcrm: permission denied for id (794034244)
% 0.21/0.45  ipcrm: permission denied for id (794099782)
% 0.21/0.45  ipcrm: permission denied for id (794132551)
% 0.21/0.45  ipcrm: permission denied for id (794165320)
% 0.21/0.45  ipcrm: permission denied for id (794198089)
% 0.21/0.45  ipcrm: permission denied for id (794263627)
% 0.21/0.46  ipcrm: permission denied for id (794361934)
% 0.21/0.46  ipcrm: permission denied for id (794427472)
% 0.21/0.46  ipcrm: permission denied for id (794460241)
% 0.21/0.47  ipcrm: permission denied for id (794591322)
% 0.21/0.47  ipcrm: permission denied for id (794656861)
% 0.21/0.49  ipcrm: permission denied for id (794820710)
% 0.21/0.49  ipcrm: permission denied for id (794853479)
% 0.21/0.49  ipcrm: permission denied for id (794886249)
% 0.21/0.49  ipcrm: permission denied for id (794919018)
% 0.21/0.49  ipcrm: permission denied for id (794984556)
% 0.21/0.50  ipcrm: permission denied for id (795050095)
% 0.21/0.50  ipcrm: permission denied for id (795082864)
% 0.21/0.50  ipcrm: permission denied for id (795181172)
% 0.21/0.51  ipcrm: permission denied for id (795246711)
% 0.21/0.51  ipcrm: permission denied for id (795279480)
% 0.21/0.51  ipcrm: permission denied for id (795377787)
% 0.21/0.52  ipcrm: permission denied for id (795443325)
% 0.82/0.64  % (2612)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.82/0.65  % (2615)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.82/0.65  % (2619)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.82/0.65  % (2620)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.82/0.65  % (2633)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.82/0.66  % (2623)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.82/0.66  % (2611)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.21/0.66  % (2629)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.21/0.66  % (2613)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.21/0.66  % (2629)Refutation not found, incomplete strategy% (2629)------------------------------
% 1.21/0.66  % (2629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.67  % (2620)Refutation not found, incomplete strategy% (2620)------------------------------
% 1.21/0.67  % (2620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.67  % (2629)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.67  
% 1.21/0.67  % (2629)Memory used [KB]: 1663
% 1.21/0.67  % (2629)Time elapsed: 0.096 s
% 1.21/0.67  % (2629)------------------------------
% 1.21/0.67  % (2629)------------------------------
% 1.21/0.67  % (2613)Refutation not found, incomplete strategy% (2613)------------------------------
% 1.21/0.67  % (2613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.67  % (2613)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.67  
% 1.21/0.67  % (2613)Memory used [KB]: 10490
% 1.21/0.67  % (2613)Time elapsed: 0.089 s
% 1.21/0.67  % (2613)------------------------------
% 1.21/0.67  % (2613)------------------------------
% 1.21/0.67  % (2610)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.21/0.67  % (2620)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.67  
% 1.21/0.67  % (2620)Memory used [KB]: 10490
% 1.21/0.67  % (2620)Time elapsed: 0.004 s
% 1.21/0.67  % (2620)------------------------------
% 1.21/0.67  % (2620)------------------------------
% 1.21/0.67  % SZS status CounterSatisfiable for theBenchmark
% 1.21/0.67  % (2619)# SZS output start Saturation.
% 1.21/0.67  cnf(u21,negated_conjecture,
% 1.21/0.67      v4_orders_2(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u28,axiom,
% 1.21/0.67      r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u25,negated_conjecture,
% 1.21/0.67      ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))).
% 1.21/0.67  
% 1.21/0.67  cnf(u27,axiom,
% 1.21/0.67      r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u23,negated_conjecture,
% 1.21/0.67      l1_orders_2(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u29,axiom,
% 1.21/0.67      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u30,axiom,
% 1.21/0.67      ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u22,negated_conjecture,
% 1.21/0.67      v5_orders_2(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u32,negated_conjecture,
% 1.21/0.67      ~v5_orders_2(sK0) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u34,negated_conjecture,
% 1.21/0.67      ~v5_orders_2(sK0) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u20,negated_conjecture,
% 1.21/0.67      v3_orders_2(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u33,negated_conjecture,
% 1.21/0.67      ~v3_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u38,negated_conjecture,
% 1.21/0.67      ~v3_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u19,negated_conjecture,
% 1.21/0.67      ~v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u31,axiom,
% 1.21/0.67      m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u24,negated_conjecture,
% 1.21/0.67      m1_subset_1(sK1,u1_struct_0(sK0))).
% 1.21/0.67  
% 1.21/0.67  cnf(u35,negated_conjecture,
% 1.21/0.67      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u39,negated_conjecture,
% 1.21/0.67      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 1.21/0.67  
% 1.21/0.67  cnf(u26,axiom,
% 1.21/0.67      ~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)).
% 1.21/0.67  
% 1.21/0.67  cnf(u41,negated_conjecture,
% 1.21/0.67      sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 1.21/0.67  
% 1.21/0.67  cnf(u37,negated_conjecture,
% 1.21/0.67      sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 1.21/0.67  
% 1.21/0.67  % (2619)# SZS output end Saturation.
% 1.21/0.67  % (2619)------------------------------
% 1.21/0.67  % (2619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.67  % (2619)Termination reason: Satisfiable
% 1.21/0.67  
% 1.21/0.67  % (2619)Memory used [KB]: 1663
% 1.21/0.67  % (2619)Time elapsed: 0.089 s
% 1.21/0.67  % (2619)------------------------------
% 1.21/0.67  % (2619)------------------------------
% 1.21/0.67  % (2635)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.21/0.67  % (2450)Success in time 0.301 s
%------------------------------------------------------------------------------
