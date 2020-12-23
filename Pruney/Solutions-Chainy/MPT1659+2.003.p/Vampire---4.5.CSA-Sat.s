%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:12 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u25,axiom,
    ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u24,axiom,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u22,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u21,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u19,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u18,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u28,axiom,
    ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1) )).

cnf(u39,negated_conjecture,
    ( sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u34,negated_conjecture,
    ( sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u16,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (18629)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (18630)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (18628)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (18628)Refutation not found, incomplete strategy% (18628)------------------------------
% 0.21/0.50  % (18628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (18628)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (18628)Memory used [KB]: 1663
% 0.21/0.50  % (18628)Time elapsed: 0.083 s
% 0.21/0.50  % (18628)------------------------------
% 0.21/0.50  % (18628)------------------------------
% 0.21/0.50  % (18638)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (18617)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (18640)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (18620)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (18631)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (18632)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (18621)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (18630)# SZS output start Saturation.
% 0.21/0.51  cnf(u20,negated_conjecture,
% 0.21/0.51      v4_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,axiom,
% 0.21/0.51      r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,axiom,
% 0.21/0.51      r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u22,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,negated_conjecture,
% 0.21/0.51      v5_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u19,negated_conjecture,
% 0.21/0.51      v3_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u18,negated_conjecture,
% 0.21/0.51      ~v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,axiom,
% 0.21/0.51      m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u17,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,axiom,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,axiom,
% 0.21/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u23,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,negated_conjecture,
% 0.21/0.51      sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,negated_conjecture,
% 0.21/0.51      sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u16,negated_conjecture,
% 0.21/0.51      sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))).
% 0.21/0.51  
% 0.21/0.51  % (18630)# SZS output end Saturation.
% 0.21/0.51  % (18630)------------------------------
% 0.21/0.51  % (18630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18630)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (18630)Memory used [KB]: 6140
% 0.21/0.51  % (18630)Time elapsed: 0.074 s
% 0.21/0.51  % (18630)------------------------------
% 0.21/0.51  % (18630)------------------------------
% 0.21/0.51  % (18640)Refutation not found, incomplete strategy% (18640)------------------------------
% 0.21/0.51  % (18640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18640)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18640)Memory used [KB]: 10618
% 0.21/0.51  % (18640)Time elapsed: 0.053 s
% 0.21/0.51  % (18640)------------------------------
% 0.21/0.51  % (18640)------------------------------
% 0.21/0.51  % (18613)Success in time 0.152 s
%------------------------------------------------------------------------------
