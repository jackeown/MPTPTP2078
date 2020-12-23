%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:12 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u25,axiom,
    ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

% (23958)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
cnf(u24,axiom,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u22,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u20,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u19,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u30,axiom,
    ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u18,negated_conjecture,
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

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X2) )).

cnf(u28,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u29,axiom,
    ( ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u43,negated_conjecture,
    ( sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u38,negated_conjecture,
    ( sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u17,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (23974)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.46  % (23966)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.46  % (23966)Refutation not found, incomplete strategy% (23966)------------------------------
% 0.21/0.46  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (23966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (23966)Memory used [KB]: 10490
% 0.21/0.46  % (23966)Time elapsed: 0.003 s
% 0.21/0.46  % (23966)------------------------------
% 0.21/0.46  % (23966)------------------------------
% 0.21/0.48  % (23969)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (23969)# SZS output start Saturation.
% 0.21/0.48  cnf(u21,negated_conjecture,
% 0.21/0.48      v4_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u25,axiom,
% 0.21/0.48      r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.21/0.48  
% 0.21/0.48  % (23958)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.48  cnf(u24,axiom,
% 0.21/0.48      r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u23,negated_conjecture,
% 0.21/0.48      l1_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u22,negated_conjecture,
% 0.21/0.48      v5_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u20,negated_conjecture,
% 0.21/0.48      v3_orders_2(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u19,negated_conjecture,
% 0.21/0.48      ~v2_struct_0(sK0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u30,axiom,
% 0.21/0.48      m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u18,negated_conjecture,
% 0.21/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  cnf(u26,axiom,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1).
% 0.21/0.48  
% 0.21/0.48  cnf(u27,axiom,
% 0.21/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1).
% 0.21/0.48  
% 0.21/0.48  cnf(u31,axiom,
% 0.21/0.48      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)).
% 0.21/0.48  
% 0.21/0.48  cnf(u28,axiom,
% 0.21/0.48      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u29,axiom,
% 0.21/0.48      ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)).
% 0.21/0.48  
% 0.21/0.48  cnf(u43,negated_conjecture,
% 0.21/0.48      sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.48  
% 0.21/0.48  cnf(u38,negated_conjecture,
% 0.21/0.48      sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.48  
% 0.21/0.48  cnf(u17,negated_conjecture,
% 0.21/0.48      sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) | ~r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))).
% 0.21/0.48  
% 0.21/0.48  % (23969)# SZS output end Saturation.
% 0.21/0.48  % (23969)------------------------------
% 0.21/0.48  % (23969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23969)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (23969)Memory used [KB]: 6140
% 0.21/0.48  % (23969)Time elapsed: 0.076 s
% 0.21/0.48  % (23969)------------------------------
% 0.21/0.48  % (23969)------------------------------
% 0.21/0.49  % (23968)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (23978)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (23955)Success in time 0.134 s
%------------------------------------------------------------------------------
