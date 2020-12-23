%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:08 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   68 (  68 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u25,axiom,
    ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u24,axiom,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

cnf(u20,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u26,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u27,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u28,axiom,
    ( v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u29,axiom,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u33,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u37,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u21,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u30,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u32,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) )).

cnf(u18,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u31,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u17,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u35,negated_conjecture,
    ( sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:00:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (25582)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.48  % (25592)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (25592)Refutation not found, incomplete strategy% (25592)------------------------------
% 0.21/0.48  % (25592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (25592)Memory used [KB]: 10490
% 0.21/0.48  % (25592)Time elapsed: 0.003 s
% 0.21/0.48  % (25592)------------------------------
% 0.21/0.48  % (25592)------------------------------
% 0.21/0.48  % (25583)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (25596)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.49  % (25591)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (25591)# SZS output start Saturation.
% 0.21/0.49  cnf(u19,negated_conjecture,
% 0.21/0.49      v4_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u25,axiom,
% 0.21/0.49      r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u24,axiom,
% 0.21/0.49      r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u23,negated_conjecture,
% 0.21/0.49      ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u20,negated_conjecture,
% 0.21/0.49      v5_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u26,axiom,
% 0.21/0.49      ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u27,axiom,
% 0.21/0.49      ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u28,axiom,
% 0.21/0.49      v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,axiom,
% 0.21/0.49      m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u22,negated_conjecture,
% 0.21/0.49      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u37,negated_conjecture,
% 0.21/0.49      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u21,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,negated_conjecture,
% 0.21/0.49      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,negated_conjecture,
% 0.21/0.49      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u18,negated_conjecture,
% 0.21/0.49      v3_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,negated_conjecture,
% 0.21/0.49      ~v3_orders_2(sK0) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u36,negated_conjecture,
% 0.21/0.49      ~v3_orders_2(sK0) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u17,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u39,negated_conjecture,
% 0.21/0.49      sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,negated_conjecture,
% 0.21/0.49      sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.49  
% 0.21/0.49  % (25591)# SZS output end Saturation.
% 0.21/0.49  % (25591)------------------------------
% 0.21/0.49  % (25591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25591)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (25591)Memory used [KB]: 1663
% 0.21/0.49  % (25591)Time elapsed: 0.074 s
% 0.21/0.49  % (25591)------------------------------
% 0.21/0.49  % (25591)------------------------------
% 0.21/0.49  % (25577)Success in time 0.132 s
%------------------------------------------------------------------------------
