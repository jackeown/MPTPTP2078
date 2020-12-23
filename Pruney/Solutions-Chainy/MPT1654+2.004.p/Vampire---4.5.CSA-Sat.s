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
% Statistics : Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    0
%              Number of atoms          :   67 (  67 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( v4_orders_2(sK0) )).

cnf(u32,axiom,
    ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u31,axiom,
    ( r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u28,negated_conjecture,
    ( ~ r1_yellow_0(sK0,k5_waybel_0(sK0,sK1))
    | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) )).

cnf(u25,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u34,axiom,
    ( ~ v5_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u23,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u37,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u26,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u38,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u43,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | v2_struct_0(sK0) )).

cnf(u29,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u35,axiom,
    ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u39,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u44,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
    | v2_struct_0(sK0) )).

cnf(u30,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u36,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u22,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u46,negated_conjecture,
    ( sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u41,negated_conjecture,
    ( sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (27551)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.45  % (27552)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (27551)Refutation not found, incomplete strategy% (27551)------------------------------
% 0.21/0.46  % (27551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (27551)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (27551)Memory used [KB]: 10490
% 0.21/0.46  % (27551)Time elapsed: 0.054 s
% 0.21/0.46  % (27551)------------------------------
% 0.21/0.46  % (27551)------------------------------
% 0.21/0.46  % (27560)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.46  % (27552)# SZS output start Saturation.
% 0.21/0.46  cnf(u24,negated_conjecture,
% 0.21/0.46      v4_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u32,axiom,
% 0.21/0.46      r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u31,axiom,
% 0.21/0.46      r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u28,negated_conjecture,
% 0.21/0.46      ~r1_yellow_0(sK0,k5_waybel_0(sK0,sK1)) | sK1 != k1_yellow_0(sK0,k5_waybel_0(sK0,sK1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u25,negated_conjecture,
% 0.21/0.46      v5_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u33,axiom,
% 0.21/0.46      ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u34,axiom,
% 0.21/0.46      ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u23,negated_conjecture,
% 0.21/0.46      v3_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u37,negated_conjecture,
% 0.21/0.46      ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u42,negated_conjecture,
% 0.21/0.46      ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u26,negated_conjecture,
% 0.21/0.46      l1_orders_2(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u38,negated_conjecture,
% 0.21/0.46      ~l1_orders_2(sK0) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u43,negated_conjecture,
% 0.21/0.46      ~l1_orders_2(sK0) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u29,axiom,
% 0.21/0.46      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u35,axiom,
% 0.21/0.46      m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u27,negated_conjecture,
% 0.21/0.46      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u39,negated_conjecture,
% 0.21/0.46      ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u44,negated_conjecture,
% 0.21/0.46      ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u30,axiom,
% 0.21/0.46      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u36,negated_conjecture,
% 0.21/0.46      l1_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u22,negated_conjecture,
% 0.21/0.46      ~v2_struct_0(sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u46,negated_conjecture,
% 0.21/0.46      sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u41,negated_conjecture,
% 0.21/0.46      sK1 = k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.46  
% 0.21/0.46  % (27552)# SZS output end Saturation.
% 0.21/0.46  % (27552)------------------------------
% 0.21/0.46  % (27552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (27552)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (27552)Memory used [KB]: 1663
% 0.21/0.46  % (27552)Time elapsed: 0.043 s
% 0.21/0.46  % (27552)------------------------------
% 0.21/0.46  % (27552)------------------------------
% 0.21/0.46  % (27542)Success in time 0.092 s
%------------------------------------------------------------------------------
