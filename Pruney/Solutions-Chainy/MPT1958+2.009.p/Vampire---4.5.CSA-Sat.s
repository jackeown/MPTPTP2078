%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:50 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( v7_struct_0(sK0)
    | k3_yellow_0(sK0) = k4_yellow_0(sK0) )).

cnf(u25,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u32,axiom,
    ( v2_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u31,axiom,
    ( v1_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u27,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u34,axiom,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u33,axiom,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u41,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,k3_yellow_0(sK0))
    | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_yellow_0(sK0) = X1 )).

cnf(u40,negated_conjecture,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,k4_yellow_0(sK0))
    | k4_yellow_0(sK0) = X0 )).

cnf(u30,axiom,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u29,axiom,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u37,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | X0 = X1 )).

cnf(u26,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u35,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u28,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u24,negated_conjecture,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (18848)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (18829)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (18841)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (18835)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (18841)Refutation not found, incomplete strategy% (18841)------------------------------
% 0.22/0.51  % (18841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (18841)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (18841)Memory used [KB]: 6140
% 0.22/0.51  % (18841)Time elapsed: 0.003 s
% 0.22/0.51  % (18841)------------------------------
% 0.22/0.51  % (18841)------------------------------
% 0.22/0.51  % (18831)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (18848)Refutation not found, incomplete strategy% (18848)------------------------------
% 0.22/0.52  % (18848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18848)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18848)Memory used [KB]: 10746
% 0.22/0.52  % (18848)Time elapsed: 0.054 s
% 0.22/0.52  % (18848)------------------------------
% 0.22/0.52  % (18848)------------------------------
% 0.22/0.52  % (18852)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (18831)# SZS output start Saturation.
% 0.22/0.52  cnf(u23,negated_conjecture,
% 0.22/0.52      v7_struct_0(sK0) | k3_yellow_0(sK0) = k4_yellow_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u25,negated_conjecture,
% 0.22/0.52      ~v2_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u32,axiom,
% 0.22/0.52      v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u31,axiom,
% 0.22/0.52      v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u27,negated_conjecture,
% 0.22/0.52      v3_yellow_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u34,axiom,
% 0.22/0.52      r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u33,axiom,
% 0.22/0.52      r1_orders_2(X0,X1,k4_yellow_0(X0)) | ~v5_orders_2(X0) | ~v2_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u41,negated_conjecture,
% 0.22/0.52      ~r1_orders_2(sK0,X1,k3_yellow_0(sK0)) | ~r1_orders_2(sK0,k3_yellow_0(sK0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_yellow_0(sK0) = X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u40,negated_conjecture,
% 0.22/0.52      ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,k4_yellow_0(sK0)) | k4_yellow_0(sK0) = X0).
% 0.22/0.52  
% 0.22/0.52  cnf(u30,axiom,
% 0.22/0.52      m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u29,axiom,
% 0.22/0.52      m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u37,negated_conjecture,
% 0.22/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | X0 = X1).
% 0.22/0.52  
% 0.22/0.52  cnf(u26,negated_conjecture,
% 0.22/0.52      v5_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u35,axiom,
% 0.22/0.52      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 0.22/0.52  
% 0.22/0.52  cnf(u28,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u24,negated_conjecture,
% 0.22/0.52      k3_yellow_0(sK0) != k4_yellow_0(sK0) | ~v7_struct_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  % (18831)# SZS output end Saturation.
% 0.22/0.52  % (18831)------------------------------
% 0.22/0.52  % (18831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18831)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (18831)Memory used [KB]: 6140
% 0.22/0.52  % (18831)Time elapsed: 0.068 s
% 0.22/0.52  % (18831)------------------------------
% 0.22/0.52  % (18831)------------------------------
% 0.22/0.52  % (18835)Refutation not found, incomplete strategy% (18835)------------------------------
% 0.22/0.52  % (18835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18822)Success in time 0.154 s
%------------------------------------------------------------------------------
