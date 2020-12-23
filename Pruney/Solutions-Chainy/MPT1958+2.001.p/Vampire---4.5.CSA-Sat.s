%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   35 (  35 expanded)
%              Number of leaves         :   35 (  35 expanded)
%              Depth                    :    0
%              Number of atoms          :   73 (  73 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u27,negated_conjecture,
    ( v7_struct_0(sK0)
    | k4_yellow_0(sK0) = k3_yellow_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v7_struct_0(sK0)
    | k4_yellow_0(sK0) != k3_yellow_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u50,negated_conjecture,
    ( v2_yellow_0(sK0) )).

cnf(u48,negated_conjecture,
    ( v1_yellow_0(sK0) )).

cnf(u31,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u35,axiom,
    ( ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v1_yellow_0(X0) )).

cnf(u36,axiom,
    ( ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_yellow_0(X0) )).

cnf(u30,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u80,negated_conjecture,
    ( r1_orders_2(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0)) )).

cnf(u74,negated_conjecture,
    ( r1_orders_2(sK0,k2_yellow_0(sK0,X1),k4_yellow_0(sK0)) )).

cnf(u70,negated_conjecture,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k2_yellow_0(sK0,X0)) )).

cnf(u63,negated_conjecture,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) )).

cnf(u59,negated_conjecture,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0)) )).

cnf(u42,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ r2_orders_2(X0,X2,X1) )).

cnf(u39,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2
    | r2_orders_2(X0,X1,X2) )).

cnf(u109,negated_conjecture,
    ( r2_orders_2(sK0,k2_yellow_0(sK0,X0),k4_yellow_0(sK0))
    | k4_yellow_0(sK0) = k2_yellow_0(sK0,X0) )).

cnf(u99,negated_conjecture,
    ( r2_orders_2(sK0,k3_yellow_0(sK0),k2_yellow_0(sK0,X0))
    | k3_yellow_0(sK0) = k2_yellow_0(sK0,X0) )).

cnf(u89,negated_conjecture,
    ( r2_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))
    | k4_yellow_0(sK0) = k3_yellow_0(sK0) )).

cnf(u119,negated_conjecture,
    ( ~ r2_orders_2(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0)) )).

cnf(u113,negated_conjecture,
    ( ~ r2_orders_2(sK0,k4_yellow_0(sK0),k2_yellow_0(sK0,X1)) )).

cnf(u103,negated_conjecture,
    ( ~ r2_orders_2(sK0,k2_yellow_0(sK0,X1),k3_yellow_0(sK0)) )).

cnf(u93,negated_conjecture,
    ( ~ r2_orders_2(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0)) )).

cnf(u37,axiom,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u45,axiom,
    ( ~ r2_orders_2(X0,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u66,negated_conjecture,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) )).

cnf(u51,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,X1,k4_yellow_0(X0)) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,k3_yellow_0(X0),X1) )).

cnf(u32,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) )).

cnf(u43,axiom,
    ( ~ l1_orders_2(X0)
    | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) )).

cnf(u52,negated_conjecture,
    ( k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (8141)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.45  % (8132)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (8132)Refutation not found, incomplete strategy% (8132)------------------------------
% 0.21/0.46  % (8132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8132)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (8132)Memory used [KB]: 10618
% 0.21/0.46  % (8132)Time elapsed: 0.009 s
% 0.21/0.46  % (8132)------------------------------
% 0.21/0.46  % (8132)------------------------------
% 0.21/0.48  % (8131)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (8135)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (8128)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (8144)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (8128)Refutation not found, incomplete strategy% (8128)------------------------------
% 0.21/0.49  % (8128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8128)Memory used [KB]: 10618
% 0.21/0.49  % (8128)Time elapsed: 0.059 s
% 0.21/0.49  % (8128)------------------------------
% 0.21/0.49  % (8128)------------------------------
% 0.21/0.49  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.49  % (8144)# SZS output start Saturation.
% 0.21/0.49  cnf(u27,negated_conjecture,
% 0.21/0.49      v7_struct_0(sK0) | k4_yellow_0(sK0) = k3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u28,negated_conjecture,
% 0.21/0.49      ~v7_struct_0(sK0) | k4_yellow_0(sK0) != k3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u29,negated_conjecture,
% 0.21/0.49      ~v2_struct_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u50,negated_conjecture,
% 0.21/0.49      v2_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u48,negated_conjecture,
% 0.21/0.49      v1_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u31,negated_conjecture,
% 0.21/0.49      v3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u35,axiom,
% 0.21/0.49      ~v3_yellow_0(X0) | ~l1_orders_2(X0) | v1_yellow_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u36,axiom,
% 0.21/0.49      ~v3_yellow_0(X0) | ~l1_orders_2(X0) | v2_yellow_0(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u30,negated_conjecture,
% 0.21/0.49      v5_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u80,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u74,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k2_yellow_0(sK0,X1),k4_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u70,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k3_yellow_0(sK0),k2_yellow_0(sK0,X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u63,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u59,negated_conjecture,
% 0.21/0.49      r1_orders_2(sK0,k3_yellow_0(sK0),k3_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u42,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~r2_orders_2(X0,X2,X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u39,axiom,
% 0.21/0.49      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2 | r2_orders_2(X0,X1,X2)).
% 0.21/0.49  
% 0.21/0.49  cnf(u109,negated_conjecture,
% 0.21/0.49      r2_orders_2(sK0,k2_yellow_0(sK0,X0),k4_yellow_0(sK0)) | k4_yellow_0(sK0) = k2_yellow_0(sK0,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u99,negated_conjecture,
% 0.21/0.49      r2_orders_2(sK0,k3_yellow_0(sK0),k2_yellow_0(sK0,X0)) | k3_yellow_0(sK0) = k2_yellow_0(sK0,X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u89,negated_conjecture,
% 0.21/0.49      r2_orders_2(sK0,k3_yellow_0(sK0),k4_yellow_0(sK0)) | k4_yellow_0(sK0) = k3_yellow_0(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u119,negated_conjecture,
% 0.21/0.49      ~r2_orders_2(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u113,negated_conjecture,
% 0.21/0.49      ~r2_orders_2(sK0,k4_yellow_0(sK0),k2_yellow_0(sK0,X1))).
% 0.21/0.49  
% 0.21/0.49  cnf(u103,negated_conjecture,
% 0.21/0.49      ~r2_orders_2(sK0,k2_yellow_0(sK0,X1),k3_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u93,negated_conjecture,
% 0.21/0.49      ~r2_orders_2(sK0,k4_yellow_0(sK0),k3_yellow_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u37,axiom,
% 0.21/0.49      ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u45,axiom,
% 0.21/0.49      ~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u66,negated_conjecture,
% 0.21/0.49      m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u53,negated_conjecture,
% 0.21/0.49      m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u51,negated_conjecture,
% 0.21/0.49      m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u40,axiom,
% 0.21/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v2_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,k4_yellow_0(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u41,axiom,
% 0.21/0.49      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1)).
% 0.21/0.49  
% 0.21/0.49  cnf(u32,negated_conjecture,
% 0.21/0.49      l1_orders_2(sK0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u33,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u34,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)).
% 0.21/0.49  
% 0.21/0.49  cnf(u43,axiom,
% 0.21/0.49      ~l1_orders_2(X0) | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))).
% 0.21/0.49  
% 0.21/0.49  cnf(u52,negated_conjecture,
% 0.21/0.49      k4_yellow_0(sK0) = k2_yellow_0(sK0,k1_xboole_0)).
% 0.21/0.49  
% 0.21/0.49  % (8144)# SZS output end Saturation.
% 0.21/0.49  % (8144)------------------------------
% 0.21/0.49  % (8144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8144)Termination reason: Satisfiable
% 0.21/0.49  
% 0.21/0.49  % (8144)Memory used [KB]: 1663
% 0.21/0.49  % (8144)Time elapsed: 0.073 s
% 0.21/0.49  % (8144)------------------------------
% 0.21/0.49  % (8144)------------------------------
% 0.21/0.49  % (8122)Success in time 0.137 s
%------------------------------------------------------------------------------
