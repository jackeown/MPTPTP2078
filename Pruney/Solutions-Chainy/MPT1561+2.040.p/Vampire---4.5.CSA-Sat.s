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
% DateTime   : Thu Dec  3 13:16:13 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :  168 ( 168 expanded)
%              Number of equality atoms :   69 (  69 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u79,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | r2_hidden(sK2(sK0,X0,sK1),X0) )).

cnf(u83,negated_conjecture,
    ( r2_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u50,axiom,
    ( ~ r2_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X4,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u81,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | r2_hidden(sK3(sK0,X0,sK1),X0) )).

cnf(u86,negated_conjecture,
    ( r1_lattice3(sK0,X0,sK1)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) )).

cnf(u54,axiom,
    ( ~ r1_lattice3(X0,X1,X2)
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | r1_orders_2(X0,X2,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u44,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u60,axiom,
    ( ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2 )).

cnf(u84,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u88,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u57,axiom,
    ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
    | r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u53,axiom,
    ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
    | r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u43,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u58,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u46,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u74,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u96,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK2(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u99,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(sK3(sK0,X0,sK1),X0)
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u102,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,X1,sK1) )).

cnf(u105,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r2_hidden(X1,X0)
    | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,X1) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK2(X0,X1,X2),X1)
    | r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK3(X0,X1,X2),X1)
    | r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
    | r2_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
    | r1_lattice3(X0,X1,X2)
    | ~ l1_orders_2(X0) )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u45,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u49,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u59,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u69,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u42,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u64,axiom,
    ( r2_hidden(sK4(X0,X1),X1)
    | sK4(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u67,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u250,axiom,
    ( ~ r2_hidden(sK4(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK4(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK4(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u65,axiom,
    ( ~ r2_hidden(sK4(X0,X1),X1)
    | sK4(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u68,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u119,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK4(X0,k1_tarski(X1)) = X1 )).

cnf(u144,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK4(X2,k1_tarski(X3)) = X4
    | sK4(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u147,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK4(X11,k1_tarski(X12)) = sK4(X13,k1_tarski(X12))
    | sK4(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u91,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u128,axiom,
    ( sK4(sK4(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK4(X1,k1_tarski(X2)))
    | sK4(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u145,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u75,axiom,
    ( sK4(X0,k1_tarski(X1)) = X0
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u75_001,axiom,
    ( sK4(X0,k1_tarski(X1)) = X0
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u145_002,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u145_003,axiom,
    ( sK4(X7,k1_tarski(X6)) = X7
    | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6))
    | sK4(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u140,axiom,
    ( k1_tarski(X5) = k1_tarski(sK4(X4,k1_tarski(X5)))
    | sK4(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u48,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u208,axiom,
    ( sK4(X2,k1_tarski(X1)) != X0
    | sK4(X2,k1_tarski(X1)) = X2
    | sK4(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u206,axiom,
    ( sK4(X2,k1_tarski(X1)) != X0
    | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1))
    | sK4(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u114,axiom,
    ( X0 != X1
    | sK4(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u120,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK4(X0,k1_tarski(X1)) = X0 )).

cnf(u93,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k1_tarski(sK1))
    | sK1 != k1_yellow_0(sK0,k1_tarski(sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (4062)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.50  % (4083)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.51  % (4075)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.51  % (4057)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (4059)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (4058)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (4060)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (4064)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (4083)Refutation not found, incomplete strategy% (4083)------------------------------
% 0.19/0.51  % (4083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (4083)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (4083)Memory used [KB]: 10746
% 0.19/0.51  % (4083)Time elapsed: 0.065 s
% 0.19/0.51  % (4083)------------------------------
% 0.19/0.51  % (4083)------------------------------
% 0.19/0.52  % (4069)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.52  % (4062)# SZS output start Saturation.
% 0.19/0.52  cnf(u79,negated_conjecture,
% 0.19/0.52      r2_lattice3(sK0,X0,sK1) | r2_hidden(sK2(sK0,X0,sK1),X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u83,negated_conjecture,
% 0.19/0.52      r2_lattice3(sK0,X0,sK1) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.19/0.52  
% 0.19/0.52  cnf(u50,axiom,
% 0.19/0.52      ~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u81,negated_conjecture,
% 0.19/0.52      r1_lattice3(sK0,X0,sK1) | r2_hidden(sK3(sK0,X0,sK1),X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u86,negated_conjecture,
% 0.19/0.52      r1_lattice3(sK0,X0,sK1) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0))).
% 0.19/0.52  
% 0.19/0.52  cnf(u54,axiom,
% 0.19/0.52      ~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u44,negated_conjecture,
% 0.19/0.52      v5_orders_2(sK0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u60,axiom,
% 0.19/0.52      ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2).
% 0.19/0.52  
% 0.19/0.52  cnf(u84,negated_conjecture,
% 0.19/0.52      r1_orders_2(sK0,sK1,sK1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u88,negated_conjecture,
% 0.19/0.52      ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1).
% 0.19/0.52  
% 0.19/0.52  cnf(u57,axiom,
% 0.19/0.52      ~r1_orders_2(X0,X2,sK3(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u53,axiom,
% 0.19/0.52      ~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u43,negated_conjecture,
% 0.19/0.52      v3_orders_2(sK0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u58,axiom,
% 0.19/0.52      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u46,negated_conjecture,
% 0.19/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.19/0.52  
% 0.19/0.52  cnf(u74,negated_conjecture,
% 0.19/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u96,negated_conjecture,
% 0.19/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK2(sK0,X0,sK1),X0) | r1_orders_2(sK0,X1,sK1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u99,negated_conjecture,
% 0.19/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_hidden(sK3(sK0,X0,sK1),X0) | r1_orders_2(sK0,sK1,X1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u102,negated_conjecture,
% 0.19/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK2(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,X1,sK1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u105,negated_conjecture,
% 0.19/0.52      ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | m1_subset_1(sK3(sK0,X0,sK1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u52,axiom,
% 0.19/0.52      ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u56,axiom,
% 0.19/0.52      ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u51,axiom,
% 0.19/0.52      ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u55,axiom,
% 0.19/0.52      ~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u61,axiom,
% 0.19/0.52      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u45,negated_conjecture,
% 0.19/0.52      l1_orders_2(sK0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u49,axiom,
% 0.19/0.52      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u59,axiom,
% 0.19/0.52      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u69,negated_conjecture,
% 0.19/0.52      l1_struct_0(sK0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u42,negated_conjecture,
% 0.19/0.52      ~v2_struct_0(sK0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u64,axiom,
% 0.19/0.52      r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.19/0.52  
% 0.19/0.52  cnf(u67,axiom,
% 0.19/0.52      r2_hidden(X3,k1_tarski(X3))).
% 0.19/0.52  
% 0.19/0.52  cnf(u250,axiom,
% 0.19/0.52      ~r2_hidden(sK4(X14,k1_tarski(X13)),k1_tarski(X13)) | sK4(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK4(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.19/0.52  
% 0.19/0.52  cnf(u65,axiom,
% 0.19/0.52      ~r2_hidden(sK4(X0,X1),X1) | sK4(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.19/0.52  
% 0.19/0.52  cnf(u68,axiom,
% 0.19/0.52      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.19/0.52  
% 0.19/0.52  cnf(u119,axiom,
% 0.19/0.52      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X1).
% 0.19/0.52  
% 0.19/0.52  cnf(u144,axiom,
% 0.19/0.52      ~r2_hidden(X4,k1_tarski(X3)) | sK4(X2,k1_tarski(X3)) = X4 | sK4(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.19/0.52  
% 0.19/0.52  cnf(u147,axiom,
% 0.19/0.52      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK4(X11,k1_tarski(X12)) = sK4(X13,k1_tarski(X12)) | sK4(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 0.19/0.52  
% 0.19/0.52  cnf(u91,negated_conjecture,
% 0.19/0.52      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u128,axiom,
% 0.19/0.52      sK4(sK4(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK4(X1,k1_tarski(X2))) | sK4(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 0.19/0.52  
% 0.19/0.52  cnf(u145,axiom,
% 0.19/0.52      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.19/0.52  
% 0.19/0.52  cnf(u75,axiom,
% 0.19/0.52      sK4(X0,k1_tarski(X1)) = X0 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u75,axiom,
% 0.19/0.52      sK4(X0,k1_tarski(X1)) = X0 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u145,axiom,
% 0.19/0.52      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.19/0.52  
% 0.19/0.52  cnf(u145,axiom,
% 0.19/0.52      sK4(X7,k1_tarski(X6)) = X7 | sK4(X5,k1_tarski(X6)) = sK4(X7,k1_tarski(X6)) | sK4(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.19/0.52  
% 0.19/0.52  cnf(u140,axiom,
% 0.19/0.52      k1_tarski(X5) = k1_tarski(sK4(X4,k1_tarski(X5))) | sK4(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.19/0.52  
% 0.19/0.52  cnf(u48,axiom,
% 0.19/0.52      k1_tarski(X0) = k2_tarski(X0,X0)).
% 0.19/0.52  
% 0.19/0.52  cnf(u208,axiom,
% 0.19/0.52      sK4(X2,k1_tarski(X1)) != X0 | sK4(X2,k1_tarski(X1)) = X2 | sK4(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u206,axiom,
% 0.19/0.52      sK4(X2,k1_tarski(X1)) != X0 | sK4(X0,k1_tarski(X1)) = sK4(X2,k1_tarski(X1)) | sK4(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.19/0.52  
% 0.19/0.52  cnf(u114,axiom,
% 0.19/0.52      X0 != X1 | sK4(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.19/0.52  
% 0.19/0.52  cnf(u120,axiom,
% 0.19/0.52      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK4(X0,k1_tarski(X1)) = X0).
% 0.19/0.52  
% 0.19/0.52  cnf(u93,negated_conjecture,
% 0.19/0.52      sK1 != k2_yellow_0(sK0,k1_tarski(sK1)) | sK1 != k1_yellow_0(sK0,k1_tarski(sK1))).
% 0.19/0.52  
% 0.19/0.52  % (4062)# SZS output end Saturation.
% 0.19/0.52  % (4062)------------------------------
% 0.19/0.52  % (4062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (4062)Termination reason: Satisfiable
% 0.19/0.52  
% 0.19/0.52  % (4062)Memory used [KB]: 1791
% 0.19/0.52  % (4062)Time elapsed: 0.064 s
% 0.19/0.52  % (4062)------------------------------
% 0.19/0.52  % (4062)------------------------------
% 0.19/0.52  % (4054)Success in time 0.165 s
%------------------------------------------------------------------------------
