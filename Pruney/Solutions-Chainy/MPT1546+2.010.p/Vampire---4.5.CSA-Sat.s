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
% DateTime   : Thu Dec  3 13:16:01 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   59 (  59 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u26,negated_conjecture,
    ( v1_lattice3(sK0) )).

cnf(u25,negated_conjecture,
    ( v5_orders_2(sK0) )).

% (16260)Refutation not found, incomplete strategy% (16260)------------------------------
% (16260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16260)Termination reason: Refutation not found, incomplete strategy

% (16260)Memory used [KB]: 10618
% (16260)Time elapsed: 0.086 s
% (16260)------------------------------
% (16260)------------------------------
cnf(u49,negated_conjecture,
    ( r1_orders_2(sK0,X0,X0)
    | v2_struct_0(sK0)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u48,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | v2_struct_0(sK0) )).

cnf(u47,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) )).

cnf(u30,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u24,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X1)
    | v2_struct_0(X0) )).

cnf(u27,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u45,negated_conjecture,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0)
    | v2_struct_0(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u40,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u41,axiom,
    ( ~ v2_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1)) )).

cnf(u42,axiom,
    ( ~ v2_struct_0(X0)
    | ~ v1_xboole_0(X1)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) = X1 )).

cnf(u35,axiom,
    ( r2_hidden(X1,X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u36,axiom,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u38,axiom,
    ( m1_subset_1(X1,X0)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) )).

cnf(u29,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u46,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0)
    | v2_struct_0(sK0) )).

cnf(u34,axiom,
    ( v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | ~ v2_struct_0(X0) )).

cnf(u37,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X1) )).

cnf(u39,axiom,
    ( ~ v1_xboole_0(X0)
    | X0 = X1
    | ~ v1_xboole_0(X1) )).

cnf(u31,negated_conjecture,
    ( sK1 != k13_lattice3(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (16262)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (16261)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (16259)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (16259)Refutation not found, incomplete strategy% (16259)------------------------------
% 0.21/0.50  % (16259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (16259)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16259)Memory used [KB]: 10618
% 0.21/0.50  % (16259)Time elapsed: 0.088 s
% 0.21/0.50  % (16259)------------------------------
% 0.21/0.50  % (16259)------------------------------
% 0.21/0.50  % (16275)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (16260)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (16258)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (16266)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (16280)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (16267)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (16266)# SZS output start Saturation.
% 0.21/0.51  cnf(u26,negated_conjecture,
% 0.21/0.51      v1_lattice3(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,negated_conjecture,
% 0.21/0.51      v5_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  % (16260)Refutation not found, incomplete strategy% (16260)------------------------------
% 0.21/0.51  % (16260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16260)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16260)Memory used [KB]: 10618
% 0.21/0.51  % (16260)Time elapsed: 0.086 s
% 0.21/0.51  % (16260)------------------------------
% 0.21/0.51  % (16260)------------------------------
% 0.21/0.51  cnf(u49,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,X0,X0) | v2_struct_0(sK0) | ~v1_xboole_0(X0) | ~v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u48,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK2,sK2) | v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u47,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u30,negated_conjecture,
% 0.21/0.51      r1_orders_2(sK0,sK2,sK1) | sK1 = k13_lattice3(sK0,sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u24,negated_conjecture,
% 0.21/0.51      v3_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,axiom,
% 0.21/0.51      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X1) | v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,negated_conjecture,
% 0.21/0.51      l1_orders_2(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u45,negated_conjecture,
% 0.21/0.51      ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0) | v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,axiom,
% 0.21/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u40,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u41,axiom,
% 0.21/0.51      ~v2_struct_0(X1) | v1_xboole_0(X0) | ~l1_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u42,axiom,
% 0.21/0.51      ~v2_struct_0(X0) | ~v1_xboole_0(X1) | ~l1_struct_0(X0) | u1_struct_0(X0) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u35,axiom,
% 0.21/0.51      r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,axiom,
% 0.21/0.51      ~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,axiom,
% 0.21/0.51      m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u29,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.51  
% 0.21/0.51  cnf(u46,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0) | v2_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,axiom,
% 0.21/0.51      v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,axiom,
% 0.21/0.51      ~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u39,axiom,
% 0.21/0.51      ~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      sK1 != k13_lattice3(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  % (16266)# SZS output end Saturation.
% 0.21/0.51  % (16266)------------------------------
% 0.21/0.51  % (16266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16266)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (16266)Memory used [KB]: 1663
% 0.21/0.51  % (16266)Time elapsed: 0.087 s
% 0.21/0.51  % (16266)------------------------------
% 0.21/0.51  % (16266)------------------------------
% 0.21/0.51  % (16269)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (16267)Refutation not found, incomplete strategy% (16267)------------------------------
% 0.21/0.51  % (16267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16267)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16267)Memory used [KB]: 10490
% 0.21/0.51  % (16267)Time elapsed: 0.083 s
% 0.21/0.51  % (16267)------------------------------
% 0.21/0.51  % (16267)------------------------------
% 0.21/0.51  % (16256)Success in time 0.14 s
%------------------------------------------------------------------------------
