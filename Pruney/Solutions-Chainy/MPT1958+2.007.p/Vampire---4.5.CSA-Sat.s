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
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :  120 ( 120 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u41,negated_conjecture,
    ( v7_struct_0(sK0)
    | k3_yellow_0(sK0) = k4_yellow_0(sK0) )).

cnf(u50,axiom,
    ( r1_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u52,axiom,
    ( r2_yellow_0(X0,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u37,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u60,axiom,
    ( r2_lattice3(X0,X2,sK1(X0,X1,X2))
    | r1_yellow_0(X0,X2)
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u57,axiom,
    ( r2_lattice3(X0,X2,sK1(X0,X1,X2))
    | k1_yellow_0(X0,X2) = X1
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u49,axiom,
    ( r2_lattice3(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u116,negated_conjecture,
    ( ~ r2_lattice3(sK0,X0,k3_yellow_0(sK0))
    | r1_yellow_0(sK0,X0)
    | ~ m1_subset_1(sK1(sK0,k3_yellow_0(sK0),X0),u1_struct_0(sK0)) )).

cnf(u132,negated_conjecture,
    ( ~ r2_lattice3(sK0,X0,k3_yellow_0(sK0))
    | k3_yellow_0(sK0) = k1_yellow_0(sK0,X0)
    | ~ m1_subset_1(sK1(sK0,k3_yellow_0(sK0),X0),u1_struct_0(sK0)) )).

cnf(u130,negated_conjecture,
    ( r1_yellow_0(sK0,k1_xboole_0) )).

cnf(u51,axiom,
    ( r1_yellow_0(X0,k1_xboole_0)
    | ~ l1_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u48,axiom,
    ( v2_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u47,axiom,
    ( v1_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u39,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u97,negated_conjecture,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u53,axiom,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ v5_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u78,negated_conjecture,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u112,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | k3_yellow_0(sK0) = X0 )).

cnf(u68,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u61,axiom,
    ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
    | r1_yellow_0(X0,X2)
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u58,axiom,
    ( ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
    | k1_yellow_0(X0,X2) = X1
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u59,axiom,
    ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | r1_yellow_0(X0,X2)
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u56,axiom,
    ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | k1_yellow_0(X0,X2) = X1
    | ~ r2_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u45,axiom,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u44,axiom,
    ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u64,axiom,
    ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X2)
    | r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u63,axiom,
    ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
    | ~ r2_lattice3(X0,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X0))
    | ~ r1_yellow_0(X0,X2)
    | r1_orders_2(X0,k1_yellow_0(X0,X2),X4)
    | ~ l1_orders_2(X0)
    | ~ v5_orders_2(X0) )).

cnf(u38,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u62,axiom,
    ( ~ v5_orders_2(X0)
    | ~ r1_orders_2(X0,X2,X1)
    | ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X1 = X2 )).

cnf(u43,axiom,
    ( l1_struct_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u40,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u46,axiom,
    ( ~ l1_orders_2(X0)
    | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) )).

cnf(u65,negated_conjecture,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) )).

cnf(u42,negated_conjecture,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (11023)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (11022)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (11020)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (11024)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (11032)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (11037)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (11032)Refutation not found, incomplete strategy% (11032)------------------------------
% 0.21/0.51  % (11032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11032)Memory used [KB]: 6140
% 0.21/0.51  % (11032)Time elapsed: 0.071 s
% 0.21/0.51  % (11032)------------------------------
% 0.21/0.51  % (11032)------------------------------
% 0.21/0.51  % (11030)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (11038)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (11030)Refutation not found, incomplete strategy% (11030)------------------------------
% 0.21/0.51  % (11030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11030)Memory used [KB]: 10618
% 0.21/0.51  % (11030)Time elapsed: 0.095 s
% 0.21/0.51  % (11030)------------------------------
% 0.21/0.51  % (11030)------------------------------
% 0.21/0.51  % (11039)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (11020)Refutation not found, incomplete strategy% (11020)------------------------------
% 0.21/0.51  % (11020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11020)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11020)Memory used [KB]: 10618
% 0.21/0.51  % (11020)Time elapsed: 0.103 s
% 0.21/0.51  % (11020)------------------------------
% 0.21/0.51  % (11020)------------------------------
% 0.21/0.51  % (11046)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (11041)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (11029)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (11031)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (11040)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (11041)# SZS output start Saturation.
% 0.21/0.52  cnf(u41,negated_conjecture,
% 0.21/0.52      v7_struct_0(sK0) | k3_yellow_0(sK0) = k4_yellow_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u50,axiom,
% 0.21/0.52      r1_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u52,axiom,
% 0.21/0.52      r2_yellow_0(X0,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u37,negated_conjecture,
% 0.21/0.52      ~v2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u60,axiom,
% 0.21/0.52      r2_lattice3(X0,X2,sK1(X0,X1,X2)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u57,axiom,
% 0.21/0.52      r2_lattice3(X0,X2,sK1(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u49,axiom,
% 0.21/0.52      r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u116,negated_conjecture,
% 0.21/0.52      ~r2_lattice3(sK0,X0,k3_yellow_0(sK0)) | r1_yellow_0(sK0,X0) | ~m1_subset_1(sK1(sK0,k3_yellow_0(sK0),X0),u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u132,negated_conjecture,
% 0.21/0.52      ~r2_lattice3(sK0,X0,k3_yellow_0(sK0)) | k3_yellow_0(sK0) = k1_yellow_0(sK0,X0) | ~m1_subset_1(sK1(sK0,k3_yellow_0(sK0),X0),u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u130,negated_conjecture,
% 0.21/0.52      r1_yellow_0(sK0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u51,axiom,
% 0.21/0.52      r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u47,axiom,
% 0.21/0.52      v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u39,negated_conjecture,
% 0.21/0.52      v3_yellow_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u97,negated_conjecture,
% 0.21/0.52      r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u53,axiom,
% 0.21/0.52      r1_orders_2(X0,X1,k4_yellow_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u78,negated_conjecture,
% 0.21/0.52      ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u112,negated_conjecture,
% 0.21/0.52      ~r1_orders_2(sK0,X0,k3_yellow_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_yellow_0(sK0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u68,negated_conjecture,
% 0.21/0.52      ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u61,axiom,
% 0.21/0.52      ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u58,axiom,
% 0.21/0.52      ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u59,axiom,
% 0.21/0.52      m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u56,axiom,
% 0.21/0.52      m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,axiom,
% 0.21/0.52      m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u44,axiom,
% 0.21/0.52      m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u64,axiom,
% 0.21/0.52      ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | r2_lattice3(X0,X2,k1_yellow_0(X0,X2)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u63,axiom,
% 0.21/0.52      ~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | r1_orders_2(X0,k1_yellow_0(X0,X2),X4) | ~l1_orders_2(X0) | ~v5_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u38,negated_conjecture,
% 0.21/0.52      v5_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u62,axiom,
% 0.21/0.52      ~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2).
% 0.21/0.52  
% 0.21/0.52  cnf(u43,axiom,
% 0.21/0.52      l1_struct_0(X0) | ~l1_orders_2(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u40,negated_conjecture,
% 0.21/0.52      l1_orders_2(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,axiom,
% 0.21/0.52      ~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u65,negated_conjecture,
% 0.21/0.52      k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u42,negated_conjecture,
% 0.21/0.52      k3_yellow_0(sK0) != k4_yellow_0(sK0) | ~v7_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  % (11041)# SZS output end Saturation.
% 0.21/0.52  % (11041)------------------------------
% 0.21/0.52  % (11041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11041)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (11041)Memory used [KB]: 6140
% 0.21/0.52  % (11041)Time elapsed: 0.108 s
% 0.21/0.52  % (11041)------------------------------
% 0.21/0.52  % (11041)------------------------------
% 0.21/0.52  % (11010)Success in time 0.163 s
%------------------------------------------------------------------------------
