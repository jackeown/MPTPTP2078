%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:00 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   41 (  41 expanded)
%              Number of leaves         :   41 (  41 expanded)
%              Depth                    :    0
%              Number of atoms          :   93 (  93 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u87,negated_conjecture,
    ( r1_orders_2(sK0,sK4(u1_struct_0(sK0)),sK4(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k1_xboole_0 = u1_struct_0(sK0) )).

cnf(u85,negated_conjecture,
    ( r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u61,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK2)
    | v2_struct_0(sK0) )).

cnf(u20,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK1)
    | sK1 = k13_lattice3(sK0,sK1,sK2) )).

cnf(u63,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) )).

cnf(u21,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | sK1 != k13_lattice3(sK0,sK1,sK2) )).

cnf(u24,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u78,axiom,
    ( ~ v3_orders_2(X2)
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | r1_orders_2(X2,sK3(u1_struct_0(X2)),sK3(u1_struct_0(X2))) )).

cnf(u82,axiom,
    ( ~ v3_orders_2(X2)
    | k1_xboole_0 = u1_struct_0(X2)
    | ~ l1_orders_2(X2)
    | v2_struct_0(X2)
    | r1_orders_2(X2,sK4(u1_struct_0(X2)),sK4(u1_struct_0(X2))) )).

cnf(u25,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u26,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u39,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,axiom,
    ( ~ l1_struct_0(X0)
    | ~ v2_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) )).

cnf(u44,negated_conjecture,
    ( ~ v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u42,axiom,
    ( m1_subset_1(sK4(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u41,axiom,
    ( m1_subset_1(sK3(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | v2_struct_0(X0)
    | r1_orders_2(X0,X1,X1) )).

cnf(u35,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X1,X0)
    | r2_hidden(X1,X0)
    | v1_xboole_0(X0) )).

cnf(u48,negated_conjecture,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u47,negated_conjecture,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u33,axiom,
    ( r2_hidden(sK4(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u29,axiom,
    ( r2_hidden(sK3(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u30,axiom,
    ( ~ r2_hidden(X1,X0)
    | ~ v1_xboole_0(X0) )).

cnf(u38,axiom,
    ( ~ r2_hidden(X1,X0)
    | m1_subset_1(X1,X0) )).

cnf(u31,axiom,
    ( ~ r2_hidden(X2,X0)
    | k1_xboole_0 = X0
    | k4_tarski(X2,X3) != sK4(X0) )).

cnf(u32,axiom,
    ( ~ r2_hidden(X3,X0)
    | k1_xboole_0 = X0
    | k4_tarski(X2,X3) != sK4(X0) )).

cnf(u45,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK2) )).

cnf(u46,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1) )).

cnf(u34,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | m1_subset_1(X1,X0) )).

cnf(u43,axiom,
    ( ~ v1_xboole_0(X1)
    | k1_xboole_0 = X1 )).

cnf(u68,negated_conjecture,
    ( k4_tarski(X0,sK2) != sK4(u1_struct_0(sK0))
    | k1_xboole_0 = u1_struct_0(sK0) )).

cnf(u75,negated_conjecture,
    ( sK4(u1_struct_0(sK0)) != k4_tarski(sK1,X1)
    | k1_xboole_0 = u1_struct_0(sK0) )).

% (22813)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
cnf(u74,negated_conjecture,
    ( sK4(u1_struct_0(sK0)) != k4_tarski(X0,sK1)
    | k1_xboole_0 = u1_struct_0(sK0) )).

cnf(u69,negated_conjecture,
    ( sK4(u1_struct_0(sK0)) != k4_tarski(sK2,X1)
    | k1_xboole_0 = u1_struct_0(sK0) )).

cnf(u57,axiom,
    ( sK4(X0) != k4_tarski(X1,sK3(X0))
    | k1_xboole_0 = X0 )).

cnf(u56,axiom,
    ( sK4(X2) != k4_tarski(X3,sK4(X2))
    | k1_xboole_0 = X2 )).

cnf(u53,axiom,
    ( sK4(X0) != k4_tarski(sK3(X0),X1)
    | k1_xboole_0 = X0 )).

cnf(u52,axiom,
    ( sK4(X2) != k4_tarski(sK4(X2),X3)
    | k1_xboole_0 = X2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22811)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (22817)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (22811)Refutation not found, incomplete strategy% (22811)------------------------------
% 0.22/0.47  % (22811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22825)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (22819)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (22811)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22811)Memory used [KB]: 6268
% 0.22/0.48  % (22811)Time elapsed: 0.055 s
% 0.22/0.48  % (22811)------------------------------
% 0.22/0.48  % (22811)------------------------------
% 0.22/0.48  % (22825)Refutation not found, incomplete strategy% (22825)------------------------------
% 0.22/0.48  % (22825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22817)Refutation not found, incomplete strategy% (22817)------------------------------
% 0.22/0.48  % (22817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22825)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22825)Memory used [KB]: 10618
% 0.22/0.48  % (22825)Time elapsed: 0.060 s
% 0.22/0.48  % (22825)------------------------------
% 0.22/0.48  % (22825)------------------------------
% 0.22/0.48  % (22817)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22817)Memory used [KB]: 10618
% 0.22/0.48  % (22817)Time elapsed: 0.062 s
% 0.22/0.48  % (22817)------------------------------
% 0.22/0.48  % (22817)------------------------------
% 0.22/0.49  % (22818)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (22815)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (22814)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (22827)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (22826)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (22826)Refutation not found, incomplete strategy% (22826)------------------------------
% 0.22/0.50  % (22826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22826)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22826)Memory used [KB]: 6140
% 0.22/0.50  % (22826)Time elapsed: 0.052 s
% 0.22/0.50  % (22826)------------------------------
% 0.22/0.50  % (22826)------------------------------
% 0.22/0.50  % (22829)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (22816)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (22827)Refutation not found, incomplete strategy% (22827)------------------------------
% 0.22/0.50  % (22827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22827)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22827)Memory used [KB]: 10874
% 0.22/0.50  % (22827)Time elapsed: 0.058 s
% 0.22/0.50  % (22827)------------------------------
% 0.22/0.50  % (22827)------------------------------
% 0.22/0.51  % (22812)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (22814)Refutation not found, incomplete strategy% (22814)------------------------------
% 0.22/0.51  % (22814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22814)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22814)Memory used [KB]: 10618
% 0.22/0.51  % (22814)Time elapsed: 0.092 s
% 0.22/0.51  % (22814)------------------------------
% 0.22/0.51  % (22814)------------------------------
% 0.22/0.51  % (22812)Refutation not found, incomplete strategy% (22812)------------------------------
% 0.22/0.51  % (22812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22812)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22812)Memory used [KB]: 10618
% 0.22/0.51  % (22812)Time elapsed: 0.092 s
% 0.22/0.51  % (22812)------------------------------
% 0.22/0.51  % (22812)------------------------------
% 0.22/0.51  % (22821)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % (22828)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (22820)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (22821)Refutation not found, incomplete strategy% (22821)------------------------------
% 0.22/0.51  % (22821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22821)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22821)Memory used [KB]: 6140
% 0.22/0.51  % (22821)Time elapsed: 0.097 s
% 0.22/0.51  % (22821)------------------------------
% 0.22/0.51  % (22821)------------------------------
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (22828)# SZS output start Saturation.
% 0.22/0.51  cnf(u87,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK4(u1_struct_0(sK0)),sK4(u1_struct_0(sK0))) | v2_struct_0(sK0) | k1_xboole_0 = u1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u85,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK3(u1_struct_0(sK0)),sK3(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u61,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK2,sK2) | v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK2,sK1) | sK1 = k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u63,negated_conjecture,
% 0.22/0.51      r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,negated_conjecture,
% 0.22/0.51      ~r1_orders_2(sK0,sK2,sK1) | sK1 != k13_lattice3(sK0,sK1,sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,negated_conjecture,
% 0.22/0.51      v3_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u78,axiom,
% 0.22/0.51      ~v3_orders_2(X2) | v1_xboole_0(u1_struct_0(X2)) | ~l1_orders_2(X2) | v2_struct_0(X2) | r1_orders_2(X2,sK3(u1_struct_0(X2)),sK3(u1_struct_0(X2)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u82,axiom,
% 0.22/0.51      ~v3_orders_2(X2) | k1_xboole_0 = u1_struct_0(X2) | ~l1_orders_2(X2) | v2_struct_0(X2) | r1_orders_2(X2,sK4(u1_struct_0(X2)),sK4(u1_struct_0(X2)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,negated_conjecture,
% 0.22/0.51      l1_orders_2(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,axiom,
% 0.22/0.51      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u39,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u28,axiom,
% 0.22/0.51      ~l1_struct_0(X0) | ~v2_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u44,negated_conjecture,
% 0.22/0.51      ~v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u42,axiom,
% 0.22/0.51      m1_subset_1(sK4(X0),X0) | k1_xboole_0 = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u41,axiom,
% 0.22/0.51      m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK2,u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u27,axiom,
% 0.22/0.51      ~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,axiom,
% 0.22/0.51      ~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u37,axiom,
% 0.22/0.51      ~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u48,negated_conjecture,
% 0.22/0.51      r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u47,negated_conjecture,
% 0.22/0.51      r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,axiom,
% 0.22/0.51      r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,axiom,
% 0.22/0.51      r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u38,axiom,
% 0.22/0.51      ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u31,axiom,
% 0.22/0.51      ~r2_hidden(X2,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK4(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u32,axiom,
% 0.22/0.51      ~r2_hidden(X3,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK4(X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u45,negated_conjecture,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u46,negated_conjecture,
% 0.22/0.51      ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,axiom,
% 0.22/0.51      ~v1_xboole_0(X0) | ~v1_xboole_0(X1) | m1_subset_1(X1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u43,axiom,
% 0.22/0.51      ~v1_xboole_0(X1) | k1_xboole_0 = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u68,negated_conjecture,
% 0.22/0.51      k4_tarski(X0,sK2) != sK4(u1_struct_0(sK0)) | k1_xboole_0 = u1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u75,negated_conjecture,
% 0.22/0.51      sK4(u1_struct_0(sK0)) != k4_tarski(sK1,X1) | k1_xboole_0 = u1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  % (22813)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  cnf(u74,negated_conjecture,
% 0.22/0.51      sK4(u1_struct_0(sK0)) != k4_tarski(X0,sK1) | k1_xboole_0 = u1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u69,negated_conjecture,
% 0.22/0.51      sK4(u1_struct_0(sK0)) != k4_tarski(sK2,X1) | k1_xboole_0 = u1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u57,axiom,
% 0.22/0.51      sK4(X0) != k4_tarski(X1,sK3(X0)) | k1_xboole_0 = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u56,axiom,
% 0.22/0.51      sK4(X2) != k4_tarski(X3,sK4(X2)) | k1_xboole_0 = X2).
% 0.22/0.51  
% 0.22/0.51  cnf(u53,axiom,
% 0.22/0.51      sK4(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u52,axiom,
% 0.22/0.51      sK4(X2) != k4_tarski(sK4(X2),X3) | k1_xboole_0 = X2).
% 0.22/0.51  
% 0.22/0.51  % (22828)# SZS output end Saturation.
% 0.22/0.51  % (22828)------------------------------
% 0.22/0.51  % (22828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22828)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (22828)Memory used [KB]: 1663
% 0.22/0.51  % (22828)Time elapsed: 0.095 s
% 0.22/0.51  % (22828)------------------------------
% 0.22/0.51  % (22828)------------------------------
% 0.22/0.51  % (22820)Refutation not found, incomplete strategy% (22820)------------------------------
% 0.22/0.51  % (22820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22820)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22820)Memory used [KB]: 10618
% 0.22/0.51  % (22820)Time elapsed: 0.097 s
% 0.22/0.51  % (22820)------------------------------
% 0.22/0.51  % (22820)------------------------------
% 0.22/0.51  % (22810)Success in time 0.153 s
%------------------------------------------------------------------------------
