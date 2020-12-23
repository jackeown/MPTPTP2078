%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:07 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1009)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
cnf(u31,negated_conjecture,
    ( ~ r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

cnf(u28,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u54,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u27,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u49,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | v1_xboole_0(X0) )).

cnf(u34,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u29,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u50,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u26,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u58,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (996)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.44  % (996)Refutation not found, incomplete strategy% (996)------------------------------
% 0.20/0.44  % (996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (996)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (996)Memory used [KB]: 1663
% 0.20/0.44  % (996)Time elapsed: 0.045 s
% 0.20/0.44  % (996)------------------------------
% 0.20/0.44  % (996)------------------------------
% 0.20/0.45  % (1006)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.45  % (1006)Refutation not found, incomplete strategy% (1006)------------------------------
% 0.20/0.45  % (1006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (1006)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (1006)Memory used [KB]: 10618
% 0.20/0.45  % (1006)Time elapsed: 0.053 s
% 0.20/0.45  % (1006)------------------------------
% 0.20/0.45  % (1006)------------------------------
% 0.20/0.46  % (1000)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (1000)Refutation not found, incomplete strategy% (1000)------------------------------
% 0.20/0.46  % (1000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (1000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (1000)Memory used [KB]: 6140
% 0.20/0.46  % (1000)Time elapsed: 0.042 s
% 0.20/0.46  % (1000)------------------------------
% 0.20/0.46  % (1000)------------------------------
% 0.20/0.46  % (1005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (1003)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (997)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (1008)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (1004)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (1008)# SZS output start Saturation.
% 0.20/0.47  % (1009)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  cnf(u31,negated_conjecture,
% 0.20/0.47      ~r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.20/0.47  
% 0.20/0.47  cnf(u28,negated_conjecture,
% 0.20/0.47      v5_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u54,negated_conjecture,
% 0.20/0.47      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.47  
% 0.20/0.47  cnf(u27,negated_conjecture,
% 0.20/0.47      v3_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u30,negated_conjecture,
% 0.20/0.47      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.47  
% 0.20/0.47  cnf(u49,axiom,
% 0.20/0.47      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) | v1_xboole_0(X0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u34,axiom,
% 0.20/0.47      ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u29,negated_conjecture,
% 0.20/0.47      l1_orders_2(sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u33,axiom,
% 0.20/0.47      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u35,axiom,
% 0.20/0.47      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u50,negated_conjecture,
% 0.20/0.47      l1_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u26,negated_conjecture,
% 0.20/0.47      ~v2_struct_0(sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u58,negated_conjecture,
% 0.20/0.47      k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)).
% 0.20/0.47  
% 0.20/0.47  % (1008)# SZS output end Saturation.
% 0.20/0.47  % (1008)------------------------------
% 0.20/0.47  % (1008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (1008)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (1008)Memory used [KB]: 1663
% 0.20/0.47  % (1008)Time elapsed: 0.061 s
% 0.20/0.47  % (1008)------------------------------
% 0.20/0.47  % (1008)------------------------------
% 0.20/0.47  % (994)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (989)Success in time 0.118 s
%------------------------------------------------------------------------------
