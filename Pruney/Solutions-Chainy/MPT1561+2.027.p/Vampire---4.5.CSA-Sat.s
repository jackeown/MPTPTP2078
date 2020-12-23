%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:11 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u22,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u42,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u21,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u24,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

% (29235)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
cnf(u28,axiom,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1)
    | ~ l1_orders_2(X0)
    | ~ v3_orders_2(X0)
    | v2_struct_0(X0) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | v1_xboole_0(X0) )).

cnf(u23,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u27,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u29,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u32,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u20,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) )).

cnf(u38,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1))
    | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (29237)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (29239)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (29238)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (29239)Refutation not found, incomplete strategy% (29239)------------------------------
% 0.22/0.47  % (29239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29239)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (29239)Memory used [KB]: 6140
% 0.22/0.47  % (29239)Time elapsed: 0.062 s
% 0.22/0.47  % (29239)------------------------------
% 0.22/0.47  % (29239)------------------------------
% 0.22/0.47  % (29249)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (29245)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (29238)Refutation not found, incomplete strategy% (29238)------------------------------
% 0.22/0.47  % (29238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29238)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (29238)Memory used [KB]: 6140
% 0.22/0.47  % (29238)Time elapsed: 0.063 s
% 0.22/0.47  % (29238)------------------------------
% 0.22/0.47  % (29238)------------------------------
% 0.22/0.47  % (29237)Refutation not found, incomplete strategy% (29237)------------------------------
% 0.22/0.47  % (29237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (29237)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (29237)Memory used [KB]: 1535
% 0.22/0.47  % (29237)Time elapsed: 0.062 s
% 0.22/0.47  % (29237)------------------------------
% 0.22/0.47  % (29237)------------------------------
% 0.22/0.48  % (29241)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (29247)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (29246)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (29247)# SZS output start Saturation.
% 0.22/0.48  cnf(u22,negated_conjecture,
% 0.22/0.48      v5_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u42,negated_conjecture,
% 0.22/0.48      r1_orders_2(sK0,sK1,sK1)).
% 0.22/0.48  
% 0.22/0.48  cnf(u21,negated_conjecture,
% 0.22/0.48      v3_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u24,negated_conjecture,
% 0.22/0.48      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.22/0.48  
% 0.22/0.48  % (29235)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  cnf(u28,axiom,
% 0.22/0.48      ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u31,axiom,
% 0.22/0.48      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u23,negated_conjecture,
% 0.22/0.48      l1_orders_2(sK0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u27,axiom,
% 0.22/0.48      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u29,axiom,
% 0.22/0.48      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u32,negated_conjecture,
% 0.22/0.48      l1_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u20,negated_conjecture,
% 0.22/0.48      ~v2_struct_0(sK0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u36,negated_conjecture,
% 0.22/0.48      k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)).
% 0.22/0.48  
% 0.22/0.48  cnf(u38,negated_conjecture,
% 0.22/0.48      sK1 != k2_yellow_0(sK0,k2_tarski(sK1,sK1)) | sK1 != k1_yellow_0(sK0,k2_tarski(sK1,sK1))).
% 0.22/0.48  
% 0.22/0.48  % (29247)# SZS output end Saturation.
% 0.22/0.48  % (29247)------------------------------
% 0.22/0.48  % (29247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29247)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (29247)Memory used [KB]: 1663
% 0.22/0.48  % (29247)Time elapsed: 0.062 s
% 0.22/0.48  % (29247)------------------------------
% 0.22/0.48  % (29247)------------------------------
% 0.22/0.48  % (29236)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (29245)Refutation not found, incomplete strategy% (29245)------------------------------
% 0.22/0.48  % (29245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (29245)Memory used [KB]: 10618
% 0.22/0.48  % (29245)Time elapsed: 0.062 s
% 0.22/0.48  % (29245)------------------------------
% 0.22/0.48  % (29245)------------------------------
% 0.22/0.48  % (29233)Success in time 0.117 s
%------------------------------------------------------------------------------
