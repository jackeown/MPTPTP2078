%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:49 EST 2020

% Result     : CounterSatisfiable 1.62s
% Output     : Saturation 1.62s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   65 (  65 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( v7_struct_0(sK0)
    | k3_yellow_0(sK0) = k4_yellow_0(sK0) )).

cnf(u27,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u34,axiom,
    ( v2_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u50,negated_conjecture,
    ( ~ v2_yellow_0(sK0)
    | ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u33,axiom,
    ( v1_yellow_0(X0)
    | ~ v3_yellow_0(X0)
    | ~ l1_orders_2(X0) )).

cnf(u54,negated_conjecture,
    ( ~ v1_yellow_0(sK0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | k3_yellow_0(sK0) = X1
    | ~ r1_orders_2(sK0,X1,k3_yellow_0(sK0)) )).

cnf(u29,negated_conjecture,
    ( v3_yellow_0(sK0) )).

cnf(u36,axiom,
    ( r1_orders_2(X0,k3_yellow_0(X0),X1)
    | ~ v5_orders_2(X0)
    | ~ v1_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u35,axiom,
    ( r1_orders_2(X0,X1,k4_yellow_0(X0))
    | ~ v5_orders_2(X0)
    | ~ v2_yellow_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0) )).

cnf(u64,negated_conjecture,
    ( ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u57,negated_conjecture,
    ( ~ r1_orders_2(sK0,X0,k3_yellow_0(sK0))
    | k3_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u43,negated_conjecture,
    ( ~ r1_orders_2(sK0,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X0 = X1 )).

cnf(u41,negated_conjecture,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) )).

cnf(u38,axiom,
    ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u31,axiom,
    ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
    | ~ l1_orders_2(X0) )).

cnf(u60,negated_conjecture,
    ( ~ m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,k4_yellow_0(sK0),X0)
    | k4_yellow_0(sK0) = X0
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) )).

cnf(u28,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u37,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u30,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u32,axiom,
    ( ~ l1_orders_2(X0)
    | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) )).

cnf(u39,negated_conjecture,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) )).

cnf(u26,negated_conjecture,
    ( k3_yellow_0(sK0) != k4_yellow_0(sK0)
    | ~ v7_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:46:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (12540)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (12540)Refutation not found, incomplete strategy% (12540)------------------------------
% 0.21/0.52  % (12540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12540)Memory used [KB]: 6268
% 0.21/0.52  % (12540)Time elapsed: 0.111 s
% 0.21/0.52  % (12540)------------------------------
% 0.21/0.52  % (12540)------------------------------
% 0.21/0.53  % (12548)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (12557)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (12557)Refutation not found, incomplete strategy% (12557)------------------------------
% 0.21/0.54  % (12557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12557)Memory used [KB]: 10746
% 0.21/0.54  % (12557)Time elapsed: 0.120 s
% 0.21/0.54  % (12557)------------------------------
% 0.21/0.54  % (12557)------------------------------
% 0.21/0.56  % (12535)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (12561)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (12539)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (12539)Refutation not found, incomplete strategy% (12539)------------------------------
% 0.21/0.57  % (12539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (12539)Memory used [KB]: 6268
% 0.21/0.57  % (12539)Time elapsed: 0.146 s
% 0.21/0.57  % (12539)------------------------------
% 0.21/0.57  % (12539)------------------------------
% 0.21/0.57  % (12558)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.57  % (12538)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (12558)Refutation not found, incomplete strategy% (12558)------------------------------
% 0.21/0.57  % (12558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12558)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (12558)Memory used [KB]: 1791
% 0.21/0.57  % (12558)Time elapsed: 0.109 s
% 0.21/0.57  % (12558)------------------------------
% 0.21/0.57  % (12558)------------------------------
% 0.21/0.57  % (12553)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (12549)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (12550)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (12550)Refutation not found, incomplete strategy% (12550)------------------------------
% 0.21/0.58  % (12550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12550)Memory used [KB]: 6140
% 0.21/0.58  % (12550)Time elapsed: 0.001 s
% 0.21/0.58  % (12550)------------------------------
% 0.21/0.58  % (12550)------------------------------
% 0.21/0.58  % (12561)Refutation not found, incomplete strategy% (12561)------------------------------
% 0.21/0.58  % (12561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12545)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (12542)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.58  % (12552)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (12561)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12561)Memory used [KB]: 10746
% 0.21/0.58  % (12545)Refutation not found, incomplete strategy% (12545)------------------------------
% 0.21/0.58  % (12545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12561)Time elapsed: 0.153 s
% 0.21/0.58  % (12561)------------------------------
% 0.21/0.58  % (12561)------------------------------
% 0.21/0.58  % (12542)Refutation not found, incomplete strategy% (12542)------------------------------
% 0.21/0.58  % (12542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12542)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12542)Memory used [KB]: 6268
% 0.21/0.58  % (12542)Time elapsed: 0.130 s
% 0.21/0.58  % (12542)------------------------------
% 0.21/0.58  % (12542)------------------------------
% 0.21/0.58  % (12535)Refutation not found, incomplete strategy% (12535)------------------------------
% 0.21/0.58  % (12535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12535)Memory used [KB]: 1663
% 0.21/0.58  % (12535)Time elapsed: 0.124 s
% 0.21/0.58  % (12535)------------------------------
% 0.21/0.58  % (12535)------------------------------
% 0.21/0.58  % (12545)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12545)Memory used [KB]: 10618
% 0.21/0.58  % (12545)Time elapsed: 0.160 s
% 0.21/0.58  % (12545)------------------------------
% 0.21/0.58  % (12545)------------------------------
% 1.62/0.59  % (12560)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.62/0.59  % (12537)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.62/0.59  % (12537)Refutation not found, incomplete strategy% (12537)------------------------------
% 1.62/0.59  % (12537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (12537)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (12537)Memory used [KB]: 10746
% 1.62/0.59  % (12537)Time elapsed: 0.163 s
% 1.62/0.59  % (12537)------------------------------
% 1.62/0.59  % (12537)------------------------------
% 1.62/0.59  % (12544)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.62/0.59  % (12538)Refutation not found, incomplete strategy% (12538)------------------------------
% 1.62/0.59  % (12538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (12538)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (12538)Memory used [KB]: 10746
% 1.62/0.59  % (12538)Time elapsed: 0.156 s
% 1.62/0.59  % (12538)------------------------------
% 1.62/0.59  % (12538)------------------------------
% 1.62/0.60  % (12541)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.62/0.60  % (12544)Refutation not found, incomplete strategy% (12544)------------------------------
% 1.62/0.60  % (12544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (12544)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (12544)Memory used [KB]: 10746
% 1.62/0.60  % (12544)Time elapsed: 0.174 s
% 1.62/0.60  % (12544)------------------------------
% 1.62/0.60  % (12544)------------------------------
% 1.62/0.60  % (12554)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.62/0.60  % (12536)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.62/0.60  % (12563)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.62/0.60  % SZS status CounterSatisfiable for theBenchmark
% 1.62/0.60  % (12541)# SZS output start Saturation.
% 1.62/0.60  cnf(u25,negated_conjecture,
% 1.62/0.60      v7_struct_0(sK0) | k3_yellow_0(sK0) = k4_yellow_0(sK0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u27,negated_conjecture,
% 1.62/0.60      ~v2_struct_0(sK0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u34,axiom,
% 1.62/0.60      v2_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u50,negated_conjecture,
% 1.62/0.60      ~v2_yellow_0(sK0) | ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | ~m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.62/0.60  
% 1.62/0.60  cnf(u33,axiom,
% 1.62/0.60      v1_yellow_0(X0) | ~v3_yellow_0(X0) | ~l1_orders_2(X0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u54,negated_conjecture,
% 1.62/0.60      ~v1_yellow_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k3_yellow_0(sK0) = X1 | ~r1_orders_2(sK0,X1,k3_yellow_0(sK0))).
% 1.62/0.60  
% 1.62/0.60  cnf(u29,negated_conjecture,
% 1.62/0.60      v3_yellow_0(sK0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u36,axiom,
% 1.62/0.60      r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u35,axiom,
% 1.62/0.60      r1_orders_2(X0,X1,k4_yellow_0(X0)) | ~v5_orders_2(X0) | ~v2_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u64,negated_conjecture,
% 1.62/0.60      ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.62/0.60  
% 1.62/0.60  cnf(u57,negated_conjecture,
% 1.62/0.60      ~r1_orders_2(sK0,X0,k3_yellow_0(sK0)) | k3_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.62/0.60  
% 1.62/0.60  cnf(u43,negated_conjecture,
% 1.62/0.60      ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1).
% 1.62/0.60  
% 1.62/0.60  cnf(u41,negated_conjecture,
% 1.62/0.60      m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))).
% 1.62/0.60  
% 1.62/0.60  cnf(u38,axiom,
% 1.62/0.60      m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u31,axiom,
% 1.62/0.60      m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u60,negated_conjecture,
% 1.62/0.60      ~m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,k4_yellow_0(sK0),X0) | k4_yellow_0(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))).
% 1.62/0.60  
% 1.62/0.60  cnf(u28,negated_conjecture,
% 1.62/0.60      v5_orders_2(sK0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u37,axiom,
% 1.62/0.60      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 1.62/0.60  
% 1.62/0.60  cnf(u30,negated_conjecture,
% 1.62/0.60      l1_orders_2(sK0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u32,axiom,
% 1.62/0.60      ~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u39,negated_conjecture,
% 1.62/0.60      k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)).
% 1.62/0.60  
% 1.62/0.60  cnf(u26,negated_conjecture,
% 1.62/0.60      k3_yellow_0(sK0) != k4_yellow_0(sK0) | ~v7_struct_0(sK0)).
% 1.62/0.60  
% 1.62/0.60  % (12541)# SZS output end Saturation.
% 1.62/0.60  % (12541)------------------------------
% 1.62/0.60  % (12541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (12541)Termination reason: Satisfiable
% 1.62/0.60  
% 1.62/0.60  % (12541)Memory used [KB]: 6268
% 1.62/0.60  % (12541)Time elapsed: 0.174 s
% 1.62/0.60  % (12541)------------------------------
% 1.62/0.60  % (12541)------------------------------
% 1.62/0.60  % (12552)Refutation not found, incomplete strategy% (12552)------------------------------
% 1.62/0.60  % (12552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (12552)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (12552)Memory used [KB]: 10618
% 1.62/0.60  % (12552)Time elapsed: 0.175 s
% 1.62/0.60  % (12552)------------------------------
% 1.62/0.60  % (12552)------------------------------
% 1.62/0.60  % (12534)Success in time 0.231 s
%------------------------------------------------------------------------------
