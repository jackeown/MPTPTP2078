%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,negated_conjecture,
    ( v5_orders_2(sK0) )).

cnf(u36,axiom,
    ( ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r1_orders_2(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,X1)
    | X1 = X2 )).

cnf(u55,negated_conjecture,
    ( r1_orders_2(sK0,sK1,sK1) )).

cnf(u62,negated_conjecture,
    ( ~ r1_orders_2(sK0,sK1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,sK1)
    | sK1 = X0 )).

cnf(u29,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u34,axiom,
    ( ~ v3_orders_2(X0)
    | v2_struct_0(X0)
    | ~ l1_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r1_orders_2(X0,X1,X1) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) )).

cnf(u54,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | r1_orders_2(sK0,X0,X0) )).

cnf(u61,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,X0,X1)
    | ~ r1_orders_2(sK0,X1,X0)
    | X0 = X1 )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u33,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u51,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u59,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

cnf(u26,negated_conjecture,
    ( sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.48  % (4092)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.48  % (4080)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (4083)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.48  % (4092)Refutation not found, incomplete strategy% (4092)------------------------------
% 0.20/0.48  % (4092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4092)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (4092)Memory used [KB]: 1663
% 0.20/0.48  % (4092)Time elapsed: 0.074 s
% 0.20/0.48  % (4092)------------------------------
% 0.20/0.48  % (4092)------------------------------
% 0.20/0.48  % (4098)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.49  % (4089)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.49  % (4083)Refutation not found, incomplete strategy% (4083)------------------------------
% 0.20/0.49  % (4083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4083)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4083)Memory used [KB]: 6268
% 0.20/0.49  % (4083)Time elapsed: 0.069 s
% 0.20/0.49  % (4083)------------------------------
% 0.20/0.49  % (4083)------------------------------
% 0.20/0.49  % (4077)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (4089)Refutation not found, incomplete strategy% (4089)------------------------------
% 0.20/0.49  % (4089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4089)Memory used [KB]: 10746
% 0.20/0.49  % (4089)Time elapsed: 0.094 s
% 0.20/0.49  % (4089)------------------------------
% 0.20/0.49  % (4089)------------------------------
% 0.20/0.49  % (4098)Refutation not found, incomplete strategy% (4098)------------------------------
% 0.20/0.49  % (4098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4098)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4098)Memory used [KB]: 1791
% 0.20/0.49  % (4098)Time elapsed: 0.093 s
% 0.20/0.49  % (4098)------------------------------
% 0.20/0.49  % (4098)------------------------------
% 0.20/0.49  % (4080)Refutation not found, incomplete strategy% (4080)------------------------------
% 0.20/0.49  % (4080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4080)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4080)Memory used [KB]: 6140
% 0.20/0.49  % (4080)Time elapsed: 0.104 s
% 0.20/0.49  % (4080)------------------------------
% 0.20/0.49  % (4080)------------------------------
% 0.20/0.49  % (4077)Refutation not found, incomplete strategy% (4077)------------------------------
% 0.20/0.49  % (4077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4075)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.49  % (4077)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4077)Memory used [KB]: 10746
% 0.20/0.49  % (4077)Time elapsed: 0.080 s
% 0.20/0.49  % (4077)------------------------------
% 0.20/0.49  % (4077)------------------------------
% 0.20/0.49  % (4097)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.49  % (4075)Refutation not found, incomplete strategy% (4075)------------------------------
% 0.20/0.49  % (4075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4075)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4075)Memory used [KB]: 6268
% 0.20/0.49  % (4075)Time elapsed: 0.079 s
% 0.20/0.49  % (4075)------------------------------
% 0.20/0.49  % (4075)------------------------------
% 0.20/0.50  % (4090)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (4081)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (4072)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (4090)Refutation not found, incomplete strategy% (4090)------------------------------
% 0.20/0.51  % (4090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4072)Refutation not found, incomplete strategy% (4072)------------------------------
% 0.20/0.51  % (4072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4072)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4072)Memory used [KB]: 6268
% 0.20/0.51  % (4072)Time elapsed: 0.107 s
% 0.20/0.51  % (4072)------------------------------
% 0.20/0.51  % (4072)------------------------------
% 0.20/0.51  % (4068)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (4090)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4090)Memory used [KB]: 1663
% 0.20/0.51  % (4090)Time elapsed: 0.110 s
% 0.20/0.51  % (4090)------------------------------
% 0.20/0.51  % (4090)------------------------------
% 0.20/0.51  % (4068)Refutation not found, incomplete strategy% (4068)------------------------------
% 0.20/0.51  % (4068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4068)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4068)Memory used [KB]: 1663
% 0.20/0.51  % (4068)Time elapsed: 0.117 s
% 0.20/0.51  % (4068)------------------------------
% 0.20/0.51  % (4068)------------------------------
% 0.20/0.51  % (4073)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (4070)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (4073)Refutation not found, incomplete strategy% (4073)------------------------------
% 0.20/0.51  % (4073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4073)Memory used [KB]: 6268
% 0.20/0.51  % (4073)Time elapsed: 0.116 s
% 0.20/0.51  % (4073)------------------------------
% 0.20/0.51  % (4073)------------------------------
% 0.20/0.52  % (4070)Refutation not found, incomplete strategy% (4070)------------------------------
% 0.20/0.52  % (4070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4070)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4070)Memory used [KB]: 10618
% 0.20/0.52  % (4070)Time elapsed: 0.118 s
% 0.20/0.52  % (4070)------------------------------
% 0.20/0.52  % (4070)------------------------------
% 0.20/0.52  % (4091)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (4069)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (4076)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (4093)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (4078)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (4076)Refutation not found, incomplete strategy% (4076)------------------------------
% 0.20/0.52  % (4076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4076)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4076)Memory used [KB]: 10618
% 0.20/0.52  % (4076)Time elapsed: 0.125 s
% 0.20/0.52  % (4076)------------------------------
% 0.20/0.52  % (4076)------------------------------
% 0.20/0.52  % (4079)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (4078)Refutation not found, incomplete strategy% (4078)------------------------------
% 0.20/0.52  % (4078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4078)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4078)Memory used [KB]: 10618
% 0.20/0.52  % (4078)Time elapsed: 0.126 s
% 0.20/0.52  % (4078)------------------------------
% 0.20/0.52  % (4078)------------------------------
% 0.20/0.52  % (4074)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (4084)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (4079)Refutation not found, incomplete strategy% (4079)------------------------------
% 0.20/0.52  % (4079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (4074)# SZS output start Saturation.
% 0.20/0.52  cnf(u30,negated_conjecture,
% 0.20/0.52      v5_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u36,axiom,
% 0.20/0.52      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 0.20/0.52  
% 0.20/0.52  cnf(u55,negated_conjecture,
% 0.20/0.52      r1_orders_2(sK0,sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u62,negated_conjecture,
% 0.20/0.52      ~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK1) | sK1 = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u29,negated_conjecture,
% 0.20/0.52      v3_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u34,axiom,
% 0.20/0.52      ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u27,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u50,axiom,
% 0.20/0.52      ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u54,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u61,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | X0 = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u31,negated_conjecture,
% 0.20/0.52      l1_orders_2(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u33,axiom,
% 0.20/0.52      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u35,axiom,
% 0.20/0.52      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u51,negated_conjecture,
% 0.20/0.52      l1_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u28,negated_conjecture,
% 0.20/0.52      ~v2_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.53  cnf(u59,negated_conjecture,
% 0.20/0.53      k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u26,negated_conjecture,
% 0.20/0.53      sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.20/0.53  
% 0.20/0.53  % (4074)# SZS output end Saturation.
% 0.20/0.53  % (4074)------------------------------
% 0.20/0.53  % (4074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4074)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (4074)Memory used [KB]: 6268
% 0.20/0.53  % (4074)Time elapsed: 0.128 s
% 0.20/0.53  % (4074)------------------------------
% 0.20/0.53  % (4074)------------------------------
% 0.20/0.53  % (4071)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (4093)Refutation not found, incomplete strategy% (4093)------------------------------
% 0.20/0.53  % (4093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4065)Success in time 0.173 s
%------------------------------------------------------------------------------
