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
% DateTime   : Thu Dec  3 13:16:12 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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

% (21006)Refutation not found, incomplete strategy% (21006)------------------------------
% (21006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (21026)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (21018)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (21018)Refutation not found, incomplete strategy% (21018)------------------------------
% 0.21/0.52  % (21018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21018)Memory used [KB]: 1663
% 0.21/0.52  % (21018)Time elapsed: 0.111 s
% 0.21/0.52  % (21018)------------------------------
% 0.21/0.52  % (21018)------------------------------
% 0.21/0.52  % (21007)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (21002)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (21015)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (21009)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (20997)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (21009)Refutation not found, incomplete strategy% (21009)------------------------------
% 0.21/0.52  % (21009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21009)Memory used [KB]: 6140
% 0.21/0.52  % (21009)Time elapsed: 0.121 s
% 0.21/0.52  % (21009)------------------------------
% 0.21/0.52  % (21009)------------------------------
% 0.21/0.53  % (21019)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (21020)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (21026)Refutation not found, incomplete strategy% (21026)------------------------------
% 0.21/0.53  % (21026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21011)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (21002)Refutation not found, incomplete strategy% (21002)------------------------------
% 0.21/0.53  % (21002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21002)Memory used [KB]: 6268
% 0.21/0.53  % (21002)Time elapsed: 0.116 s
% 0.21/0.53  % (21002)------------------------------
% 0.21/0.53  % (21002)------------------------------
% 0.21/0.53  % (21000)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (21000)Refutation not found, incomplete strategy% (21000)------------------------------
% 0.21/0.53  % (21000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21026)Memory used [KB]: 1791
% 0.21/0.53  % (21026)Time elapsed: 0.123 s
% 0.21/0.53  % (21026)------------------------------
% 0.21/0.53  % (21026)------------------------------
% 0.21/0.53  % (21010)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (21019)Refutation not found, incomplete strategy% (21019)------------------------------
% 0.21/0.53  % (21019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20999)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21012)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (21013)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (20999)Refutation not found, incomplete strategy% (20999)------------------------------
% 0.21/0.53  % (20999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20999)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20999)Memory used [KB]: 10618
% 0.21/0.53  % (20999)Time elapsed: 0.124 s
% 0.21/0.53  % (20999)------------------------------
% 0.21/0.53  % (20999)------------------------------
% 0.21/0.53  % (21001)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21012)Refutation not found, incomplete strategy% (21012)------------------------------
% 0.21/0.53  % (21012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21012)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21012)Memory used [KB]: 6268
% 0.21/0.53  % (21012)Time elapsed: 0.129 s
% 0.21/0.53  % (21012)------------------------------
% 0.21/0.53  % (21012)------------------------------
% 0.21/0.53  % (21007)Refutation not found, incomplete strategy% (21007)------------------------------
% 0.21/0.53  % (21007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20998)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21001)Refutation not found, incomplete strategy% (21001)------------------------------
% 0.21/0.53  % (21001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21001)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21001)Memory used [KB]: 6268
% 0.21/0.53  % (21001)Time elapsed: 0.124 s
% 0.21/0.53  % (21001)------------------------------
% 0.21/0.53  % (21001)------------------------------
% 0.21/0.53  % (21007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21007)Memory used [KB]: 10618
% 0.21/0.53  % (21007)Time elapsed: 0.131 s
% 0.21/0.54  % (21007)------------------------------
% 0.21/0.54  % (21007)------------------------------
% 0.21/0.54  % (21025)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (21019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21019)Memory used [KB]: 10618
% 0.21/0.54  % (21019)Time elapsed: 0.131 s
% 0.21/0.54  % (21019)------------------------------
% 0.21/0.54  % (21019)------------------------------
% 0.21/0.54  % (21021)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21021)Refutation not found, incomplete strategy% (21021)------------------------------
% 0.21/0.54  % (21021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21021)Memory used [KB]: 6268
% 0.21/0.54  % (21021)Time elapsed: 0.128 s
% 0.21/0.54  % (21021)------------------------------
% 0.21/0.54  % (21021)------------------------------
% 0.21/0.54  % (20997)Refutation not found, incomplete strategy% (20997)------------------------------
% 0.21/0.54  % (20997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20997)Memory used [KB]: 1663
% 0.21/0.54  % (20997)Time elapsed: 0.093 s
% 0.21/0.54  % (20997)------------------------------
% 0.21/0.54  % (20997)------------------------------
% 0.21/0.54  % (21004)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (21000)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21000)Memory used [KB]: 10618
% 0.21/0.54  % (21000)Time elapsed: 0.117 s
% 0.21/0.54  % (21000)------------------------------
% 0.21/0.54  % (21000)------------------------------
% 0.21/0.54  % (21004)Refutation not found, incomplete strategy% (21004)------------------------------
% 0.21/0.54  % (21004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21016)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (21006)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (21003)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (21003)# SZS output start Saturation.
% 0.21/0.54  cnf(u30,negated_conjecture,
% 0.21/0.54      v5_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  % (21006)Refutation not found, incomplete strategy% (21006)------------------------------
% 0.21/0.54  % (21006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  cnf(u36,axiom,
% 0.21/0.54      ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X2,X1) | X1 = X2).
% 0.21/0.54  
% 0.21/0.54  cnf(u55,negated_conjecture,
% 0.21/0.54      r1_orders_2(sK0,sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u62,negated_conjecture,
% 0.21/0.54      ~r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK1) | sK1 = X0).
% 0.21/0.54  
% 0.21/0.54  cnf(u29,negated_conjecture,
% 0.21/0.54      v3_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u34,axiom,
% 0.21/0.54      ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u27,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.54  
% 0.21/0.54  cnf(u50,axiom,
% 0.21/0.54      ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u54,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u61,negated_conjecture,
% 0.21/0.54      ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | X0 = X1).
% 0.21/0.54  
% 0.21/0.54  cnf(u31,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u33,axiom,
% 0.21/0.54      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u35,axiom,
% 0.21/0.54      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u51,negated_conjecture,
% 0.21/0.54      l1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u28,negated_conjecture,
% 0.21/0.54      ~v2_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u59,negated_conjecture,
% 0.21/0.54      k6_domain_1(u1_struct_0(sK0),sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u26,negated_conjecture,
% 0.21/0.54      sK1 != k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | sK1 != k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))).
% 0.21/0.54  
% 0.21/0.54  % (21003)# SZS output end Saturation.
% 0.21/0.54  % (21003)------------------------------
% 0.21/0.54  % (21003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21003)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (21003)Memory used [KB]: 6268
% 0.21/0.54  % (21003)Time elapsed: 0.104 s
% 0.21/0.54  % (21003)------------------------------
% 0.21/0.54  % (21003)------------------------------
% 0.21/0.54  % (20994)Success in time 0.177 s
%------------------------------------------------------------------------------
