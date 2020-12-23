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
% DateTime   : Thu Dec  3 13:16:02 EST 2020

% Result     : CounterSatisfiable 1.65s
% Output     : Saturation 1.65s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u61,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK1,X0,X1) )).

cnf(u17,axiom,
    ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X2) )).

cnf(u18,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) )).

cnf(u50,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u16,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u15,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u12,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u21,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u41,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u47,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u29,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u23,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u48,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

cnf(u14,negated_conjecture,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (19496)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.49  % (19482)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (19482)Refutation not found, incomplete strategy% (19482)------------------------------
% 0.21/0.50  % (19482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19482)Memory used [KB]: 6268
% 0.21/0.50  % (19482)Time elapsed: 0.077 s
% 0.21/0.50  % (19482)------------------------------
% 0.21/0.50  % (19482)------------------------------
% 0.21/0.50  % (19496)Refutation not found, incomplete strategy% (19496)------------------------------
% 0.21/0.50  % (19496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19496)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19496)Memory used [KB]: 10746
% 0.21/0.50  % (19496)Time elapsed: 0.092 s
% 0.21/0.50  % (19496)------------------------------
% 0.21/0.50  % (19496)------------------------------
% 0.21/0.53  % (19478)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (19501)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (19489)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (19476)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (19475)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (19493)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (19479)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (19475)Refutation not found, incomplete strategy% (19475)------------------------------
% 0.21/0.55  % (19475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19475)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19475)Memory used [KB]: 1663
% 0.21/0.55  % (19475)Time elapsed: 0.133 s
% 0.21/0.55  % (19475)------------------------------
% 0.21/0.55  % (19475)------------------------------
% 0.21/0.55  % (19493)Refutation not found, incomplete strategy% (19493)------------------------------
% 0.21/0.55  % (19493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19493)Memory used [KB]: 10618
% 0.21/0.55  % (19493)Time elapsed: 0.153 s
% 0.21/0.55  % (19493)------------------------------
% 0.21/0.55  % (19493)------------------------------
% 0.21/0.55  % (19479)Refutation not found, incomplete strategy% (19479)------------------------------
% 0.21/0.55  % (19479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19479)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19479)Memory used [KB]: 6140
% 0.21/0.55  % (19479)Time elapsed: 0.150 s
% 0.21/0.55  % (19479)------------------------------
% 0.21/0.55  % (19479)------------------------------
% 0.21/0.55  % (19477)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (19506)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (19487)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (19487)Refutation not found, incomplete strategy% (19487)------------------------------
% 0.21/0.55  % (19487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19487)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19487)Memory used [KB]: 10618
% 0.21/0.55  % (19487)Time elapsed: 0.153 s
% 0.21/0.55  % (19487)------------------------------
% 0.21/0.55  % (19487)------------------------------
% 0.21/0.55  % (19506)Refutation not found, incomplete strategy% (19506)------------------------------
% 0.21/0.55  % (19506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (19506)Memory used [KB]: 1791
% 0.21/0.55  % (19506)Time elapsed: 0.128 s
% 0.21/0.55  % (19506)------------------------------
% 0.21/0.55  % (19506)------------------------------
% 0.21/0.55  % (19494)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (19477)Refutation not found, incomplete strategy% (19477)------------------------------
% 0.21/0.56  % (19477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19478)Refutation not found, incomplete strategy% (19478)------------------------------
% 0.21/0.56  % (19478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19478)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19478)Memory used [KB]: 10746
% 0.21/0.56  % (19478)Time elapsed: 0.160 s
% 0.21/0.56  % (19478)------------------------------
% 0.21/0.56  % (19478)------------------------------
% 0.21/0.56  % (19504)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (19477)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19477)Memory used [KB]: 10746
% 0.21/0.56  % (19477)Time elapsed: 0.130 s
% 0.21/0.56  % (19477)------------------------------
% 0.21/0.56  % (19477)------------------------------
% 0.21/0.56  % (19490)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (19502)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (19480)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (19498)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (19498)Refutation not found, incomplete strategy% (19498)------------------------------
% 0.21/0.56  % (19498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19498)Memory used [KB]: 10746
% 0.21/0.56  % (19498)Time elapsed: 0.157 s
% 0.21/0.56  % (19498)------------------------------
% 0.21/0.56  % (19498)------------------------------
% 0.21/0.56  % (19501)Refutation not found, incomplete strategy% (19501)------------------------------
% 0.21/0.56  % (19501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (19501)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (19501)Memory used [KB]: 6268
% 0.21/0.56  % (19501)Time elapsed: 0.161 s
% 0.21/0.56  % (19501)------------------------------
% 0.21/0.56  % (19501)------------------------------
% 0.21/0.56  % (19481)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (19491)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (19488)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (19503)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (19491)Refutation not found, incomplete strategy% (19491)------------------------------
% 0.21/0.57  % (19491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (19491)Memory used [KB]: 6140
% 0.21/0.57  % (19491)Time elapsed: 0.146 s
% 0.21/0.57  % (19491)------------------------------
% 0.21/0.57  % (19491)------------------------------
% 0.21/0.57  % (19500)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (19492)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (19488)Refutation not found, incomplete strategy% (19488)------------------------------
% 0.21/0.57  % (19488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19488)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (19488)Memory used [KB]: 6268
% 0.21/0.57  % (19488)Time elapsed: 0.174 s
% 0.21/0.57  % (19488)------------------------------
% 0.21/0.57  % (19488)------------------------------
% 0.21/0.57  % (19503)Refutation not found, incomplete strategy% (19503)------------------------------
% 0.21/0.57  % (19503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (19503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (19503)Memory used [KB]: 6268
% 0.21/0.57  % (19503)Time elapsed: 0.168 s
% 0.21/0.57  % (19503)------------------------------
% 0.21/0.57  % (19503)------------------------------
% 0.21/0.57  % (19485)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (19500)Refutation not found, incomplete strategy% (19500)------------------------------
% 0.21/0.57  % (19500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.57  % (19500)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.57  
% 1.65/0.57  % (19500)Memory used [KB]: 6268
% 1.65/0.57  % (19500)Time elapsed: 0.145 s
% 1.65/0.57  % (19500)------------------------------
% 1.65/0.57  % (19500)------------------------------
% 1.65/0.58  % (19485)Refutation not found, incomplete strategy% (19485)------------------------------
% 1.65/0.58  % (19485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (19485)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (19485)Memory used [KB]: 10746
% 1.65/0.58  % (19485)Time elapsed: 0.141 s
% 1.65/0.58  % (19485)------------------------------
% 1.65/0.58  % (19485)------------------------------
% 1.65/0.58  % (19483)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.58  % (19495)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.65/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.65/0.58  % (19481)# SZS output start Saturation.
% 1.65/0.58  cnf(u61,negated_conjecture,
% 1.65/0.58      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 1.65/0.58  
% 1.65/0.58  cnf(u17,axiom,
% 1.65/0.58      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 1.65/0.58  
% 1.65/0.58  cnf(u18,axiom,
% 1.65/0.58      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 1.65/0.58  
% 1.65/0.58  cnf(u50,negated_conjecture,
% 1.65/0.58      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.65/0.58  
% 1.65/0.58  cnf(u16,axiom,
% 1.65/0.58      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 1.65/0.58  
% 1.65/0.58  cnf(u19,axiom,
% 1.65/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 1.65/0.58  
% 1.65/0.58  cnf(u20,axiom,
% 1.65/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 1.65/0.58  
% 1.65/0.58  cnf(u15,negated_conjecture,
% 1.65/0.58      l1_orders_2(sK0)).
% 1.65/0.58  
% 1.65/0.58  cnf(u12,negated_conjecture,
% 1.65/0.58      l1_orders_2(sK1)).
% 1.65/0.58  
% 1.65/0.58  cnf(u21,axiom,
% 1.65/0.58      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.65/0.58  
% 1.65/0.58  cnf(u41,axiom,
% 1.65/0.58      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.65/0.58  
% 1.65/0.58  cnf(u47,negated_conjecture,
% 1.65/0.58      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 1.65/0.58  
% 1.65/0.58  cnf(u29,negated_conjecture,
% 1.65/0.58      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 1.65/0.58  
% 1.65/0.58  cnf(u23,negated_conjecture,
% 1.65/0.58      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 1.65/0.58  
% 1.65/0.58  cnf(u48,negated_conjecture,
% 1.65/0.58      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 1.65/0.58  
% 1.65/0.58  cnf(u14,negated_conjecture,
% 1.65/0.58      k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)).
% 1.65/0.58  
% 1.65/0.58  % (19481)# SZS output end Saturation.
% 1.65/0.58  % (19481)------------------------------
% 1.65/0.58  % (19481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (19481)Termination reason: Satisfiable
% 1.65/0.58  
% 1.65/0.58  % (19481)Memory used [KB]: 6268
% 1.65/0.58  % (19481)Time elapsed: 0.165 s
% 1.65/0.58  % (19481)------------------------------
% 1.65/0.58  % (19481)------------------------------
% 1.65/0.58  % (19474)Success in time 0.211 s
%------------------------------------------------------------------------------
