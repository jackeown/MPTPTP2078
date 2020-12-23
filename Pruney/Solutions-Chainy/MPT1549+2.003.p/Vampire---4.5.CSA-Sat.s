%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 1.87s
% Output     : Saturation 1.87s
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
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:42:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (5299)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (5311)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (5299)Refutation not found, incomplete strategy% (5299)------------------------------
% 0.21/0.55  % (5299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (5303)Refutation not found, incomplete strategy% (5303)------------------------------
% 0.21/0.56  % (5303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5303)Memory used [KB]: 6140
% 0.21/0.56  % (5303)Time elapsed: 0.075 s
% 0.21/0.56  % (5303)------------------------------
% 0.21/0.56  % (5303)------------------------------
% 0.21/0.56  % (5299)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5299)Memory used [KB]: 10618
% 0.21/0.56  % (5299)Time elapsed: 0.123 s
% 0.21/0.56  % (5299)------------------------------
% 0.21/0.56  % (5299)------------------------------
% 0.21/0.56  % (5311)Refutation not found, incomplete strategy% (5311)------------------------------
% 0.21/0.56  % (5311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5311)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5311)Memory used [KB]: 1663
% 0.21/0.56  % (5311)Time elapsed: 0.077 s
% 0.21/0.56  % (5311)------------------------------
% 0.21/0.56  % (5311)------------------------------
% 0.21/0.56  % (5288)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (5291)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (5295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (5291)Refutation not found, incomplete strategy% (5291)------------------------------
% 0.21/0.56  % (5291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5291)Memory used [KB]: 10746
% 0.21/0.56  % (5291)Time elapsed: 0.133 s
% 0.21/0.56  % (5291)------------------------------
% 0.21/0.56  % (5291)------------------------------
% 0.21/0.56  % (5295)Refutation not found, incomplete strategy% (5295)------------------------------
% 0.21/0.56  % (5295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5295)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5295)Memory used [KB]: 6268
% 0.21/0.56  % (5295)Time elapsed: 0.084 s
% 0.21/0.56  % (5295)------------------------------
% 0.21/0.56  % (5295)------------------------------
% 0.21/0.56  % (5308)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (5306)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (5316)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (5290)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (5290)Refutation not found, incomplete strategy% (5290)------------------------------
% 0.21/0.57  % (5290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (5290)Memory used [KB]: 10746
% 0.21/0.57  % (5290)Time elapsed: 0.141 s
% 0.21/0.57  % (5290)------------------------------
% 0.21/0.57  % (5290)------------------------------
% 0.21/0.57  % (5301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (5300)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (5300)Refutation not found, incomplete strategy% (5300)------------------------------
% 0.21/0.58  % (5300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (5300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (5300)Memory used [KB]: 6268
% 0.21/0.58  % (5300)Time elapsed: 0.153 s
% 0.21/0.58  % (5288)Refutation not found, incomplete strategy% (5288)------------------------------
% 0.21/0.58  % (5288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (5288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (5288)Memory used [KB]: 1663
% 0.21/0.58  % (5288)Time elapsed: 0.129 s
% 0.21/0.58  % (5288)------------------------------
% 0.21/0.58  % (5288)------------------------------
% 0.21/0.58  % (5293)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.62/0.59  % (5293)Refutation not found, incomplete strategy% (5293)------------------------------
% 1.62/0.59  % (5293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (5293)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (5293)Memory used [KB]: 6268
% 1.62/0.59  % (5293)Time elapsed: 0.151 s
% 1.62/0.59  % (5293)------------------------------
% 1.62/0.59  % (5293)------------------------------
% 1.62/0.59  % (5308)Refutation not found, incomplete strategy% (5308)------------------------------
% 1.62/0.59  % (5308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (5308)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.59  
% 1.62/0.59  % (5308)Memory used [KB]: 10746
% 1.62/0.59  % (5308)Time elapsed: 0.157 s
% 1.62/0.59  % (5308)------------------------------
% 1.62/0.59  % (5308)------------------------------
% 1.62/0.59  % (5298)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.62/0.60  % (5310)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.62/0.60  % (5317)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.60  % (5289)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.62/0.60  % (5292)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.62/0.60  % (5300)------------------------------
% 1.62/0.60  % (5300)------------------------------
% 1.62/0.60  % (5292)Refutation not found, incomplete strategy% (5292)------------------------------
% 1.62/0.60  % (5292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (5292)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (5309)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.62/0.60  % (5292)Memory used [KB]: 6140
% 1.62/0.60  % (5292)Time elapsed: 0.172 s
% 1.62/0.60  % (5292)------------------------------
% 1.62/0.60  % (5292)------------------------------
% 1.87/0.60  % (5309)Refutation not found, incomplete strategy% (5309)------------------------------
% 1.87/0.60  % (5309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (5309)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.60  
% 1.87/0.60  % (5309)Memory used [KB]: 1663
% 1.87/0.60  % (5309)Time elapsed: 0.175 s
% 1.87/0.60  % (5309)------------------------------
% 1.87/0.60  % (5309)------------------------------
% 1.87/0.60  % (5297)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.87/0.61  % (5302)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.87/0.61  % (5304)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.87/0.61  % (5297)Refutation not found, incomplete strategy% (5297)------------------------------
% 1.87/0.61  % (5297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (5297)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (5297)Memory used [KB]: 10618
% 1.87/0.61  % (5297)Time elapsed: 0.176 s
% 1.87/0.61  % (5297)------------------------------
% 1.87/0.61  % (5297)------------------------------
% 1.87/0.61  % (5294)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.87/0.61  % (5307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.87/0.61  % (5305)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.87/0.61  % (5315)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.87/0.61  % (5298)Refutation not found, incomplete strategy% (5298)------------------------------
% 1.87/0.61  % (5298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (5298)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (5298)Memory used [KB]: 10746
% 1.87/0.61  % (5298)Time elapsed: 0.164 s
% 1.87/0.61  % (5298)------------------------------
% 1.87/0.61  % (5298)------------------------------
% 1.87/0.61  % SZS status CounterSatisfiable for theBenchmark
% 1.87/0.61  % (5294)# SZS output start Saturation.
% 1.87/0.61  cnf(u61,negated_conjecture,
% 1.87/0.61      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 1.87/0.61  
% 1.87/0.61  cnf(u17,axiom,
% 1.87/0.61      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 1.87/0.61  
% 1.87/0.61  cnf(u18,axiom,
% 1.87/0.61      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 1.87/0.61  
% 1.87/0.61  cnf(u50,negated_conjecture,
% 1.87/0.61      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.87/0.61  
% 1.87/0.61  cnf(u16,axiom,
% 1.87/0.61      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 1.87/0.61  
% 1.87/0.62  cnf(u19,axiom,
% 1.87/0.62      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 1.87/0.62  
% 1.87/0.62  cnf(u20,axiom,
% 1.87/0.62      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 1.87/0.62  
% 1.87/0.62  cnf(u15,negated_conjecture,
% 1.87/0.62      l1_orders_2(sK0)).
% 1.87/0.62  
% 1.87/0.62  cnf(u12,negated_conjecture,
% 1.87/0.62      l1_orders_2(sK1)).
% 1.87/0.62  
% 1.87/0.62  cnf(u21,axiom,
% 1.87/0.62      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.87/0.62  
% 1.87/0.62  cnf(u41,axiom,
% 1.87/0.62      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.87/0.62  
% 1.87/0.62  cnf(u47,negated_conjecture,
% 1.87/0.62      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 1.87/0.62  
% 1.87/0.62  cnf(u29,negated_conjecture,
% 1.87/0.62      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 1.87/0.62  
% 1.87/0.62  cnf(u23,negated_conjecture,
% 1.87/0.62      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 1.87/0.62  
% 1.87/0.62  cnf(u48,negated_conjecture,
% 1.87/0.62      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 1.87/0.62  
% 1.87/0.62  cnf(u14,negated_conjecture,
% 1.87/0.62      k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)).
% 1.87/0.62  
% 1.87/0.62  % (5294)# SZS output end Saturation.
% 1.87/0.62  % (5294)------------------------------
% 1.87/0.62  % (5294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (5294)Termination reason: Satisfiable
% 1.87/0.62  
% 1.87/0.62  % (5294)Memory used [KB]: 6268
% 1.87/0.62  % (5294)Time elapsed: 0.184 s
% 1.87/0.62  % (5294)------------------------------
% 1.87/0.62  % (5294)------------------------------
% 1.87/0.62  % (5307)Refutation not found, incomplete strategy% (5307)------------------------------
% 1.87/0.62  % (5307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (5314)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.87/0.62  % (5296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.87/0.62  % (5287)Success in time 0.245 s
%------------------------------------------------------------------------------
