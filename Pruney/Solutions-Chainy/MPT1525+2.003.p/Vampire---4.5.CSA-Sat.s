%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:54 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   54 (  54 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u21,axiom,
    ( r1_orders_2(X0,sK3(X0,X1),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_lattice3(X0,X1,X3)
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) )).

% (23593)Termination reason: Refutation not found, incomplete strategy

% (23593)Memory used [KB]: 10746
% (23593)Time elapsed: 0.127 s
% (23593)------------------------------
% (23593)------------------------------
% (23621)Refutation not found, incomplete strategy% (23621)------------------------------
% (23621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23621)Termination reason: Refutation not found, incomplete strategy

% (23621)Memory used [KB]: 1791
% (23621)Time elapsed: 0.133 s
% (23621)------------------------------
% (23621)------------------------------
% (23608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (23612)Termination reason: Refutation not found, incomplete strategy

% (23612)Memory used [KB]: 10746
% (23612)Time elapsed: 0.128 s
% (23612)------------------------------
% (23612)------------------------------
% (23609)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (23613)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (23614)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (23609)Refutation not found, incomplete strategy% (23609)------------------------------
% (23609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23598)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (23613)Refutation not found, incomplete strategy% (23613)------------------------------
% (23613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23613)Termination reason: Refutation not found, incomplete strategy

% (23613)Memory used [KB]: 1791
% (23613)Time elapsed: 0.141 s
% (23613)------------------------------
% (23613)------------------------------
% (23614)Refutation not found, incomplete strategy% (23614)------------------------------
% (23614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23614)Termination reason: Refutation not found, incomplete strategy

% (23614)Memory used [KB]: 10746
% (23614)Time elapsed: 0.141 s
% (23614)------------------------------
% (23614)------------------------------
% (23598)Refutation not found, incomplete strategy% (23598)------------------------------
% (23598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23598)Termination reason: Refutation not found, incomplete strategy

% (23598)Memory used [KB]: 10746
% (23598)Time elapsed: 0.140 s
% (23598)------------------------------
% (23598)------------------------------
% (23599)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
cnf(u20,axiom,
    ( ~ r1_orders_2(X0,X2,sK4(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_lattice3(X0,sK2(X0),X2)
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) )).

cnf(u19,axiom,
    ( r2_lattice3(X0,sK2(X0),sK4(X0,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_lattice3(X0,sK2(X0),X2)
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) )).

cnf(u23,axiom,
    ( r2_lattice3(X0,X1,sK3(X0,X1))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) )).

cnf(u14,negated_conjecture,
    ( v3_lattice3(sK0) )).

cnf(u15,negated_conjecture,
    ( ~ v3_lattice3(sK1) )).

cnf(u72,negated_conjecture,
    ( m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ r2_lattice3(sK1,sK2(sK1),X0) )).

cnf(u18,axiom,
    ( m1_subset_1(sK4(X0,X2),u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ r2_lattice3(X0,sK2(X0),X2)
    | ~ l1_orders_2(X0)
    | v3_lattice3(X0) )).

cnf(u56,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u17,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u22,axiom,
    ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ v3_lattice3(X0) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u16,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u12,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u26,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u47,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u53,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u34,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u28,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u54,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (23611)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (23590)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (23619)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (23619)Refutation not found, incomplete strategy% (23619)------------------------------
% 0.20/0.51  % (23619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23610)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.51  % (23602)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (23605)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (23615)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (23602)Refutation not found, incomplete strategy% (23602)------------------------------
% 0.20/0.52  % (23602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23619)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23619)Memory used [KB]: 6268
% 0.20/0.52  % (23619)Time elapsed: 0.107 s
% 0.20/0.52  % (23619)------------------------------
% 0.20/0.52  % (23619)------------------------------
% 0.20/0.52  % (23607)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (23590)Refutation not found, incomplete strategy% (23590)------------------------------
% 0.20/0.52  % (23590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23590)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23590)Memory used [KB]: 1663
% 0.20/0.52  % (23590)Time elapsed: 0.114 s
% 0.20/0.52  % (23590)------------------------------
% 0.20/0.52  % (23590)------------------------------
% 0.20/0.52  % (23602)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23602)Memory used [KB]: 10618
% 0.20/0.52  % (23602)Time elapsed: 0.117 s
% 0.20/0.52  % (23602)------------------------------
% 0.20/0.52  % (23602)------------------------------
% 0.20/0.52  % (23597)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (23618)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (23611)Refutation not found, incomplete strategy% (23611)------------------------------
% 0.20/0.52  % (23611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23611)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23611)Memory used [KB]: 10746
% 0.20/0.52  % (23611)Time elapsed: 0.114 s
% 0.20/0.52  % (23611)------------------------------
% 0.20/0.52  % (23611)------------------------------
% 0.20/0.52  % (23597)Refutation not found, incomplete strategy% (23597)------------------------------
% 0.20/0.52  % (23597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23597)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23597)Memory used [KB]: 6268
% 0.20/0.52  % (23597)Time elapsed: 0.090 s
% 0.20/0.52  % (23597)------------------------------
% 0.20/0.52  % (23597)------------------------------
% 0.20/0.52  % (23604)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (23595)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (23615)Refutation not found, incomplete strategy% (23615)------------------------------
% 0.20/0.52  % (23615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23615)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23615)Memory used [KB]: 1791
% 0.20/0.52  % (23591)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (23615)Time elapsed: 0.084 s
% 0.20/0.52  % (23615)------------------------------
% 0.20/0.52  % (23615)------------------------------
% 0.20/0.52  % (23592)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (23607)Refutation not found, incomplete strategy% (23607)------------------------------
% 0.20/0.52  % (23607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23607)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23607)Memory used [KB]: 6140
% 0.20/0.52  % (23607)Time elapsed: 0.095 s
% 0.20/0.52  % (23607)------------------------------
% 0.20/0.52  % (23607)------------------------------
% 0.20/0.52  % (23620)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (23595)Refutation not found, incomplete strategy% (23595)------------------------------
% 0.20/0.52  % (23595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (23595)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (23595)Memory used [KB]: 6268
% 0.20/0.52  % (23595)Time elapsed: 0.118 s
% 0.20/0.52  % (23595)------------------------------
% 0.20/0.52  % (23595)------------------------------
% 0.20/0.52  % (23621)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (23601)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (23603)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (23593)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (23594)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (23603)Refutation not found, incomplete strategy% (23603)------------------------------
% 0.20/0.53  % (23603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23603)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23603)Memory used [KB]: 6268
% 0.20/0.53  % (23603)Time elapsed: 0.129 s
% 0.20/0.53  % (23603)------------------------------
% 0.20/0.53  % (23603)------------------------------
% 0.20/0.53  % (23612)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (23592)Refutation not found, incomplete strategy% (23592)------------------------------
% 0.20/0.53  % (23592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23594)Refutation not found, incomplete strategy% (23594)------------------------------
% 0.20/0.53  % (23594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23594)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23594)Memory used [KB]: 6268
% 0.20/0.53  % (23594)Time elapsed: 0.128 s
% 0.20/0.53  % (23594)------------------------------
% 0.20/0.53  % (23594)------------------------------
% 0.20/0.53  % (23592)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23592)Memory used [KB]: 10746
% 0.20/0.53  % (23592)Time elapsed: 0.124 s
% 0.20/0.53  % (23592)------------------------------
% 0.20/0.53  % (23592)------------------------------
% 0.20/0.53  % (23593)Refutation not found, incomplete strategy% (23593)------------------------------
% 0.20/0.53  % (23593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23616)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (23596)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (23618)Refutation not found, incomplete strategy% (23618)------------------------------
% 0.20/0.53  % (23618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23618)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23618)Memory used [KB]: 10746
% 0.20/0.53  % (23618)Time elapsed: 0.129 s
% 0.20/0.53  % (23618)------------------------------
% 0.20/0.53  % (23618)------------------------------
% 0.20/0.53  % (23616)Refutation not found, incomplete strategy% (23616)------------------------------
% 0.20/0.53  % (23616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23616)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23616)Memory used [KB]: 6268
% 0.20/0.53  % (23616)Time elapsed: 0.127 s
% 0.20/0.53  % (23616)------------------------------
% 0.20/0.53  % (23616)------------------------------
% 0.20/0.53  % (23612)Refutation not found, incomplete strategy% (23612)------------------------------
% 0.20/0.53  % (23612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (23596)# SZS output start Saturation.
% 0.20/0.53  cnf(u21,axiom,
% 0.20/0.53      r1_orders_2(X0,sK3(X0,X1),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | ~l1_orders_2(X0) | ~v3_lattice3(X0)).
% 0.20/0.53  
% 0.20/0.53  % (23593)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23593)Memory used [KB]: 10746
% 0.20/0.53  % (23593)Time elapsed: 0.127 s
% 0.20/0.53  % (23593)------------------------------
% 0.20/0.53  % (23593)------------------------------
% 0.20/0.53  % (23621)Refutation not found, incomplete strategy% (23621)------------------------------
% 0.20/0.53  % (23621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (23621)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23621)Memory used [KB]: 1791
% 0.20/0.53  % (23621)Time elapsed: 0.133 s
% 0.20/0.53  % (23621)------------------------------
% 0.20/0.53  % (23621)------------------------------
% 0.20/0.53  % (23608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (23612)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (23612)Memory used [KB]: 10746
% 0.20/0.53  % (23612)Time elapsed: 0.128 s
% 0.20/0.53  % (23612)------------------------------
% 0.20/0.53  % (23612)------------------------------
% 0.20/0.54  % (23609)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (23613)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (23614)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (23609)Refutation not found, incomplete strategy% (23609)------------------------------
% 0.20/0.54  % (23609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23598)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (23613)Refutation not found, incomplete strategy% (23613)------------------------------
% 0.20/0.54  % (23613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23613)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23613)Memory used [KB]: 1791
% 0.20/0.54  % (23613)Time elapsed: 0.141 s
% 0.20/0.54  % (23613)------------------------------
% 0.20/0.54  % (23613)------------------------------
% 0.20/0.54  % (23614)Refutation not found, incomplete strategy% (23614)------------------------------
% 0.20/0.54  % (23614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23614)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23614)Memory used [KB]: 10746
% 0.20/0.54  % (23614)Time elapsed: 0.141 s
% 0.20/0.54  % (23614)------------------------------
% 0.20/0.54  % (23614)------------------------------
% 0.20/0.54  % (23598)Refutation not found, incomplete strategy% (23598)------------------------------
% 0.20/0.54  % (23598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23598)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (23598)Memory used [KB]: 10746
% 0.20/0.54  % (23598)Time elapsed: 0.140 s
% 0.20/0.54  % (23598)------------------------------
% 0.20/0.54  % (23598)------------------------------
% 0.20/0.54  % (23599)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  cnf(u20,axiom,
% 0.20/0.54      ~r1_orders_2(X0,X2,sK4(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | ~l1_orders_2(X0) | v3_lattice3(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u19,axiom,
% 0.20/0.54      r2_lattice3(X0,sK2(X0),sK4(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | ~l1_orders_2(X0) | v3_lattice3(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u23,axiom,
% 0.20/0.54      r2_lattice3(X0,X1,sK3(X0,X1)) | ~l1_orders_2(X0) | ~v3_lattice3(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u14,negated_conjecture,
% 0.20/0.54      v3_lattice3(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u15,negated_conjecture,
% 0.20/0.54      ~v3_lattice3(sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u72,negated_conjecture,
% 0.20/0.54      m1_subset_1(sK4(sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_lattice3(sK1,sK2(sK1),X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u18,axiom,
% 0.20/0.54      m1_subset_1(sK4(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_lattice3(X0,sK2(X0),X2) | ~l1_orders_2(X0) | v3_lattice3(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u56,negated_conjecture,
% 0.20/0.54      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.54  
% 0.20/0.54  cnf(u17,axiom,
% 0.20/0.54      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u22,axiom,
% 0.20/0.54      m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_lattice3(X0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u24,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.20/0.54  
% 0.20/0.54  cnf(u25,axiom,
% 0.20/0.54      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.20/0.54  
% 0.20/0.54  cnf(u16,negated_conjecture,
% 0.20/0.54      l1_orders_2(sK0)).
% 0.20/0.54  
% 0.20/0.54  cnf(u12,negated_conjecture,
% 0.20/0.54      l1_orders_2(sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u26,axiom,
% 0.20/0.54      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u47,axiom,
% 0.20/0.54      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.54  
% 0.20/0.54  cnf(u53,negated_conjecture,
% 0.20/0.54      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u34,negated_conjecture,
% 0.20/0.54      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.54  
% 0.20/0.54  cnf(u28,negated_conjecture,
% 0.20/0.54      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.20/0.54  
% 0.20/0.54  cnf(u54,negated_conjecture,
% 0.20/0.54      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.20/0.54  
% 0.20/0.54  % (23596)# SZS output end Saturation.
% 0.20/0.54  % (23596)------------------------------
% 0.20/0.54  % (23596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (23596)Termination reason: Satisfiable
% 0.20/0.54  
% 0.20/0.54  % (23596)Memory used [KB]: 6268
% 0.20/0.54  % (23596)Time elapsed: 0.139 s
% 0.20/0.54  % (23596)------------------------------
% 0.20/0.54  % (23596)------------------------------
% 0.20/0.54  % (23585)Success in time 0.181 s
%------------------------------------------------------------------------------
