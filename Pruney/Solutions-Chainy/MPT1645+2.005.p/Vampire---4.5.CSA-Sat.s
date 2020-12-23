%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:05 EST 2020

% Result     : CounterSatisfiable 1.56s
% Output     : Saturation 1.56s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u13,negated_conjecture,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) )).

cnf(u30,negated_conjecture,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK2,sK1) )).

cnf(u27,negated_conjecture,
    ( ~ v13_waybel_0(sK2,sK1)
    | v12_waybel_0(sK2,sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v13_waybel_0(sK2,sK1)
    | ~ v12_waybel_0(sK2,sK1) )).

cnf(u78,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | r1_orders_2(sK1,X0,X1) )).

cnf(u22,axiom,
    ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | r1_orders_2(X0,X1,X2) )).

cnf(u23,axiom,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) )).

cnf(u61,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u21,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u20,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u18,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u31,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u49,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u58,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u39,negated_conjecture,
    ( u1_struct_0(sK1) = u1_struct_0(sK0) )).

cnf(u16,negated_conjecture,
    ( sK2 = sK3 )).

cnf(u33,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u59,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (22636)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (22636)Refutation not found, incomplete strategy% (22636)------------------------------
% 0.22/0.51  % (22636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22656)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (22647)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (22636)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22636)Memory used [KB]: 1791
% 0.22/0.51  % (22636)Time elapsed: 0.085 s
% 0.22/0.51  % (22636)------------------------------
% 0.22/0.51  % (22636)------------------------------
% 0.22/0.51  % (22658)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (22641)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (22647)Refutation not found, incomplete strategy% (22647)------------------------------
% 0.22/0.52  % (22647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22647)Memory used [KB]: 10746
% 0.22/0.52  % (22647)Time elapsed: 0.100 s
% 0.22/0.52  % (22647)------------------------------
% 0.22/0.52  % (22647)------------------------------
% 0.22/0.52  % (22658)Refutation not found, incomplete strategy% (22658)------------------------------
% 0.22/0.52  % (22658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22656)Refutation not found, incomplete strategy% (22656)------------------------------
% 0.22/0.52  % (22656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22656)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22656)Memory used [KB]: 10746
% 0.22/0.52  % (22656)Time elapsed: 0.103 s
% 0.22/0.52  % (22656)------------------------------
% 0.22/0.52  % (22656)------------------------------
% 0.22/0.52  % (22649)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (22645)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (22645)Refutation not found, incomplete strategy% (22645)------------------------------
% 0.22/0.52  % (22645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22645)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22645)Memory used [KB]: 10746
% 0.22/0.52  % (22645)Time elapsed: 0.109 s
% 0.22/0.52  % (22645)------------------------------
% 0.22/0.52  % (22645)------------------------------
% 0.22/0.52  % (22641)Refutation not found, incomplete strategy% (22641)------------------------------
% 0.22/0.52  % (22641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22658)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22658)Memory used [KB]: 10746
% 0.22/0.52  % (22658)Time elapsed: 0.053 s
% 0.22/0.52  % (22658)------------------------------
% 0.22/0.52  % (22658)------------------------------
% 0.22/0.53  % (22641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22641)Memory used [KB]: 6268
% 0.22/0.53  % (22641)Time elapsed: 0.068 s
% 0.22/0.53  % (22641)------------------------------
% 0.22/0.53  % (22641)------------------------------
% 0.22/0.53  % (22648)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (22648)Refutation not found, incomplete strategy% (22648)------------------------------
% 0.22/0.53  % (22648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22648)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22648)Memory used [KB]: 6268
% 0.22/0.53  % (22648)Time elapsed: 0.109 s
% 0.22/0.53  % (22648)------------------------------
% 0.22/0.53  % (22648)------------------------------
% 1.38/0.54  % (22640)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.54  % (22657)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.54  % (22640)Refutation not found, incomplete strategy% (22640)------------------------------
% 1.38/0.54  % (22640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22640)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22640)Memory used [KB]: 6268
% 1.38/0.54  % (22640)Time elapsed: 0.117 s
% 1.38/0.54  % (22640)------------------------------
% 1.38/0.54  % (22640)------------------------------
% 1.38/0.54  % (22664)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (22638)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (22637)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.54  % (22638)Refutation not found, incomplete strategy% (22638)------------------------------
% 1.38/0.54  % (22638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22638)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22638)Memory used [KB]: 10746
% 1.38/0.54  % (22638)Time elapsed: 0.132 s
% 1.38/0.54  % (22638)------------------------------
% 1.38/0.54  % (22638)------------------------------
% 1.38/0.54  % (22659)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.54  % (22657)Refutation not found, incomplete strategy% (22657)------------------------------
% 1.38/0.54  % (22657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22657)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22657)Memory used [KB]: 1791
% 1.38/0.54  % (22657)Time elapsed: 0.122 s
% 1.38/0.54  % (22657)------------------------------
% 1.38/0.54  % (22657)------------------------------
% 1.38/0.54  % (22659)Refutation not found, incomplete strategy% (22659)------------------------------
% 1.38/0.54  % (22659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (22659)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (22659)Memory used [KB]: 1791
% 1.38/0.54  % (22659)Time elapsed: 0.132 s
% 1.38/0.54  % (22659)------------------------------
% 1.38/0.54  % (22659)------------------------------
% 1.38/0.55  % (22644)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.55  % (22653)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (22644)Refutation not found, incomplete strategy% (22644)------------------------------
% 1.38/0.55  % (22644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (22644)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (22644)Memory used [KB]: 10746
% 1.38/0.55  % (22644)Time elapsed: 0.124 s
% 1.38/0.55  % (22644)------------------------------
% 1.38/0.55  % (22644)------------------------------
% 1.38/0.55  % (22653)Refutation not found, incomplete strategy% (22653)------------------------------
% 1.38/0.55  % (22653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (22653)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (22653)Memory used [KB]: 10618
% 1.38/0.55  % (22653)Time elapsed: 0.141 s
% 1.38/0.55  % (22653)------------------------------
% 1.38/0.55  % (22653)------------------------------
% 1.38/0.55  % (22663)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (22663)Refutation not found, incomplete strategy% (22663)------------------------------
% 1.38/0.55  % (22663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (22663)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (22663)Memory used [KB]: 6268
% 1.38/0.55  % (22663)Time elapsed: 0.141 s
% 1.38/0.55  % (22663)------------------------------
% 1.38/0.55  % (22663)------------------------------
% 1.38/0.55  % (22643)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.55  % (22643)Refutation not found, incomplete strategy% (22643)------------------------------
% 1.56/0.55  % (22643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.55  % (22650)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.55  % (22643)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.55  
% 1.56/0.55  % (22643)Memory used [KB]: 6268
% 1.56/0.55  % (22643)Time elapsed: 0.138 s
% 1.56/0.55  % (22643)------------------------------
% 1.56/0.55  % (22643)------------------------------
% 1.56/0.56  % (22661)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.56  % (22665)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.57  % (22642)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.57  % (22655)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.56/0.57  % (22639)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.57  % (22655)Refutation not found, incomplete strategy% (22655)------------------------------
% 1.56/0.57  % (22655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (22655)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (22655)Memory used [KB]: 10746
% 1.56/0.57  % (22655)Time elapsed: 0.161 s
% 1.56/0.57  % (22655)------------------------------
% 1.56/0.57  % (22655)------------------------------
% 1.56/0.57  % (22639)Refutation not found, incomplete strategy% (22639)------------------------------
% 1.56/0.57  % (22639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (22639)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (22639)Memory used [KB]: 10746
% 1.56/0.57  % (22639)Time elapsed: 0.160 s
% 1.56/0.57  % (22639)------------------------------
% 1.56/0.57  % (22639)------------------------------
% 1.56/0.57  % (22646)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.56/0.57  % (22646)Refutation not found, incomplete strategy% (22646)------------------------------
% 1.56/0.57  % (22646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (22646)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (22646)Memory used [KB]: 10746
% 1.56/0.57  % (22646)Time elapsed: 0.162 s
% 1.56/0.57  % (22646)------------------------------
% 1.56/0.57  % (22646)------------------------------
% 1.56/0.57  % (22651)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.57  % (22654)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.57  % (22651)Refutation not found, incomplete strategy% (22651)------------------------------
% 1.56/0.57  % (22651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (22651)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (22651)Memory used [KB]: 6140
% 1.56/0.57  % (22651)Time elapsed: 0.151 s
% 1.56/0.57  % (22651)------------------------------
% 1.56/0.57  % (22651)------------------------------
% 1.56/0.58  % (22662)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.56/0.58  % (22660)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.58  % (22662)Refutation not found, incomplete strategy% (22662)------------------------------
% 1.56/0.58  % (22662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (22662)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (22662)Memory used [KB]: 10746
% 1.56/0.58  % (22662)Time elapsed: 0.162 s
% 1.56/0.58  % (22662)------------------------------
% 1.56/0.58  % (22662)------------------------------
% 1.56/0.58  % (22661)Refutation not found, incomplete strategy% (22661)------------------------------
% 1.56/0.58  % (22661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (22661)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (22661)Memory used [KB]: 6268
% 1.56/0.58  % (22661)Time elapsed: 0.168 s
% 1.56/0.58  % (22661)------------------------------
% 1.56/0.58  % (22661)------------------------------
% 1.56/0.58  % (22660)Refutation not found, incomplete strategy% (22660)------------------------------
% 1.56/0.58  % (22660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (22660)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (22660)Memory used [KB]: 6268
% 1.56/0.58  % (22660)Time elapsed: 0.173 s
% 1.56/0.58  % (22660)------------------------------
% 1.56/0.58  % (22660)------------------------------
% 1.56/0.58  % (22652)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.58  % (22665)Refutation not found, incomplete strategy% (22665)------------------------------
% 1.56/0.58  % (22665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (22665)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (22665)Memory used [KB]: 1791
% 1.56/0.58  % (22665)Time elapsed: 0.148 s
% 1.56/0.58  % (22665)------------------------------
% 1.56/0.58  % (22665)------------------------------
% 1.56/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.56/0.58  % (22642)# SZS output start Saturation.
% 1.56/0.58  cnf(u13,negated_conjecture,
% 1.56/0.58      v13_waybel_0(sK2,sK0) | v12_waybel_0(sK2,sK0)).
% 1.56/0.58  
% 1.56/0.58  cnf(u30,negated_conjecture,
% 1.56/0.58      v13_waybel_0(sK2,sK0) | ~v12_waybel_0(sK2,sK1)).
% 1.56/0.58  
% 1.56/0.58  cnf(u27,negated_conjecture,
% 1.56/0.58      ~v13_waybel_0(sK2,sK1) | v12_waybel_0(sK2,sK0)).
% 1.56/0.58  
% 1.56/0.58  cnf(u29,negated_conjecture,
% 1.56/0.58      ~v13_waybel_0(sK2,sK1) | ~v12_waybel_0(sK2,sK1)).
% 1.56/0.58  
% 1.56/0.58  cnf(u78,negated_conjecture,
% 1.56/0.58      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 1.56/0.58  
% 1.56/0.58  cnf(u22,axiom,
% 1.56/0.58      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 1.56/0.58  
% 1.56/0.58  cnf(u23,axiom,
% 1.56/0.58      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 1.56/0.58  
% 1.56/0.58  cnf(u61,negated_conjecture,
% 1.56/0.58      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.56/0.58  
% 1.56/0.58  cnf(u21,axiom,
% 1.56/0.58      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 1.56/0.58  
% 1.56/0.58  cnf(u17,negated_conjecture,
% 1.56/0.58      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.56/0.58  
% 1.56/0.58  cnf(u24,axiom,
% 1.56/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 1.56/0.58  
% 1.56/0.58  cnf(u25,axiom,
% 1.56/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 1.56/0.58  
% 1.56/0.58  cnf(u20,negated_conjecture,
% 1.56/0.58      l1_orders_2(sK0)).
% 1.56/0.58  
% 1.56/0.58  cnf(u18,negated_conjecture,
% 1.56/0.58      l1_orders_2(sK1)).
% 1.56/0.58  
% 1.56/0.58  cnf(u31,axiom,
% 1.56/0.58      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.56/0.58  
% 1.56/0.58  cnf(u49,axiom,
% 1.56/0.58      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.56/0.58  
% 1.56/0.58  cnf(u58,negated_conjecture,
% 1.56/0.58      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 1.56/0.58  
% 1.56/0.58  cnf(u39,negated_conjecture,
% 1.56/0.58      u1_struct_0(sK1) = u1_struct_0(sK0)).
% 1.56/0.58  
% 1.56/0.58  cnf(u16,negated_conjecture,
% 1.56/0.58      sK2 = sK3).
% 1.56/0.58  
% 1.56/0.58  cnf(u33,negated_conjecture,
% 1.56/0.58      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 1.56/0.58  
% 1.56/0.58  cnf(u59,negated_conjecture,
% 1.56/0.58      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 1.56/0.58  
% 1.56/0.58  % (22642)# SZS output end Saturation.
% 1.56/0.58  % (22642)------------------------------
% 1.56/0.58  % (22642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (22642)Termination reason: Satisfiable
% 1.56/0.58  
% 1.56/0.58  % (22642)Memory used [KB]: 6268
% 1.56/0.58  % (22642)Time elapsed: 0.152 s
% 1.56/0.58  % (22642)------------------------------
% 1.56/0.58  % (22642)------------------------------
% 1.56/0.58  % (22635)Success in time 0.205 s
%------------------------------------------------------------------------------
