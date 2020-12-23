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
% DateTime   : Thu Dec  3 13:17:04 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (13277)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (13277)Refutation not found, incomplete strategy% (13277)------------------------------
% 0.21/0.51  % (13277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13272)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13268)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (13272)Refutation not found, incomplete strategy% (13272)------------------------------
% 0.21/0.51  % (13272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13272)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13272)Memory used [KB]: 6268
% 0.21/0.51  % (13272)Time elapsed: 0.110 s
% 0.21/0.51  % (13272)------------------------------
% 0.21/0.51  % (13272)------------------------------
% 0.21/0.51  % (13268)Refutation not found, incomplete strategy% (13268)------------------------------
% 0.21/0.51  % (13268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13273)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (13285)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (13277)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13277)Memory used [KB]: 10746
% 0.21/0.51  % (13277)Time elapsed: 0.095 s
% 0.21/0.51  % (13277)------------------------------
% 0.21/0.51  % (13277)------------------------------
% 0.21/0.51  % (13275)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (13268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13268)Memory used [KB]: 1791
% 0.21/0.51  % (13268)Time elapsed: 0.103 s
% 0.21/0.51  % (13268)------------------------------
% 0.21/0.51  % (13268)------------------------------
% 0.21/0.51  % (13293)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (13283)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (13283)Refutation not found, incomplete strategy% (13283)------------------------------
% 0.21/0.52  % (13283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13283)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13283)Memory used [KB]: 6140
% 0.21/0.52  % (13283)Time elapsed: 0.108 s
% 0.21/0.52  % (13283)------------------------------
% 0.21/0.52  % (13283)------------------------------
% 0.21/0.52  % (13282)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (13293)Refutation not found, incomplete strategy% (13293)------------------------------
% 0.21/0.52  % (13293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13275)Refutation not found, incomplete strategy% (13275)------------------------------
% 0.21/0.52  % (13275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13275)Memory used [KB]: 6268
% 0.21/0.52  % (13275)Time elapsed: 0.110 s
% 0.21/0.52  % (13275)------------------------------
% 0.21/0.52  % (13275)------------------------------
% 0.21/0.52  % (13285)Refutation not found, incomplete strategy% (13285)------------------------------
% 0.21/0.52  % (13285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13293)Memory used [KB]: 6268
% 0.21/0.52  % (13293)Time elapsed: 0.106 s
% 0.21/0.52  % (13293)------------------------------
% 0.21/0.52  % (13293)------------------------------
% 0.21/0.52  % (13285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13285)Memory used [KB]: 10618
% 0.21/0.52  % (13285)Time elapsed: 0.115 s
% 0.21/0.52  % (13285)------------------------------
% 0.21/0.52  % (13285)------------------------------
% 0.21/0.52  % (13290)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13280)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13290)Refutation not found, incomplete strategy% (13290)------------------------------
% 0.21/0.53  % (13290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13290)Memory used [KB]: 10746
% 0.21/0.53  % (13290)Time elapsed: 0.081 s
% 0.21/0.53  % (13290)------------------------------
% 0.21/0.53  % (13290)------------------------------
% 0.21/0.53  % (13269)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13297)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (13294)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (13297)Refutation not found, incomplete strategy% (13297)------------------------------
% 0.21/0.53  % (13297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13297)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13297)Memory used [KB]: 1791
% 0.21/0.53  % (13297)Time elapsed: 0.133 s
% 0.21/0.53  % (13297)------------------------------
% 0.21/0.53  % (13297)------------------------------
% 0.21/0.53  % (13288)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (13295)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (13291)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13270)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (13271)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (13288)Refutation not found, incomplete strategy% (13288)------------------------------
% 0.21/0.53  % (13288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13288)Memory used [KB]: 10746
% 0.21/0.53  % (13288)Time elapsed: 0.134 s
% 0.21/0.53  % (13288)------------------------------
% 0.21/0.53  % (13288)------------------------------
% 0.21/0.53  % (13273)Refutation not found, incomplete strategy% (13273)------------------------------
% 0.21/0.53  % (13273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13273)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13273)Memory used [KB]: 6268
% 0.21/0.53  % (13273)Time elapsed: 0.125 s
% 0.21/0.53  % (13273)------------------------------
% 0.21/0.53  % (13273)------------------------------
% 0.21/0.53  % (13270)Refutation not found, incomplete strategy% (13270)------------------------------
% 0.21/0.53  % (13270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13270)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13270)Memory used [KB]: 10746
% 0.21/0.53  % (13270)Time elapsed: 0.126 s
% 0.21/0.53  % (13270)------------------------------
% 0.21/0.53  % (13270)------------------------------
% 0.21/0.54  % (13271)Refutation not found, incomplete strategy% (13271)------------------------------
% 0.21/0.54  % (13271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13271)Memory used [KB]: 10746
% 0.21/0.54  % (13271)Time elapsed: 0.125 s
% 0.21/0.54  % (13271)------------------------------
% 0.21/0.54  % (13271)------------------------------
% 0.21/0.54  % (13274)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13292)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13280)Refutation not found, incomplete strategy% (13280)------------------------------
% 0.21/0.54  % (13280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13280)Memory used [KB]: 6268
% 0.21/0.54  % (13280)Time elapsed: 0.134 s
% 0.21/0.54  % (13280)------------------------------
% 0.21/0.54  % (13280)------------------------------
% 0.21/0.54  % (13281)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (13274)# SZS output start Saturation.
% 0.21/0.54  cnf(u13,negated_conjecture,
% 0.21/0.54      v13_waybel_0(sK2,sK0) | v12_waybel_0(sK2,sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u30,negated_conjecture,
% 0.21/0.54      v13_waybel_0(sK2,sK0) | ~v12_waybel_0(sK2,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u27,negated_conjecture,
% 0.21/0.54      ~v13_waybel_0(sK2,sK1) | v12_waybel_0(sK2,sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u29,negated_conjecture,
% 0.21/0.54      ~v13_waybel_0(sK2,sK1) | ~v12_waybel_0(sK2,sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u78,negated_conjecture,
% 0.21/0.54      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u22,axiom,
% 0.21/0.54      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u23,axiom,
% 0.21/0.54      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u61,negated_conjecture,
% 0.21/0.54      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.21/0.54  
% 0.21/0.54  cnf(u21,axiom,
% 0.21/0.54      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u17,negated_conjecture,
% 0.21/0.54      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  cnf(u24,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.21/0.54  
% 0.21/0.54  cnf(u25,axiom,
% 0.21/0.54      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.21/0.54  
% 0.21/0.54  cnf(u20,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u18,negated_conjecture,
% 0.21/0.54      l1_orders_2(sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u31,axiom,
% 0.21/0.54      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u49,axiom,
% 0.21/0.54      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.21/0.54  
% 0.21/0.54  cnf(u58,negated_conjecture,
% 0.21/0.54      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.21/0.54  
% 0.21/0.54  cnf(u39,negated_conjecture,
% 0.21/0.54      u1_struct_0(sK1) = u1_struct_0(sK0)).
% 0.21/0.54  
% 0.21/0.54  cnf(u16,negated_conjecture,
% 0.21/0.54      sK2 = sK3).
% 0.21/0.54  
% 0.21/0.54  cnf(u33,negated_conjecture,
% 0.21/0.54      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.21/0.54  
% 0.21/0.54  cnf(u59,negated_conjecture,
% 0.21/0.54      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.21/0.54  
% 0.21/0.54  % (13274)# SZS output end Saturation.
% 0.21/0.54  % (13274)------------------------------
% 0.21/0.54  % (13274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13274)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (13274)Memory used [KB]: 6268
% 0.21/0.54  % (13274)Time elapsed: 0.096 s
% 0.21/0.54  % (13274)------------------------------
% 0.21/0.54  % (13274)------------------------------
% 0.21/0.54  % (13267)Success in time 0.176 s
%------------------------------------------------------------------------------
