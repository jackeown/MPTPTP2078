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

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:18:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (6485)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (6504)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (6496)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (6485)Refutation not found, incomplete strategy% (6485)------------------------------
% 0.22/0.56  % (6485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6485)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6485)Memory used [KB]: 6268
% 0.22/0.56  % (6485)Time elapsed: 0.128 s
% 0.22/0.56  % (6485)------------------------------
% 0.22/0.56  % (6485)------------------------------
% 0.22/0.56  % (6504)Refutation not found, incomplete strategy% (6504)------------------------------
% 0.22/0.56  % (6504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6496)Refutation not found, incomplete strategy% (6496)------------------------------
% 0.22/0.56  % (6496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6496)Memory used [KB]: 6140
% 0.22/0.56  % (6496)Time elapsed: 0.075 s
% 0.22/0.56  % (6496)------------------------------
% 0.22/0.56  % (6496)------------------------------
% 0.22/0.56  % (6504)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6504)Memory used [KB]: 1791
% 0.22/0.56  % (6504)Time elapsed: 0.068 s
% 0.22/0.56  % (6504)------------------------------
% 0.22/0.56  % (6504)------------------------------
% 0.22/0.56  % (6493)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (6488)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (6493)Refutation not found, incomplete strategy% (6493)------------------------------
% 0.22/0.56  % (6493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6493)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6493)Memory used [KB]: 6268
% 0.22/0.56  % (6493)Time elapsed: 0.130 s
% 0.22/0.56  % (6493)------------------------------
% 0.22/0.56  % (6493)------------------------------
% 0.22/0.56  % (6488)Refutation not found, incomplete strategy% (6488)------------------------------
% 0.22/0.56  % (6488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6488)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6488)Memory used [KB]: 6268
% 0.22/0.56  % (6488)Time elapsed: 0.074 s
% 0.22/0.56  % (6488)------------------------------
% 0.22/0.56  % (6488)------------------------------
% 0.22/0.56  % (6503)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (6503)Refutation not found, incomplete strategy% (6503)------------------------------
% 0.22/0.57  % (6503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (6503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (6503)Memory used [KB]: 10746
% 0.22/0.57  % (6503)Time elapsed: 0.140 s
% 0.22/0.57  % (6503)------------------------------
% 0.22/0.57  % (6503)------------------------------
% 0.22/0.57  % (6486)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (6489)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.59  % (6487)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.59  % (6487)# SZS output start Saturation.
% 0.22/0.59  cnf(u13,negated_conjecture,
% 0.22/0.59      v13_waybel_0(sK2,sK0) | v12_waybel_0(sK2,sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u30,negated_conjecture,
% 0.22/0.59      v13_waybel_0(sK2,sK0) | ~v12_waybel_0(sK2,sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u27,negated_conjecture,
% 0.22/0.59      ~v13_waybel_0(sK2,sK1) | v12_waybel_0(sK2,sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u29,negated_conjecture,
% 0.22/0.59      ~v13_waybel_0(sK2,sK1) | ~v12_waybel_0(sK2,sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u78,negated_conjecture,
% 0.22/0.59      ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_orders_2(sK1,X0,X1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u22,axiom,
% 0.22/0.59      ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u23,axiom,
% 0.22/0.59      ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u61,negated_conjecture,
% 0.22/0.59      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.59  
% 0.22/0.59  cnf(u21,axiom,
% 0.22/0.59      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u17,negated_conjecture,
% 0.22/0.59      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.59  
% 0.22/0.59  cnf(u24,axiom,
% 0.22/0.59      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.22/0.59  
% 0.22/0.59  cnf(u25,axiom,
% 0.22/0.59      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.22/0.59  
% 0.22/0.59  cnf(u20,negated_conjecture,
% 0.22/0.59      l1_orders_2(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u18,negated_conjecture,
% 0.22/0.59      l1_orders_2(sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u31,axiom,
% 0.22/0.59      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u49,axiom,
% 0.22/0.59      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.59  
% 0.22/0.59  cnf(u58,negated_conjecture,
% 0.22/0.59      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.22/0.59  
% 0.22/0.59  cnf(u39,negated_conjecture,
% 0.22/0.59      u1_struct_0(sK1) = u1_struct_0(sK0)).
% 0.22/0.59  
% 0.22/0.59  cnf(u16,negated_conjecture,
% 0.22/0.59      sK2 = sK3).
% 0.22/0.59  
% 0.22/0.59  cnf(u33,negated_conjecture,
% 0.22/0.59      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.22/0.59  
% 0.22/0.59  cnf(u59,negated_conjecture,
% 0.22/0.59      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.22/0.59  
% 0.22/0.59  % (6487)# SZS output end Saturation.
% 0.22/0.59  % (6487)------------------------------
% 0.22/0.59  % (6487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (6487)Termination reason: Satisfiable
% 0.22/0.59  
% 0.22/0.59  % (6487)Memory used [KB]: 6268
% 0.22/0.59  % (6487)Time elapsed: 0.163 s
% 0.22/0.59  % (6487)------------------------------
% 0.22/0.59  % (6487)------------------------------
% 0.22/0.59  % (6482)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (6480)Success in time 0.224 s
%------------------------------------------------------------------------------
