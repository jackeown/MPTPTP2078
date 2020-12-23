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
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u46,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u14,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u15,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u16,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u13,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u10,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u17,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u37,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u43,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u25,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u19,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u44,negated_conjecture,
    ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_orders_2(sK0) = X1 )).

cnf(u12,negated_conjecture,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (8663)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.49  % (8671)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (8663)Refutation not found, incomplete strategy% (8663)------------------------------
% 0.20/0.50  % (8663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8663)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8663)Memory used [KB]: 10618
% 0.20/0.50  % (8663)Time elapsed: 0.092 s
% 0.20/0.50  % (8663)------------------------------
% 0.20/0.50  % (8663)------------------------------
% 0.20/0.50  % (8660)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (8660)Refutation not found, incomplete strategy% (8660)------------------------------
% 0.20/0.50  % (8660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8660)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8660)Memory used [KB]: 6268
% 0.20/0.50  % (8660)Time elapsed: 0.107 s
% 0.20/0.50  % (8660)------------------------------
% 0.20/0.50  % (8660)------------------------------
% 0.20/0.50  % (8675)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (8659)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (8675)Refutation not found, incomplete strategy% (8675)------------------------------
% 0.20/0.51  % (8675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8675)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8675)Memory used [KB]: 10746
% 0.20/0.51  % (8675)Time elapsed: 0.075 s
% 0.20/0.51  % (8675)------------------------------
% 0.20/0.51  % (8675)------------------------------
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (8659)# SZS output start Saturation.
% 0.20/0.51  cnf(u46,negated_conjecture,
% 0.20/0.51      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u14,axiom,
% 0.20/0.51      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u15,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.20/0.51  
% 0.20/0.51  cnf(u16,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.20/0.51  
% 0.20/0.51  cnf(u13,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u10,negated_conjecture,
% 0.20/0.51      l1_orders_2(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u17,axiom,
% 0.20/0.51      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,negated_conjecture,
% 0.20/0.51      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u25,negated_conjecture,
% 0.20/0.51      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u19,negated_conjecture,
% 0.20/0.51      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,negated_conjecture,
% 0.20/0.51      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u12,negated_conjecture,
% 0.20/0.51      k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)).
% 0.20/0.51  
% 0.20/0.51  % (8659)# SZS output end Saturation.
% 0.20/0.51  % (8659)------------------------------
% 0.20/0.51  % (8659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8659)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (8659)Memory used [KB]: 6268
% 0.20/0.51  % (8659)Time elapsed: 0.109 s
% 0.20/0.51  % (8659)------------------------------
% 0.20/0.51  % (8659)------------------------------
% 0.20/0.51  % (8652)Success in time 0.151 s
%------------------------------------------------------------------------------
