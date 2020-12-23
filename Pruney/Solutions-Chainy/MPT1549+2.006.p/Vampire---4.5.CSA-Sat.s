%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:03 EST 2020

% Result     : CounterSatisfiable 1.69s
% Output     : Saturation 1.69s
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.45/0.56  % (29504)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (29485)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.57  % (29496)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.57  % (29499)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.57  % (29504)Refutation not found, incomplete strategy% (29504)------------------------------
% 1.45/0.57  % (29504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (29496)Refutation not found, incomplete strategy% (29496)------------------------------
% 1.45/0.57  % (29496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (29504)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (29504)Memory used [KB]: 1663
% 1.45/0.57  % (29504)Time elapsed: 0.085 s
% 1.45/0.57  % (29504)------------------------------
% 1.45/0.57  % (29504)------------------------------
% 1.45/0.57  % (29500)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.57  % (29496)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (29496)Memory used [KB]: 6140
% 1.45/0.57  % (29496)Time elapsed: 0.081 s
% 1.45/0.57  % (29496)------------------------------
% 1.45/0.57  % (29496)------------------------------
% 1.45/0.57  % (29490)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.57  % (29488)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.69/0.58  % (29487)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.69/0.58  % (29488)Refutation not found, incomplete strategy% (29488)------------------------------
% 1.69/0.58  % (29488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (29488)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (29488)Memory used [KB]: 6268
% 1.69/0.58  % (29488)Time elapsed: 0.092 s
% 1.69/0.58  % (29488)------------------------------
% 1.69/0.58  % (29488)------------------------------
% 1.69/0.58  % (29492)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.69/0.58  % (29487)# SZS output start Saturation.
% 1.69/0.58  cnf(u46,negated_conjecture,
% 1.69/0.58      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 1.69/0.58  
% 1.69/0.58  cnf(u14,axiom,
% 1.69/0.58      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 1.69/0.58  
% 1.69/0.58  cnf(u15,axiom,
% 1.69/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 1.69/0.58  
% 1.69/0.58  cnf(u16,axiom,
% 1.69/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 1.69/0.58  
% 1.69/0.58  cnf(u13,negated_conjecture,
% 1.69/0.58      l1_orders_2(sK0)).
% 1.69/0.58  
% 1.69/0.58  cnf(u10,negated_conjecture,
% 1.69/0.58      l1_orders_2(sK1)).
% 1.69/0.58  
% 1.69/0.58  cnf(u17,axiom,
% 1.69/0.58      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.69/0.58  
% 1.69/0.58  cnf(u37,axiom,
% 1.69/0.58      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 1.69/0.58  
% 1.69/0.58  cnf(u43,negated_conjecture,
% 1.69/0.58      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 1.69/0.58  
% 1.69/0.58  cnf(u25,negated_conjecture,
% 1.69/0.58      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 1.69/0.58  
% 1.69/0.58  cnf(u19,negated_conjecture,
% 1.69/0.58      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 1.69/0.58  
% 1.69/0.58  cnf(u44,negated_conjecture,
% 1.69/0.58      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 1.69/0.58  
% 1.69/0.58  cnf(u12,negated_conjecture,
% 1.69/0.58      k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)).
% 1.69/0.58  
% 1.69/0.58  % (29487)# SZS output end Saturation.
% 1.69/0.58  % (29487)------------------------------
% 1.69/0.58  % (29487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (29487)Termination reason: Satisfiable
% 1.69/0.58  
% 1.69/0.58  % (29487)Memory used [KB]: 6268
% 1.69/0.58  % (29487)Time elapsed: 0.153 s
% 1.69/0.58  % (29487)------------------------------
% 1.69/0.58  % (29487)------------------------------
% 1.69/0.58  % (29480)Success in time 0.215 s
%------------------------------------------------------------------------------
