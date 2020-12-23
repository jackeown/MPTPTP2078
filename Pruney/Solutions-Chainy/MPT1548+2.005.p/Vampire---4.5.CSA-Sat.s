%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:02 EST 2020

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
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.56  % (512)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (524)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.57  % (513)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.58  % (524)Refutation not found, incomplete strategy% (524)------------------------------
% 0.20/0.58  % (524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (524)Memory used [KB]: 1663
% 0.20/0.58  % (524)Time elapsed: 0.077 s
% 0.20/0.58  % (524)------------------------------
% 0.20/0.58  % (524)------------------------------
% 0.20/0.58  % (513)Refutation not found, incomplete strategy% (513)------------------------------
% 0.20/0.58  % (513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (513)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (513)Memory used [KB]: 6140
% 0.20/0.58  % (513)Time elapsed: 0.074 s
% 0.20/0.58  % (513)------------------------------
% 0.20/0.58  % (513)------------------------------
% 0.20/0.58  % (505)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.58  % (504)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.58  % (505)Refutation not found, incomplete strategy% (505)------------------------------
% 0.20/0.58  % (505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (505)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (505)Memory used [KB]: 6268
% 0.20/0.58  % (505)Time elapsed: 0.084 s
% 0.20/0.58  % (505)------------------------------
% 0.20/0.58  % (505)------------------------------
% 0.20/0.58  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.58  % (504)# SZS output start Saturation.
% 0.20/0.58  cnf(u46,negated_conjecture,
% 0.20/0.58      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.58  
% 0.20/0.58  cnf(u14,axiom,
% 0.20/0.58      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.58  
% 0.20/0.58  cnf(u15,axiom,
% 0.20/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.20/0.58  
% 0.20/0.58  cnf(u16,axiom,
% 0.20/0.58      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.20/0.58  
% 0.20/0.58  cnf(u13,negated_conjecture,
% 0.20/0.58      l1_orders_2(sK0)).
% 0.20/0.58  
% 0.20/0.58  cnf(u10,negated_conjecture,
% 0.20/0.58      l1_orders_2(sK1)).
% 0.20/0.58  
% 0.20/0.58  cnf(u17,axiom,
% 0.20/0.58      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.58  
% 0.20/0.58  cnf(u37,axiom,
% 0.20/0.58      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.58  
% 0.20/0.58  cnf(u43,negated_conjecture,
% 0.20/0.58      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.20/0.58  
% 0.20/0.58  cnf(u25,negated_conjecture,
% 0.20/0.58      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.58  
% 0.20/0.58  cnf(u19,negated_conjecture,
% 0.20/0.58      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.20/0.58  
% 0.20/0.58  cnf(u44,negated_conjecture,
% 0.20/0.58      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.20/0.58  
% 0.20/0.58  cnf(u12,negated_conjecture,
% 0.20/0.58      k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)).
% 0.20/0.58  
% 0.20/0.58  % (504)# SZS output end Saturation.
% 0.20/0.58  % (504)------------------------------
% 0.20/0.58  % (504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (504)Termination reason: Satisfiable
% 0.20/0.58  
% 0.20/0.58  % (504)Memory used [KB]: 6268
% 0.20/0.58  % (504)Time elapsed: 0.142 s
% 0.20/0.58  % (504)------------------------------
% 0.20/0.58  % (504)------------------------------
% 0.20/0.59  % (485)Success in time 0.221 s
%------------------------------------------------------------------------------
