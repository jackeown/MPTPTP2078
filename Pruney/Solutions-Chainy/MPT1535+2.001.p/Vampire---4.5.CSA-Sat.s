%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u9,negated_conjecture,
    ( v2_yellow_0(sK0)
    | ~ v1_yellow_0(sK1) )).

cnf(u11,negated_conjecture,
    ( v2_yellow_0(sK0)
    | v1_yellow_0(sK0) )).

cnf(u10,negated_conjecture,
    ( ~ v2_yellow_0(sK1)
    | ~ v1_yellow_0(sK1) )).

cnf(u12,negated_conjecture,
    ( ~ v2_yellow_0(sK1)
    | v1_yellow_0(sK0) )).

cnf(u52,negated_conjecture,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) )).

cnf(u16,axiom,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) )).

cnf(u17,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X0 = X2 )).

cnf(u18,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
    | X1 = X3 )).

cnf(u15,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u13,negated_conjecture,
    ( l1_orders_2(sK1) )).

cnf(u19,axiom,
    ( ~ l1_orders_2(X0)
    | u1_struct_0(X0) = X1
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u39,axiom,
    ( ~ l1_orders_2(X0)
    | u1_orders_2(X0) = X2
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2) )).

cnf(u49,negated_conjecture,
    ( u1_orders_2(sK0) = u1_orders_2(sK1) )).

cnf(u27,negated_conjecture,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) )).

cnf(u21,negated_conjecture,
    ( g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = X2 )).

cnf(u45,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X3,X2)
    | u1_orders_2(sK0) = X2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:05:38 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.22/0.51  % (17739)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (17731)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (17730)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (17723)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (17739)Refutation not found, incomplete strategy% (17739)------------------------------
% 0.22/0.52  % (17739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (17739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17739)Memory used [KB]: 10746
% 0.22/0.52  % (17739)Time elapsed: 0.072 s
% 0.22/0.52  % (17739)------------------------------
% 0.22/0.52  % (17739)------------------------------
% 0.22/0.52  % (17723)# SZS output start Saturation.
% 0.22/0.52  cnf(u9,negated_conjecture,
% 0.22/0.52      v2_yellow_0(sK0) | ~v1_yellow_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u11,negated_conjecture,
% 0.22/0.52      v2_yellow_0(sK0) | v1_yellow_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u10,negated_conjecture,
% 0.22/0.52      ~v2_yellow_0(sK1) | ~v1_yellow_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u12,negated_conjecture,
% 0.22/0.52      ~v2_yellow_0(sK1) | v1_yellow_0(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u52,negated_conjecture,
% 0.22/0.52      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.52  
% 0.22/0.52  cnf(u16,axiom,
% 0.22/0.52      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u17,axiom,
% 0.22/0.52      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.22/0.52  
% 0.22/0.52  cnf(u18,axiom,
% 0.22/0.52      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.22/0.52  
% 0.22/0.52  cnf(u15,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u13,negated_conjecture,
% 0.22/0.52      l1_orders_2(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u19,axiom,
% 0.22/0.52      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u39,axiom,
% 0.22/0.52      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u49,negated_conjecture,
% 0.22/0.52      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u27,negated_conjecture,
% 0.22/0.52      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u21,negated_conjecture,
% 0.22/0.52      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.22/0.52  
% 0.22/0.52  cnf(u45,negated_conjecture,
% 0.22/0.52      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X3,X2) | u1_orders_2(sK0) = X2).
% 0.22/0.52  
% 0.22/0.52  % (17723)# SZS output end Saturation.
% 0.22/0.52  % (17723)------------------------------
% 0.22/0.52  % (17723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17723)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (17723)Memory used [KB]: 6268
% 0.22/0.52  % (17723)Time elapsed: 0.074 s
% 0.22/0.52  % (17723)------------------------------
% 0.22/0.52  % (17723)------------------------------
% 0.22/0.52  % (17716)Success in time 0.166 s
%------------------------------------------------------------------------------
