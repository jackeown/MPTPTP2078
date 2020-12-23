%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:02 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:25:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (13850)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.46  % (13834)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.47  % (13834)Refutation not found, incomplete strategy% (13834)------------------------------
% 0.22/0.47  % (13834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (13834)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (13834)Memory used [KB]: 6268
% 0.22/0.47  % (13834)Time elapsed: 0.057 s
% 0.22/0.47  % (13834)------------------------------
% 0.22/0.47  % (13834)------------------------------
% 0.22/0.47  % (13850)Refutation not found, incomplete strategy% (13850)------------------------------
% 0.22/0.47  % (13850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (13850)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (13850)Memory used [KB]: 1663
% 0.22/0.47  % (13850)Time elapsed: 0.057 s
% 0.22/0.47  % (13850)------------------------------
% 0.22/0.47  % (13850)------------------------------
% 0.22/0.51  % (13829)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (13828)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (13839)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (13839)Refutation not found, incomplete strategy% (13839)------------------------------
% 0.22/0.52  % (13839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13839)Memory used [KB]: 6268
% 0.22/0.52  % (13839)Time elapsed: 0.121 s
% 0.22/0.52  % (13839)------------------------------
% 0.22/0.52  % (13839)------------------------------
% 0.22/0.52  % (13832)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (13838)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (13832)Refutation not found, incomplete strategy% (13832)------------------------------
% 0.22/0.52  % (13832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13832)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13832)Memory used [KB]: 6268
% 0.22/0.52  % (13832)Time elapsed: 0.118 s
% 0.22/0.52  % (13832)------------------------------
% 0.22/0.52  % (13832)------------------------------
% 0.22/0.52  % (13838)Refutation not found, incomplete strategy% (13838)------------------------------
% 0.22/0.52  % (13838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13838)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13838)Memory used [KB]: 10746
% 0.22/0.52  % (13838)Time elapsed: 0.118 s
% 0.22/0.52  % (13838)------------------------------
% 0.22/0.52  % (13838)------------------------------
% 0.22/0.53  % (13855)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (13833)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.53  % (13833)# SZS output start Saturation.
% 0.22/0.53  cnf(u46,negated_conjecture,
% 0.22/0.53      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.22/0.53  
% 0.22/0.53  cnf(u14,axiom,
% 0.22/0.53      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u15,axiom,
% 0.22/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.22/0.53  
% 0.22/0.53  cnf(u16,axiom,
% 0.22/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.22/0.53  
% 0.22/0.53  cnf(u13,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK0)).
% 0.22/0.53  
% 0.22/0.53  cnf(u10,negated_conjecture,
% 0.22/0.53      l1_orders_2(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u17,axiom,
% 0.22/0.53      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u37,axiom,
% 0.22/0.53      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.22/0.53  
% 0.22/0.53  cnf(u43,negated_conjecture,
% 0.22/0.53      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u25,negated_conjecture,
% 0.22/0.53      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.22/0.53  
% 0.22/0.53  cnf(u19,negated_conjecture,
% 0.22/0.53      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.22/0.53  
% 0.22/0.53  cnf(u44,negated_conjecture,
% 0.22/0.53      g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_orders_2(sK0) = X1).
% 0.22/0.53  
% 0.22/0.53  cnf(u12,negated_conjecture,
% 0.22/0.53      k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)).
% 0.22/0.53  
% 0.22/0.53  % (13833)# SZS output end Saturation.
% 0.22/0.53  % (13833)------------------------------
% 0.22/0.53  % (13833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13833)Termination reason: Satisfiable
% 0.22/0.53  
% 0.22/0.53  % (13833)Memory used [KB]: 6268
% 0.22/0.53  % (13833)Time elapsed: 0.103 s
% 0.22/0.53  % (13833)------------------------------
% 0.22/0.53  % (13833)------------------------------
% 0.22/0.53  % (13826)Success in time 0.165 s
%------------------------------------------------------------------------------
