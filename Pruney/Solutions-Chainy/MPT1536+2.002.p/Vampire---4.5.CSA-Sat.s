%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
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
    ( r2_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK1,sK2) )).

cnf(u11,negated_conjecture,
    ( r2_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2) )).

cnf(u10,negated_conjecture,
    ( ~ r2_yellow_0(sK1,sK2)
    | ~ r1_yellow_0(sK1,sK2) )).

cnf(u12,negated_conjecture,
    ( ~ r2_yellow_0(sK1,sK2)
    | r1_yellow_0(sK0,sK2) )).

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
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (4955)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.49  % (4963)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (4963)Refutation not found, incomplete strategy% (4963)------------------------------
% 0.20/0.49  % (4963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (4963)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (4963)Memory used [KB]: 1663
% 0.20/0.49  % (4963)Time elapsed: 0.077 s
% 0.20/0.49  % (4963)------------------------------
% 0.20/0.49  % (4963)------------------------------
% 0.20/0.50  % (4946)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (4946)Refutation not found, incomplete strategy% (4946)------------------------------
% 0.20/0.51  % (4946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4946)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4946)Memory used [KB]: 6268
% 0.20/0.51  % (4946)Time elapsed: 0.100 s
% 0.20/0.51  % (4946)------------------------------
% 0.20/0.51  % (4946)------------------------------
% 0.20/0.51  % (4954)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (4954)Refutation not found, incomplete strategy% (4954)------------------------------
% 0.20/0.51  % (4954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4954)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4954)Memory used [KB]: 6268
% 0.20/0.51  % (4954)Time elapsed: 0.104 s
% 0.20/0.51  % (4954)------------------------------
% 0.20/0.51  % (4954)------------------------------
% 0.20/0.52  % (4962)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (4971)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (4971)Refutation not found, incomplete strategy% (4971)------------------------------
% 0.20/0.52  % (4971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4971)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (4971)Memory used [KB]: 1791
% 0.20/0.52  % (4971)Time elapsed: 0.122 s
% 0.20/0.52  % (4971)------------------------------
% 0.20/0.52  % (4971)------------------------------
% 0.20/0.52  % (4944)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (4956)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (4953)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (4965)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (4952)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (4944)Refutation not found, incomplete strategy% (4944)------------------------------
% 0.20/0.53  % (4944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4944)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4944)Memory used [KB]: 10746
% 0.20/0.53  % (4944)Time elapsed: 0.116 s
% 0.20/0.53  % (4944)------------------------------
% 0.20/0.53  % (4944)------------------------------
% 0.20/0.53  % (4945)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (4947)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (4966)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (4942)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (4945)Refutation not found, incomplete strategy% (4945)------------------------------
% 0.20/0.53  % (4945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4945)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4945)Memory used [KB]: 10746
% 0.20/0.53  % (4945)Time elapsed: 0.117 s
% 0.20/0.53  % (4945)------------------------------
% 0.20/0.53  % (4945)------------------------------
% 0.20/0.53  % (4947)Refutation not found, incomplete strategy% (4947)------------------------------
% 0.20/0.53  % (4947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4947)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4947)Memory used [KB]: 6268
% 0.20/0.53  % (4947)Time elapsed: 0.128 s
% 0.20/0.53  % (4947)------------------------------
% 0.20/0.53  % (4947)------------------------------
% 0.20/0.53  % (4942)Refutation not found, incomplete strategy% (4942)------------------------------
% 0.20/0.53  % (4942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4942)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (4942)Memory used [KB]: 1663
% 0.20/0.53  % (4942)Time elapsed: 0.126 s
% 0.20/0.53  % (4942)------------------------------
% 0.20/0.53  % (4942)------------------------------
% 0.20/0.53  % (4943)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (4970)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (4969)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (4948)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (4948)# SZS output start Saturation.
% 0.20/0.53  cnf(u9,negated_conjecture,
% 0.20/0.53      r2_yellow_0(sK0,sK2) | ~r1_yellow_0(sK1,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u11,negated_conjecture,
% 0.20/0.53      r2_yellow_0(sK0,sK2) | r1_yellow_0(sK0,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u10,negated_conjecture,
% 0.20/0.53      ~r2_yellow_0(sK1,sK2) | ~r1_yellow_0(sK1,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u12,negated_conjecture,
% 0.20/0.53      ~r2_yellow_0(sK1,sK2) | r1_yellow_0(sK0,sK2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u52,negated_conjecture,
% 0.20/0.53      m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))).
% 0.20/0.53  
% 0.20/0.53  cnf(u16,axiom,
% 0.20/0.53      m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u17,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u18,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3).
% 0.20/0.53  
% 0.20/0.53  cnf(u15,negated_conjecture,
% 0.20/0.53      l1_orders_2(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u13,negated_conjecture,
% 0.20/0.53      l1_orders_2(sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u19,axiom,
% 0.20/0.53      ~l1_orders_2(X0) | u1_struct_0(X0) = X1 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,axiom,
% 0.20/0.53      ~l1_orders_2(X0) | u1_orders_2(X0) = X2 | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u49,negated_conjecture,
% 0.20/0.53      u1_orders_2(sK0) = u1_orders_2(sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u27,negated_conjecture,
% 0.20/0.53      u1_struct_0(sK0) = u1_struct_0(sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u21,negated_conjecture,
% 0.20/0.53      g1_orders_2(X2,X3) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) | u1_struct_0(sK0) = X2).
% 0.20/0.53  
% 0.20/0.53  cnf(u45,negated_conjecture,
% 0.20/0.53      g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X3,X2) | u1_orders_2(sK0) = X2).
% 0.20/0.53  
% 0.20/0.53  % (4948)# SZS output end Saturation.
% 0.20/0.53  % (4948)------------------------------
% 0.20/0.53  % (4948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4948)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (4948)Memory used [KB]: 6268
% 0.20/0.53  % (4948)Time elapsed: 0.106 s
% 0.20/0.53  % (4948)------------------------------
% 0.20/0.53  % (4948)------------------------------
% 0.20/0.53  % (4941)Success in time 0.177 s
%------------------------------------------------------------------------------
