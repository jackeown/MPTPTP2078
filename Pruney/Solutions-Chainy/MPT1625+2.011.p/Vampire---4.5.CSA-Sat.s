%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:54 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :   95 (  95 expanded)
%              Number of equality atoms :   66 (  66 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,negated_conjecture,
    ( v3_orders_2(sK0) )).

cnf(u36,axiom,
    ( ~ v3_orders_2(X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0) )).

cnf(u58,negated_conjecture,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u32,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK0))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X1,X0)
    | k6_domain_1(X0,X1) = k1_tarski(X1)
    | v1_xboole_0(X0) )).

cnf(u31,negated_conjecture,
    ( l1_orders_2(sK0) )).

cnf(u34,axiom,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) )).

cnf(u72,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1)) )).

cnf(u35,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u45,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u40,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u43,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u198,axiom,
    ( ~ r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK2(X14,k1_tarski(X13)) != X12
    | k1_tarski(X12) = k1_tarski(X13)
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u41,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u44,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u70,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X1 )).

cnf(u92,axiom,
    ( ~ r2_hidden(X4,k1_tarski(X3))
    | sK2(X2,k1_tarski(X3)) = X4
    | sK2(X2,k1_tarski(X3)) = X2
    | k1_tarski(X3) = k1_tarski(X2) )).

cnf(u95,axiom,
    ( ~ r2_hidden(X13,k1_tarski(X12))
    | k1_tarski(X12) = k1_tarski(X13)
    | sK2(X11,k1_tarski(X12)) = sK2(X13,k1_tarski(X12))
    | sK2(X11,k1_tarski(X12)) = X11
    | k1_tarski(X12) = k1_tarski(X11) )).

cnf(u56,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) )).

cnf(u76,axiom,
    ( sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2)))
    | sK2(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u93,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u48,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u48_001,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u93_002,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u93_003,axiom,
    ( sK2(X7,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X7) = k1_tarski(X6)
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u88,axiom,
    ( k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5)))
    | sK2(X4,k1_tarski(X5)) = X4
    | k1_tarski(X5) = k1_tarski(X4) )).

cnf(u33,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u156,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X2,k1_tarski(X1)) = X2
    | sK2(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u154,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1))
    | sK2(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u65,axiom,
    ( X0 != X1
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u71,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (31402)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (31429)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (31403)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (31405)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (31413)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (31410)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (31406)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31401)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (31401)Refutation not found, incomplete strategy% (31401)------------------------------
% 0.21/0.52  % (31401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31401)Memory used [KB]: 1663
% 0.21/0.52  % (31401)Time elapsed: 0.107 s
% 0.21/0.52  % (31401)------------------------------
% 0.21/0.52  % (31401)------------------------------
% 0.21/0.52  % (31413)Refutation not found, incomplete strategy% (31413)------------------------------
% 0.21/0.52  % (31413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31429)Refutation not found, incomplete strategy% (31429)------------------------------
% 0.21/0.52  % (31429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31429)Memory used [KB]: 1663
% 0.21/0.52  % (31429)Time elapsed: 0.002 s
% 0.21/0.52  % (31429)------------------------------
% 0.21/0.52  % (31429)------------------------------
% 0.21/0.52  % (31413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31413)Memory used [KB]: 6268
% 0.21/0.52  % (31413)Time elapsed: 0.111 s
% 0.21/0.52  % (31413)------------------------------
% 0.21/0.52  % (31413)------------------------------
% 0.21/0.52  % (31407)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (31427)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (31404)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (31427)Refutation not found, incomplete strategy% (31427)------------------------------
% 0.21/0.52  % (31427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31427)Memory used [KB]: 6140
% 0.21/0.52  % (31427)Time elapsed: 0.109 s
% 0.21/0.52  % (31427)------------------------------
% 0.21/0.52  % (31427)------------------------------
% 0.21/0.52  % (31417)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (31404)Refutation not found, incomplete strategy% (31404)------------------------------
% 0.21/0.52  % (31404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31404)Memory used [KB]: 1791
% 0.21/0.52  % (31404)Time elapsed: 0.108 s
% 0.21/0.52  % (31404)------------------------------
% 0.21/0.52  % (31404)------------------------------
% 0.21/0.52  % (31409)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (31425)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (31425)Refutation not found, incomplete strategy% (31425)------------------------------
% 0.21/0.53  % (31425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31425)Memory used [KB]: 6140
% 0.21/0.53  % (31425)Time elapsed: 0.117 s
% 0.21/0.53  % (31425)------------------------------
% 0.21/0.53  % (31425)------------------------------
% 0.21/0.53  % (31410)Refutation not found, incomplete strategy% (31410)------------------------------
% 0.21/0.53  % (31410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31410)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31410)Memory used [KB]: 10618
% 0.21/0.53  % (31410)Time elapsed: 0.122 s
% 0.21/0.53  % (31410)------------------------------
% 0.21/0.53  % (31410)------------------------------
% 0.21/0.53  % (31422)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (31418)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (31420)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (31408)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (31423)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (31418)Refutation not found, incomplete strategy% (31418)------------------------------
% 0.21/0.53  % (31418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31418)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31418)Memory used [KB]: 1663
% 0.21/0.53  % (31418)Time elapsed: 0.121 s
% 0.21/0.53  % (31418)------------------------------
% 0.21/0.53  % (31418)------------------------------
% 0.21/0.53  % (31415)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (31423)Refutation not found, incomplete strategy% (31423)------------------------------
% 0.21/0.53  % (31423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31423)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31423)Memory used [KB]: 10746
% 0.21/0.53  % (31423)Time elapsed: 0.091 s
% 0.21/0.53  % (31423)------------------------------
% 0.21/0.53  % (31423)------------------------------
% 0.21/0.54  % (31417)Refutation not found, incomplete strategy% (31417)------------------------------
% 0.21/0.54  % (31417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31417)Memory used [KB]: 1663
% 0.21/0.54  % (31417)Time elapsed: 0.120 s
% 0.21/0.54  % (31417)------------------------------
% 0.21/0.54  % (31417)------------------------------
% 0.21/0.54  % (31400)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (31426)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (31424)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (31426)Refutation not found, incomplete strategy% (31426)------------------------------
% 0.21/0.54  % (31426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31426)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31426)Memory used [KB]: 6140
% 0.21/0.54  % (31426)Time elapsed: 0.129 s
% 0.21/0.54  % (31426)------------------------------
% 0.21/0.54  % (31426)------------------------------
% 0.21/0.54  % (31428)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (31424)Refutation not found, incomplete strategy% (31424)------------------------------
% 0.21/0.54  % (31424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31424)Memory used [KB]: 10618
% 0.21/0.54  % (31424)Time elapsed: 0.131 s
% 0.21/0.54  % (31424)------------------------------
% 0.21/0.54  % (31424)------------------------------
% 0.21/0.54  % (31428)Refutation not found, incomplete strategy% (31428)------------------------------
% 0.21/0.54  % (31428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31428)Memory used [KB]: 10746
% 0.21/0.54  % (31428)Time elapsed: 0.133 s
% 0.21/0.54  % (31428)------------------------------
% 0.21/0.54  % (31428)------------------------------
% 0.21/0.54  % (31414)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (31414)Refutation not found, incomplete strategy% (31414)------------------------------
% 0.21/0.54  % (31414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31414)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31414)Memory used [KB]: 1663
% 0.21/0.54  % (31414)Time elapsed: 0.131 s
% 0.21/0.54  % (31414)------------------------------
% 0.21/0.54  % (31414)------------------------------
% 0.21/0.54  % (31411)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (31416)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (31411)Refutation not found, incomplete strategy% (31411)------------------------------
% 0.21/0.54  % (31411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31411)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31411)Memory used [KB]: 6140
% 0.21/0.54  % (31411)Time elapsed: 0.133 s
% 0.21/0.54  % (31411)------------------------------
% 0.21/0.54  % (31411)------------------------------
% 0.21/0.54  % (31422)Refutation not found, incomplete strategy% (31422)------------------------------
% 0.21/0.54  % (31422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31422)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31422)Memory used [KB]: 6268
% 0.21/0.54  % (31422)Time elapsed: 0.123 s
% 0.21/0.54  % (31422)------------------------------
% 0.21/0.54  % (31422)------------------------------
% 0.21/0.54  % (31416)Refutation not found, incomplete strategy% (31416)------------------------------
% 0.21/0.54  % (31416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31416)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31416)Memory used [KB]: 10618
% 0.21/0.54  % (31416)Time elapsed: 0.140 s
% 0.21/0.54  % (31416)------------------------------
% 0.21/0.54  % (31416)------------------------------
% 0.21/0.54  % (31421)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (31412)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (31412)Refutation not found, incomplete strategy% (31412)------------------------------
% 0.21/0.55  % (31412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31412)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31412)Memory used [KB]: 10618
% 0.21/0.55  % (31412)Time elapsed: 0.002 s
% 0.21/0.55  % (31412)------------------------------
% 0.21/0.55  % (31412)------------------------------
% 0.21/0.55  % (31421)Refutation not found, incomplete strategy% (31421)------------------------------
% 0.21/0.55  % (31421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31421)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31421)Memory used [KB]: 6268
% 0.21/0.55  % (31421)Time elapsed: 0.140 s
% 0.21/0.55  % (31421)------------------------------
% 0.21/0.55  % (31421)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (31419)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (31407)# SZS output start Saturation.
% 0.21/0.55  cnf(u30,negated_conjecture,
% 0.21/0.55      v3_orders_2(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u36,axiom,
% 0.21/0.55      ~v3_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u58,negated_conjecture,
% 0.21/0.55      m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u32,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u53,negated_conjecture,
% 0.21/0.55      ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u37,axiom,
% 0.21/0.55      ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u31,negated_conjecture,
% 0.21/0.55      l1_orders_2(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u34,axiom,
% 0.21/0.55      ~l1_orders_2(X0) | l1_struct_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u72,negated_conjecture,
% 0.21/0.55      v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(k1_zfmisc_1(u1_struct_0(sK0)),k1_tarski(sK1)) = k1_tarski(k1_tarski(sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u35,axiom,
% 0.21/0.55      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u45,negated_conjecture,
% 0.21/0.55      l1_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u29,negated_conjecture,
% 0.21/0.55      ~v2_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u40,axiom,
% 0.21/0.55      r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u43,axiom,
% 0.21/0.55      r2_hidden(X3,k1_tarski(X3))).
% 0.21/0.55  
% 0.21/0.55  cnf(u198,axiom,
% 0.21/0.55      ~r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13)) | sK2(X14,k1_tarski(X13)) != X12 | k1_tarski(X12) = k1_tarski(X13) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 0.21/0.55  
% 0.21/0.55  cnf(u41,axiom,
% 0.21/0.55      ~r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) != X0 | k1_tarski(X0) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u44,axiom,
% 0.21/0.55      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 0.21/0.55  
% 0.21/0.55  cnf(u70,axiom,
% 0.21/0.55      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u92,axiom,
% 0.21/0.55      ~r2_hidden(X4,k1_tarski(X3)) | sK2(X2,k1_tarski(X3)) = X4 | sK2(X2,k1_tarski(X3)) = X2 | k1_tarski(X3) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u95,axiom,
% 0.21/0.55      ~r2_hidden(X13,k1_tarski(X12)) | k1_tarski(X12) = k1_tarski(X13) | sK2(X11,k1_tarski(X12)) = sK2(X13,k1_tarski(X12)) | sK2(X11,k1_tarski(X12)) = X11 | k1_tarski(X12) = k1_tarski(X11)).
% 0.21/0.55  
% 0.21/0.55  cnf(u56,negated_conjecture,
% 0.21/0.55      k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u76,axiom,
% 0.21/0.55      sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2))) | sK2(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u93,axiom,
% 0.21/0.55      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.21/0.55  
% 0.21/0.55  cnf(u48,axiom,
% 0.21/0.55      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u48,axiom,
% 0.21/0.55      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u93,axiom,
% 0.21/0.55      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.21/0.55  
% 0.21/0.55  cnf(u93,axiom,
% 0.21/0.55      sK2(X7,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = sK2(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X7) = k1_tarski(X6) | k1_tarski(X5) = k1_tarski(X6)).
% 0.21/0.55  
% 0.21/0.55  cnf(u88,axiom,
% 0.21/0.55      k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5))) | sK2(X4,k1_tarski(X5)) = X4 | k1_tarski(X5) = k1_tarski(X4)).
% 0.21/0.55  
% 0.21/0.55  cnf(u33,axiom,
% 0.21/0.55      k1_tarski(X0) = k2_tarski(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u156,axiom,
% 0.21/0.55      sK2(X2,k1_tarski(X1)) != X0 | sK2(X2,k1_tarski(X1)) = X2 | sK2(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u154,axiom,
% 0.21/0.55      sK2(X2,k1_tarski(X1)) != X0 | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1)) | sK2(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u65,axiom,
% 0.21/0.55      X0 != X1 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u71,axiom,
% 0.21/0.55      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X0).
% 0.21/0.55  
% 0.21/0.55  % (31407)# SZS output end Saturation.
% 0.21/0.55  % (31407)------------------------------
% 0.21/0.55  % (31407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31407)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (31407)Memory used [KB]: 1791
% 0.21/0.55  % (31407)Time elapsed: 0.107 s
% 0.21/0.55  % (31407)------------------------------
% 0.21/0.55  % (31407)------------------------------
% 0.21/0.55  % (31399)Success in time 0.183 s
%------------------------------------------------------------------------------
