%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:34 EST 2020

% Result     : CounterSatisfiable 2.02s
% Output     : Saturation 2.02s
% Verified   : 
% Statistics : Number of clauses        :  101 ( 101 expanded)
%              Number of leaves         :  101 ( 101 expanded)
%              Depth                    :    0
%              Number of atoms          :  115 ( 115 expanded)
%              Number of equality atoms :   85 (  85 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u236,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3)) )).

cnf(u551,axiom,
    ( m1_subset_1(k4_xboole_0(X14,X15),k1_zfmisc_1(X14)) )).

cnf(u162,axiom,
    ( m1_subset_1(k3_xboole_0(X8,X7),k1_zfmisc_1(X7)) )).

cnf(u64,axiom,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) )).

cnf(u317,axiom,
    ( m1_subset_1(X24,k1_zfmisc_1(k2_xboole_0(X25,X24))) )).

cnf(u262,axiom,
    ( m1_subset_1(X7,k1_zfmisc_1(k2_xboole_0(X7,X8))) )).

cnf(u55,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u50,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u61,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u316,axiom,
    ( r1_tarski(X22,k2_xboole_0(X23,X22)) )).

cnf(u254,axiom,
    ( r1_tarski(X7,k2_xboole_0(X7,X8)) )).

cnf(u159,axiom,
    ( r1_tarski(k3_xboole_0(X2,X1),X1) )).

cnf(u233,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u519,axiom,
    ( r1_tarski(k4_xboole_0(X14,X15),X14) )).

cnf(u39,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) )).

cnf(u53,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u472,axiom,
    ( ~ r1_tarski(k2_xboole_0(X14,X13),X13)
    | k2_xboole_0(X14,X13) = X13 )).

cnf(u471,axiom,
    ( ~ r1_tarski(k2_xboole_0(X11,X12),X11)
    | k2_xboole_0(X11,X12) = X11 )).

cnf(u82,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u37,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u721,axiom,
    ( ~ r1_tarski(X31,k4_xboole_0(X31,X32))
    | k4_xboole_0(X31,X32) = X31 )).

cnf(u164,axiom,
    ( ~ r1_tarski(X11,k3_xboole_0(X12,X11))
    | k3_xboole_0(X12,X11) = X11 )).

cnf(u81,axiom,
    ( ~ r1_tarski(X1,k3_xboole_0(X1,X2))
    | k3_xboole_0(X1,X2) = X1 )).

cnf(u51,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u49,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u480,axiom,
    ( k7_subset_1(k2_xboole_0(X18,X19),X18,X20) = k4_xboole_0(X18,X20) )).

cnf(u228,axiom,
    ( k7_subset_1(X4,k3_xboole_0(X5,X4),X6) = k4_xboole_0(k3_xboole_0(X5,X4),X6) )).

cnf(u85,axiom,
    ( k7_subset_1(X0,k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(X0,X1),X2) )).

cnf(u83,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u34,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u41,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u146,axiom,
    ( k2_xboole_0(k1_xboole_0,X11) = X11 )).

cnf(u718,axiom,
    ( k2_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = X25 )).

cnf(u728,axiom,
    ( k2_xboole_0(k4_xboole_0(X46,X47),X46) = X46 )).

cnf(u390,axiom,
    ( k2_xboole_0(k3_xboole_0(X11,X12),X12) = X12 )).

cnf(u333,axiom,
    ( k2_xboole_0(k3_xboole_0(X12,X13),X12) = X12 )).

cnf(u161,axiom,
    ( k2_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) = X5 )).

cnf(u46,axiom,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 )).

cnf(u92,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u350,axiom,
    ( k2_xboole_0(X14,k4_xboole_0(X14,X15)) = X14 )).

cnf(u165,axiom,
    ( k2_xboole_0(X13,k3_xboole_0(X14,X13)) = X13 )).

cnf(u99,axiom,
    ( k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 )).

cnf(u329,axiom,
    ( k2_xboole_0(X5,X4) = k2_xboole_0(X4,k2_xboole_0(X5,X4)) )).

cnf(u145,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u380,axiom,
    ( k2_xboole_0(X10,X9) = k2_xboole_0(X9,k4_xboole_0(k2_xboole_0(X10,X9),X9)) )).

cnf(u379,axiom,
    ( k2_xboole_0(X7,X8) = k2_xboole_0(X7,k4_xboole_0(k2_xboole_0(X7,X8),X7)) )).

cnf(u149,axiom,
    ( k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1) )).

cnf(u102,axiom,
    ( k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) )).

cnf(u70,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) )).

cnf(u1272,axiom,
    ( k2_xboole_0(X14,X15) = k5_xboole_0(X15,k4_xboole_0(k2_xboole_0(X14,X15),X15)) )).

cnf(u1268,axiom,
    ( k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(k2_xboole_0(X6,X7),X6)) )).

cnf(u44,axiom,
    ( k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

cnf(u65,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) )).

cnf(u42,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

cnf(u110,axiom,
    ( k2_xboole_0(X2,X2) = X2 )).

cnf(u245,axiom,
    ( k1_xboole_0 = k7_subset_1(X6,k1_xboole_0,X7) )).

cnf(u33,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u79,axiom,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u93,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u73,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) )).

cnf(u269,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),X10) )).

cnf(u163,axiom,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X10,X9),X9) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) )).

cnf(u91,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u150,axiom,
    ( k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) )).

cnf(u40,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u157,axiom,
    ( k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )).

cnf(u59,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u1223,axiom,
    ( k5_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1 )).

cnf(u717,axiom,
    ( k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k5_xboole_0(X23,k4_xboole_0(X23,X24)) )).

cnf(u370,axiom,
    ( k4_xboole_0(k2_xboole_0(X10,X9),X9) = k5_xboole_0(k2_xboole_0(X10,X9),X9) )).

cnf(u369,axiom,
    ( k4_xboole_0(k2_xboole_0(X7,X8),X7) = k5_xboole_0(k2_xboole_0(X7,X8),X7) )).

cnf(u493,axiom,
    ( k5_xboole_0(k1_xboole_0,X2) = X2 )).

cnf(u1275,axiom,
    ( k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = X20 )).

cnf(u785,axiom,
    ( k5_xboole_0(k3_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X10 )).

cnf(u35,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u725,axiom,
    ( k7_subset_1(X39,k4_xboole_0(X39,X40),X41) = k4_xboole_0(k4_xboole_0(X39,X40),X41) )).

cnf(u481,axiom,
    ( k7_subset_1(k2_xboole_0(X22,X21),X21,X23) = k4_xboole_0(X21,X23) )).

cnf(u243,axiom,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 )).

cnf(u84,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u160,axiom,
    ( k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) )).

cnf(u45,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u693,axiom,
    ( k4_xboole_0(X25,k3_xboole_0(X24,X25)) = k4_xboole_0(X25,X24) )).

cnf(u431,axiom,
    ( k4_xboole_0(X23,k3_xboole_0(X23,X24)) = k4_xboole_0(X23,X24) )).

cnf(u703,axiom,
    ( k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) )).

cnf(u305,axiom,
    ( k4_xboole_0(X12,X13) = k3_xboole_0(k4_xboole_0(X12,X13),X12) )).

cnf(u797,axiom,
    ( k3_xboole_0(k2_xboole_0(X20,X19),X19) = X19 )).

cnf(u796,axiom,
    ( k3_xboole_0(k2_xboole_0(X17,X18),X17) = X17 )).

cnf(u67,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

cnf(u43,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u304,axiom,
    ( k3_xboole_0(X11,X10) = k3_xboole_0(k3_xboole_0(X11,X10),X10) )).

cnf(u436,axiom,
    ( k3_xboole_0(X5,X4) = k3_xboole_0(X4,k3_xboole_0(X5,X4)) )).

cnf(u198,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u180,axiom,
    ( k3_xboole_0(X9,X10) = k3_xboole_0(k3_xboole_0(X9,X10),X9) )).

cnf(u106,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

cnf(u177,axiom,
    ( k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3 )).

cnf(u118,axiom,
    ( k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 )).

cnf(u38,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (12531)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (12523)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (12523)Refutation not found, incomplete strategy% (12523)------------------------------
% 0.21/0.54  % (12523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (12524)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (12523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (12523)Memory used [KB]: 1663
% 0.21/0.55  % (12523)Time elapsed: 0.066 s
% 0.21/0.55  % (12523)------------------------------
% 0.21/0.55  % (12523)------------------------------
% 0.21/0.55  % (12517)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (12515)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (12516)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (12532)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (12509)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.57  % (12519)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (12518)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (12519)Refutation not found, incomplete strategy% (12519)------------------------------
% 0.21/0.57  % (12519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (12519)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (12519)Memory used [KB]: 10746
% 0.21/0.57  % (12519)Time elapsed: 0.156 s
% 0.21/0.57  % (12519)------------------------------
% 0.21/0.57  % (12519)------------------------------
% 0.21/0.57  % (12535)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (12512)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.58  % (12535)Refutation not found, incomplete strategy% (12535)------------------------------
% 0.21/0.58  % (12535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12535)Memory used [KB]: 6268
% 0.21/0.58  % (12535)Time elapsed: 0.158 s
% 0.21/0.58  % (12535)------------------------------
% 0.21/0.58  % (12535)------------------------------
% 0.21/0.58  % (12514)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.58  % (12513)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.58  % (12520)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.58  % (12511)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.58  % (12514)Refutation not found, incomplete strategy% (12514)------------------------------
% 0.21/0.58  % (12514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (12514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (12514)Memory used [KB]: 1918
% 0.21/0.58  % (12514)Time elapsed: 0.169 s
% 0.21/0.58  % (12514)------------------------------
% 0.21/0.58  % (12514)------------------------------
% 0.21/0.59  % (12536)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.59  % (12527)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.59  % (12536)Refutation not found, incomplete strategy% (12536)------------------------------
% 0.21/0.59  % (12536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (12536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (12536)Memory used [KB]: 6268
% 0.21/0.59  % (12536)Time elapsed: 0.176 s
% 0.21/0.59  % (12536)------------------------------
% 0.21/0.59  % (12536)------------------------------
% 0.21/0.59  % (12527)Refutation not found, incomplete strategy% (12527)------------------------------
% 0.21/0.59  % (12527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (12527)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (12527)Memory used [KB]: 1663
% 0.21/0.59  % (12527)Time elapsed: 0.180 s
% 0.21/0.59  % (12527)------------------------------
% 0.21/0.59  % (12527)------------------------------
% 1.72/0.59  % (12538)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.72/0.59  % (12538)Refutation not found, incomplete strategy% (12538)------------------------------
% 1.72/0.59  % (12538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (12538)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.59  
% 1.72/0.59  % (12538)Memory used [KB]: 1663
% 1.72/0.59  % (12538)Time elapsed: 0.172 s
% 1.72/0.59  % (12538)------------------------------
% 1.72/0.59  % (12538)------------------------------
% 1.72/0.60  % (12528)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.72/0.60  % (12537)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.72/0.60  % (12530)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.72/0.60  % (12534)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.72/0.60  % (12529)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.72/0.60  % (12522)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.72/0.60  % (12520)Refutation not found, incomplete strategy% (12520)------------------------------
% 1.72/0.60  % (12520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (12520)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.60  
% 1.72/0.60  % (12520)Memory used [KB]: 6268
% 1.72/0.60  % (12520)Time elapsed: 0.174 s
% 1.72/0.60  % (12520)------------------------------
% 1.72/0.60  % (12520)------------------------------
% 1.72/0.61  % (12521)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.72/0.61  % (12526)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.72/0.61  % (12537)Refutation not found, incomplete strategy% (12537)------------------------------
% 1.72/0.61  % (12537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (12526)Refutation not found, incomplete strategy% (12526)------------------------------
% 1.72/0.61  % (12526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (12526)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (12526)Memory used [KB]: 1791
% 1.72/0.61  % (12526)Time elapsed: 0.203 s
% 1.72/0.61  % (12526)------------------------------
% 1.72/0.61  % (12526)------------------------------
% 1.72/0.61  % (12510)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.72/0.61  % (12521)Refutation not found, incomplete strategy% (12521)------------------------------
% 1.72/0.61  % (12521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (12510)Refutation not found, incomplete strategy% (12510)------------------------------
% 1.72/0.61  % (12510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (12510)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (12510)Memory used [KB]: 1663
% 1.72/0.61  % (12510)Time elapsed: 0.189 s
% 1.72/0.61  % (12510)------------------------------
% 1.72/0.61  % (12510)------------------------------
% 2.02/0.62  % (12521)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.62  
% 2.02/0.62  % (12521)Memory used [KB]: 10618
% 2.02/0.62  % (12537)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.62  % (12521)Time elapsed: 0.194 s
% 2.02/0.62  % (12521)------------------------------
% 2.02/0.62  % (12521)------------------------------
% 2.02/0.62  
% 2.02/0.62  % (12537)Memory used [KB]: 10746
% 2.02/0.62  % (12537)Time elapsed: 0.193 s
% 2.02/0.62  % (12537)------------------------------
% 2.02/0.62  % (12537)------------------------------
% 2.02/0.62  % (12533)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.02/0.62  % (12533)Refutation not found, incomplete strategy% (12533)------------------------------
% 2.02/0.62  % (12533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.62  % (12533)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.62  
% 2.02/0.62  % (12533)Memory used [KB]: 10618
% 2.02/0.62  % (12533)Time elapsed: 0.205 s
% 2.02/0.62  % (12533)------------------------------
% 2.02/0.62  % (12533)------------------------------
% 2.02/0.63  % SZS status CounterSatisfiable for theBenchmark
% 2.02/0.63  % (12516)# SZS output start Saturation.
% 2.02/0.63  cnf(u29,negated_conjecture,
% 2.02/0.63      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 2.02/0.63  
% 2.02/0.63  cnf(u236,axiom,
% 2.02/0.63      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))).
% 2.02/0.63  
% 2.02/0.63  cnf(u551,axiom,
% 2.02/0.63      m1_subset_1(k4_xboole_0(X14,X15),k1_zfmisc_1(X14))).
% 2.02/0.63  
% 2.02/0.63  cnf(u162,axiom,
% 2.02/0.63      m1_subset_1(k3_xboole_0(X8,X7),k1_zfmisc_1(X7))).
% 2.02/0.63  
% 2.02/0.63  cnf(u64,axiom,
% 2.02/0.63      m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u317,axiom,
% 2.02/0.63      m1_subset_1(X24,k1_zfmisc_1(k2_xboole_0(X25,X24)))).
% 2.02/0.63  
% 2.02/0.63  cnf(u262,axiom,
% 2.02/0.63      m1_subset_1(X7,k1_zfmisc_1(k2_xboole_0(X7,X8)))).
% 2.02/0.63  
% 2.02/0.63  cnf(u55,axiom,
% 2.02/0.63      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 2.02/0.63  
% 2.02/0.63  cnf(u50,axiom,
% 2.02/0.63      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 2.02/0.63  
% 2.02/0.63  cnf(u52,axiom,
% 2.02/0.63      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 2.02/0.63  
% 2.02/0.63  cnf(u61,negated_conjecture,
% 2.02/0.63      r1_tarski(sK1,u1_struct_0(sK0))).
% 2.02/0.63  
% 2.02/0.63  cnf(u316,axiom,
% 2.02/0.63      r1_tarski(X22,k2_xboole_0(X23,X22))).
% 2.02/0.63  
% 2.02/0.63  cnf(u254,axiom,
% 2.02/0.63      r1_tarski(X7,k2_xboole_0(X7,X8))).
% 2.02/0.63  
% 2.02/0.63  cnf(u159,axiom,
% 2.02/0.63      r1_tarski(k3_xboole_0(X2,X1),X1)).
% 2.02/0.63  
% 2.02/0.63  cnf(u233,axiom,
% 2.02/0.63      r1_tarski(k1_xboole_0,X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u519,axiom,
% 2.02/0.63      r1_tarski(k4_xboole_0(X14,X15),X14)).
% 2.02/0.63  
% 2.02/0.63  cnf(u39,axiom,
% 2.02/0.63      r1_tarski(k3_xboole_0(X0,X1),X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u53,axiom,
% 2.02/0.63      r1_tarski(X1,X1)).
% 2.02/0.63  
% 2.02/0.63  cnf(u472,axiom,
% 2.02/0.63      ~r1_tarski(k2_xboole_0(X14,X13),X13) | k2_xboole_0(X14,X13) = X13).
% 2.02/0.63  
% 2.02/0.63  cnf(u471,axiom,
% 2.02/0.63      ~r1_tarski(k2_xboole_0(X11,X12),X11) | k2_xboole_0(X11,X12) = X11).
% 2.02/0.63  
% 2.02/0.63  cnf(u82,negated_conjecture,
% 2.02/0.63      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u37,axiom,
% 2.02/0.63      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 2.02/0.63  
% 2.02/0.63  cnf(u721,axiom,
% 2.02/0.63      ~r1_tarski(X31,k4_xboole_0(X31,X32)) | k4_xboole_0(X31,X32) = X31).
% 2.02/0.63  
% 2.02/0.63  cnf(u164,axiom,
% 2.02/0.63      ~r1_tarski(X11,k3_xboole_0(X12,X11)) | k3_xboole_0(X12,X11) = X11).
% 2.02/0.63  
% 2.02/0.63  cnf(u81,axiom,
% 2.02/0.63      ~r1_tarski(X1,k3_xboole_0(X1,X2)) | k3_xboole_0(X1,X2) = X1).
% 2.02/0.63  
% 2.02/0.63  cnf(u51,axiom,
% 2.02/0.63      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u49,axiom,
% 2.02/0.63      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 2.02/0.63  
% 2.02/0.63  cnf(u480,axiom,
% 2.02/0.63      k7_subset_1(k2_xboole_0(X18,X19),X18,X20) = k4_xboole_0(X18,X20)).
% 2.02/0.63  
% 2.02/0.63  cnf(u228,axiom,
% 2.02/0.63      k7_subset_1(X4,k3_xboole_0(X5,X4),X6) = k4_xboole_0(k3_xboole_0(X5,X4),X6)).
% 2.02/0.63  
% 2.02/0.63  cnf(u85,axiom,
% 2.02/0.63      k7_subset_1(X0,k3_xboole_0(X0,X1),X2) = k4_xboole_0(k3_xboole_0(X0,X1),X2)).
% 2.02/0.63  
% 2.02/0.63  cnf(u83,negated_conjecture,
% 2.02/0.63      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u34,axiom,
% 2.02/0.63      k2_subset_1(X0) = X0).
% 2.02/0.63  
% 2.02/0.63  cnf(u41,axiom,
% 2.02/0.63      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u146,axiom,
% 2.02/0.63      k2_xboole_0(k1_xboole_0,X11) = X11).
% 2.02/0.63  
% 2.02/0.63  cnf(u718,axiom,
% 2.02/0.63      k2_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = X25).
% 2.02/0.63  
% 2.02/0.63  cnf(u728,axiom,
% 2.02/0.63      k2_xboole_0(k4_xboole_0(X46,X47),X46) = X46).
% 2.02/0.63  
% 2.02/0.63  cnf(u390,axiom,
% 2.02/0.63      k2_xboole_0(k3_xboole_0(X11,X12),X12) = X12).
% 2.02/0.63  
% 2.02/0.63  cnf(u333,axiom,
% 2.02/0.63      k2_xboole_0(k3_xboole_0(X12,X13),X12) = X12).
% 2.02/0.63  
% 2.02/0.63  cnf(u161,axiom,
% 2.02/0.63      k2_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) = X5).
% 2.02/0.63  
% 2.02/0.63  cnf(u46,axiom,
% 2.02/0.63      k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0).
% 2.02/0.63  
% 2.02/0.63  cnf(u92,axiom,
% 2.02/0.63      k2_xboole_0(X0,k1_xboole_0) = X0).
% 2.02/0.63  
% 2.02/0.63  cnf(u350,axiom,
% 2.02/0.63      k2_xboole_0(X14,k4_xboole_0(X14,X15)) = X14).
% 2.02/0.63  
% 2.02/0.63  cnf(u165,axiom,
% 2.02/0.63      k2_xboole_0(X13,k3_xboole_0(X14,X13)) = X13).
% 2.02/0.63  
% 2.02/0.63  cnf(u99,axiom,
% 2.02/0.63      k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2).
% 2.02/0.63  
% 2.02/0.63  cnf(u329,axiom,
% 2.02/0.63      k2_xboole_0(X5,X4) = k2_xboole_0(X4,k2_xboole_0(X5,X4))).
% 2.02/0.63  
% 2.02/0.63  cnf(u145,axiom,
% 2.02/0.63      k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u380,axiom,
% 2.02/0.63      k2_xboole_0(X10,X9) = k2_xboole_0(X9,k4_xboole_0(k2_xboole_0(X10,X9),X9))).
% 2.02/0.63  
% 2.02/0.63  cnf(u379,axiom,
% 2.02/0.63      k2_xboole_0(X7,X8) = k2_xboole_0(X7,k4_xboole_0(k2_xboole_0(X7,X8),X7))).
% 2.02/0.63  
% 2.02/0.63  cnf(u149,axiom,
% 2.02/0.63      k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1)).
% 2.02/0.63  
% 2.02/0.63  cnf(u102,axiom,
% 2.02/0.63      k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)).
% 2.02/0.63  
% 2.02/0.63  cnf(u70,axiom,
% 2.02/0.63      k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u1272,axiom,
% 2.02/0.63      k2_xboole_0(X14,X15) = k5_xboole_0(X15,k4_xboole_0(k2_xboole_0(X14,X15),X15))).
% 2.02/0.63  
% 2.02/0.63  cnf(u1268,axiom,
% 2.02/0.63      k2_xboole_0(X6,X7) = k5_xboole_0(X6,k4_xboole_0(k2_xboole_0(X6,X7),X6))).
% 2.02/0.63  
% 2.02/0.63  cnf(u44,axiom,
% 2.02/0.63      k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))).
% 2.02/0.63  
% 2.02/0.63  cnf(u65,axiom,
% 2.02/0.63      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))).
% 2.02/0.63  
% 2.02/0.63  cnf(u42,axiom,
% 2.02/0.63      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u110,axiom,
% 2.02/0.63      k2_xboole_0(X2,X2) = X2).
% 2.02/0.63  
% 2.02/0.63  cnf(u245,axiom,
% 2.02/0.63      k1_xboole_0 = k7_subset_1(X6,k1_xboole_0,X7)).
% 2.02/0.63  
% 2.02/0.63  cnf(u33,negated_conjecture,
% 2.02/0.63      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u79,axiom,
% 2.02/0.63      k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u93,axiom,
% 2.02/0.63      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u73,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)).
% 2.02/0.63  
% 2.02/0.63  cnf(u269,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),X10)).
% 2.02/0.63  
% 2.02/0.63  cnf(u163,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(k3_xboole_0(X10,X9),X9)).
% 2.02/0.63  
% 2.02/0.63  cnf(u78,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u91,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u150,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))).
% 2.02/0.63  
% 2.02/0.63  cnf(u40,axiom,
% 2.02/0.63      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u157,axiom,
% 2.02/0.63      k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u59,axiom,
% 2.02/0.63      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 2.02/0.63  
% 2.02/0.63  cnf(u1223,axiom,
% 2.02/0.63      k5_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1).
% 2.02/0.63  
% 2.02/0.63  cnf(u717,axiom,
% 2.02/0.63      k4_xboole_0(X23,k4_xboole_0(X23,X24)) = k5_xboole_0(X23,k4_xboole_0(X23,X24))).
% 2.02/0.63  
% 2.02/0.63  cnf(u370,axiom,
% 2.02/0.63      k4_xboole_0(k2_xboole_0(X10,X9),X9) = k5_xboole_0(k2_xboole_0(X10,X9),X9)).
% 2.02/0.63  
% 2.02/0.63  cnf(u369,axiom,
% 2.02/0.63      k4_xboole_0(k2_xboole_0(X7,X8),X7) = k5_xboole_0(k2_xboole_0(X7,X8),X7)).
% 2.02/0.63  
% 2.02/0.63  cnf(u493,axiom,
% 2.02/0.63      k5_xboole_0(k1_xboole_0,X2) = X2).
% 2.02/0.63  
% 2.02/0.63  cnf(u1275,axiom,
% 2.02/0.63      k5_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = X20).
% 2.02/0.63  
% 2.02/0.63  cnf(u785,axiom,
% 2.02/0.63      k5_xboole_0(k3_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X10).
% 2.02/0.63  
% 2.02/0.63  cnf(u35,axiom,
% 2.02/0.63      k5_xboole_0(X0,k1_xboole_0) = X0).
% 2.02/0.63  
% 2.02/0.63  cnf(u725,axiom,
% 2.02/0.63      k7_subset_1(X39,k4_xboole_0(X39,X40),X41) = k4_xboole_0(k4_xboole_0(X39,X40),X41)).
% 2.02/0.63  
% 2.02/0.63  cnf(u481,axiom,
% 2.02/0.63      k7_subset_1(k2_xboole_0(X22,X21),X21,X23) = k4_xboole_0(X21,X23)).
% 2.02/0.63  
% 2.02/0.63  cnf(u243,axiom,
% 2.02/0.63      k4_xboole_0(X1,k1_xboole_0) = X1).
% 2.02/0.63  
% 2.02/0.63  cnf(u84,axiom,
% 2.02/0.63      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 2.02/0.63  
% 2.02/0.63  cnf(u160,axiom,
% 2.02/0.63      k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))).
% 2.02/0.63  
% 2.02/0.63  cnf(u45,axiom,
% 2.02/0.63      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u693,axiom,
% 2.02/0.63      k4_xboole_0(X25,k3_xboole_0(X24,X25)) = k4_xboole_0(X25,X24)).
% 2.02/0.63  
% 2.02/0.63  cnf(u431,axiom,
% 2.02/0.63      k4_xboole_0(X23,k3_xboole_0(X23,X24)) = k4_xboole_0(X23,X24)).
% 2.02/0.63  
% 2.02/0.63  cnf(u703,axiom,
% 2.02/0.63      k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))).
% 2.02/0.63  
% 2.02/0.63  cnf(u305,axiom,
% 2.02/0.63      k4_xboole_0(X12,X13) = k3_xboole_0(k4_xboole_0(X12,X13),X12)).
% 2.02/0.63  
% 2.02/0.63  cnf(u797,axiom,
% 2.02/0.63      k3_xboole_0(k2_xboole_0(X20,X19),X19) = X19).
% 2.02/0.63  
% 2.02/0.63  cnf(u796,axiom,
% 2.02/0.63      k3_xboole_0(k2_xboole_0(X17,X18),X17) = X17).
% 2.02/0.63  
% 2.02/0.63  cnf(u67,axiom,
% 2.02/0.63      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))).
% 2.02/0.63  
% 2.02/0.63  cnf(u43,axiom,
% 2.02/0.63      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 2.02/0.63  
% 2.02/0.63  cnf(u304,axiom,
% 2.02/0.63      k3_xboole_0(X11,X10) = k3_xboole_0(k3_xboole_0(X11,X10),X10)).
% 2.02/0.63  
% 2.02/0.63  cnf(u436,axiom,
% 2.02/0.63      k3_xboole_0(X5,X4) = k3_xboole_0(X4,k3_xboole_0(X5,X4))).
% 2.02/0.63  
% 2.02/0.63  cnf(u198,axiom,
% 2.02/0.63      k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))).
% 2.02/0.63  
% 2.02/0.63  cnf(u180,axiom,
% 2.02/0.63      k3_xboole_0(X9,X10) = k3_xboole_0(k3_xboole_0(X9,X10),X9)).
% 2.02/0.63  
% 2.02/0.63  cnf(u106,axiom,
% 2.02/0.63      k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)).
% 2.02/0.63  
% 2.02/0.63  cnf(u177,axiom,
% 2.02/0.63      k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3).
% 2.02/0.63  
% 2.02/0.63  cnf(u118,axiom,
% 2.02/0.63      k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2).
% 2.02/0.63  
% 2.02/0.63  cnf(u38,axiom,
% 2.02/0.63      k3_xboole_0(X0,X0) = X0).
% 2.02/0.63  
% 2.02/0.63  cnf(u30,negated_conjecture,
% 2.02/0.63      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 2.02/0.63  
% 2.02/0.63  % (12516)# SZS output end Saturation.
% 2.02/0.63  % (12516)------------------------------
% 2.02/0.63  % (12516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (12516)Termination reason: Satisfiable
% 2.02/0.63  
% 2.02/0.63  % (12516)Memory used [KB]: 2430
% 2.02/0.63  % (12516)Time elapsed: 0.202 s
% 2.02/0.63  % (12516)------------------------------
% 2.02/0.63  % (12516)------------------------------
% 2.02/0.63  % (12508)Success in time 0.266 s
%------------------------------------------------------------------------------
