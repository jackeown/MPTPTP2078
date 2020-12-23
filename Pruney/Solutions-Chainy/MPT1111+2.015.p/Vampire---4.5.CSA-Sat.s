%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:11 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   73 (  73 expanded)
%              Number of leaves         :   73 (  73 expanded)
%              Depth                    :    0
%              Number of atoms          :  196 ( 196 expanded)
%              Number of equality atoms :   43 (  43 expanded)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u111,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u42,axiom,
    ( m1_subset_1(sK2(X0,X1),X1)
    | r1_xboole_0(X0,X1) )).

cnf(u40,axiom,
    ( m1_subset_1(sK2(X0,X1),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u146,axiom,
    ( m1_subset_1(sK3(X7,k1_zfmisc_1(X8)),k1_zfmisc_1(X7))
    | r1_tarski(sK3(X7,k1_zfmisc_1(X8)),X8)
    | k1_zfmisc_1(X7) = k1_zfmisc_1(X8) )).

cnf(u87,axiom,
    ( r2_hidden(sK3(X5,X6),X6)
    | m1_subset_1(sK3(X5,X6),k1_zfmisc_1(X5))
    | k1_zfmisc_1(X5) = X6 )).

cnf(u141,axiom,
    ( m1_subset_1(sK3(X7,X8),X8)
    | m1_subset_1(sK3(X7,X8),k1_zfmisc_1(X7))
    | k1_zfmisc_1(X7) = X8 )).

cnf(u51,axiom,
    ( r1_tarski(sK3(X3,X4),X3)
    | m1_subset_1(sK3(X3,X4),X4)
    | k1_zfmisc_1(X3) = X4 )).

cnf(u78,axiom,
    ( m1_subset_1(sK3(X4,X5),X5)
    | r2_hidden(sK3(X4,X5),k1_zfmisc_1(X4))
    | k1_zfmisc_1(X4) = X5 )).

cnf(u141_001,axiom,
    ( m1_subset_1(sK3(X7,X8),X8)
    | m1_subset_1(sK3(X7,X8),k1_zfmisc_1(X7))
    | k1_zfmisc_1(X7) = X8 )).

cnf(u110,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u114,negated_conjecture,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0)) )).

cnf(u52,axiom,
    ( r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X5)
    | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X5) )).

cnf(u84,axiom,
    ( r2_hidden(sK3(X5,k1_zfmisc_1(X6)),k1_zfmisc_1(X5))
    | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X5) )).

cnf(u146_002,axiom,
    ( m1_subset_1(sK3(X7,k1_zfmisc_1(X8)),k1_zfmisc_1(X7))
    | r1_tarski(sK3(X7,k1_zfmisc_1(X8)),X8)
    | k1_zfmisc_1(X7) = k1_zfmisc_1(X8) )).

cnf(u43,axiom,
    ( r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3)
    | r1_xboole_0(X2,k1_zfmisc_1(X3)) )).

cnf(u41,axiom,
    ( r1_tarski(sK2(k1_zfmisc_1(X2),X3),X2)
    | r1_xboole_0(k1_zfmisc_1(X2),X3) )).

cnf(u52_003,axiom,
    ( r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X5)
    | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X5) )).

cnf(u36,axiom,
    ( r1_tarski(sK3(X0,X1),X0)
    | r2_hidden(sK3(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u51_004,axiom,
    ( r1_tarski(sK3(X3,X4),X3)
    | m1_subset_1(sK3(X3,X4),X4)
    | k1_zfmisc_1(X3) = X4 )).

cnf(u37,axiom,
    ( ~ r1_tarski(sK3(X0,X1),X0)
    | ~ r2_hidden(sK3(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u39,axiom,
    ( ~ r1_tarski(X2,X0)
    | r2_hidden(X2,k1_zfmisc_1(X0)) )).

cnf(u31,axiom,
    ( ~ r1_tarski(X1,X0)
    | v1_xboole_0(X1)
    | ~ r1_xboole_0(X1,X0) )).

cnf(u113,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u84_005,axiom,
    ( r2_hidden(sK3(X5,k1_zfmisc_1(X6)),k1_zfmisc_1(X5))
    | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X5) )).

cnf(u49,axiom,
    ( r2_hidden(sK3(X2,X3),X3)
    | r2_hidden(sK3(X2,X3),k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) = X3 )).

cnf(u78_006,axiom,
    ( m1_subset_1(sK3(X4,X5),X5)
    | r2_hidden(sK3(X4,X5),k1_zfmisc_1(X4))
    | k1_zfmisc_1(X4) = X5 )).

cnf(u36_007,axiom,
    ( r1_tarski(sK3(X0,X1),X0)
    | r2_hidden(sK3(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u49_008,axiom,
    ( r2_hidden(sK3(X2,X3),X3)
    | r2_hidden(sK3(X2,X3),k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) = X3 )).

cnf(u87_009,axiom,
    ( r2_hidden(sK3(X5,X6),X6)
    | m1_subset_1(sK3(X5,X6),k1_zfmisc_1(X5))
    | k1_zfmisc_1(X5) = X6 )).

cnf(u30,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | r1_xboole_0(X0,X1) )).

cnf(u29,axiom,
    ( r2_hidden(sK2(X0,X1),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u118,negated_conjecture,
    ( ~ r2_hidden(sK3(X0,u1_struct_0(sK0)),k1_xboole_0)
    | r1_tarski(sK3(X0,u1_struct_0(sK0)),X0)
    | k1_zfmisc_1(X0) = u1_struct_0(sK0) )).

cnf(u137,negated_conjecture,
    ( ~ r2_hidden(sK3(X2,u1_struct_0(sK0)),k1_xboole_0)
    | u1_struct_0(sK0) = k1_zfmisc_1(X2)
    | r2_hidden(sK3(X2,u1_struct_0(sK0)),k1_zfmisc_1(X2)) )).

cnf(u185,negated_conjecture,
    ( ~ r2_hidden(sK3(X2,u1_struct_0(sK0)),k1_xboole_0)
    | u1_struct_0(sK0) = k1_zfmisc_1(X2)
    | m1_subset_1(sK3(X2,u1_struct_0(sK0)),k1_zfmisc_1(X2)) )).

cnf(u162,axiom,
    ( ~ r2_hidden(sK3(X6,k1_zfmisc_1(X7)),X8)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X7)
    | r1_tarski(sK3(X6,k1_zfmisc_1(X7)),X7)
    | ~ r1_xboole_0(k1_zfmisc_1(X6),X8) )).

cnf(u50,axiom,
    ( ~ r2_hidden(sK3(X0,X1),X2)
    | k1_zfmisc_1(X0) = X1
    | r1_tarski(sK3(X0,X1),X0)
    | ~ r1_xboole_0(X1,X2) )).

cnf(u82,axiom,
    ( ~ r2_hidden(sK3(X0,X1),X2)
    | k1_zfmisc_1(X0) = X1
    | r2_hidden(sK3(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_xboole_0(X1,X2) )).

cnf(u86,axiom,
    ( ~ r2_hidden(sK3(X2,X3),X4)
    | k1_zfmisc_1(X2) = X3
    | r2_hidden(sK3(X2,X3),X3)
    | ~ r1_xboole_0(k1_zfmisc_1(X2),X4) )).

cnf(u140,axiom,
    ( ~ r2_hidden(sK3(X4,X5),X6)
    | k1_zfmisc_1(X4) = X5
    | m1_subset_1(sK3(X4,X5),X5)
    | ~ r1_xboole_0(k1_zfmisc_1(X4),X6) )).

cnf(u144,axiom,
    ( ~ r2_hidden(sK3(X2,X3),X4)
    | k1_zfmisc_1(X2) = X3
    | m1_subset_1(sK3(X2,X3),k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,X4) )).

cnf(u117,negated_conjecture,
    ( ~ r2_hidden(sK2(X0,u1_struct_0(sK0)),k1_xboole_0)
    | r1_xboole_0(X0,u1_struct_0(sK0)) )).

cnf(u116,negated_conjecture,
    ( ~ r2_hidden(sK2(u1_struct_0(sK0),X0),k1_xboole_0)
    | r1_xboole_0(u1_struct_0(sK0),X0) )).

cnf(u46,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X2)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,X1) )).

cnf(u47,axiom,
    ( ~ r2_hidden(sK2(X3,X4),X5)
    | ~ r1_xboole_0(X4,X5)
    | r1_xboole_0(X3,X4) )).

cnf(u38,axiom,
    ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
    | r1_tarski(X2,X0) )).

cnf(u33,axiom,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) )).

cnf(u28,axiom,
    ( ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1)
    | ~ r1_xboole_0(X0,X1) )).

cnf(u120,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,u1_struct_0(sK0)) )).

cnf(u119,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) )).

cnf(u100,axiom,
    ( ~ r1_xboole_0(sK3(X1,k1_zfmisc_1(X2)),X2)
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | v1_xboole_0(sK3(X1,k1_zfmisc_1(X2)))
    | r1_tarski(sK3(X1,k1_zfmisc_1(X2)),X1) )).

cnf(u165,axiom,
    ( ~ r1_xboole_0(sK3(X1,k1_zfmisc_1(X2)),X2)
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | v1_xboole_0(sK3(X1,k1_zfmisc_1(X2)))
    | r2_hidden(sK3(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1)) )).

cnf(u214,axiom,
    ( ~ r1_xboole_0(sK3(X1,k1_zfmisc_1(X2)),X2)
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)
    | v1_xboole_0(sK3(X1,k1_zfmisc_1(X2)))
    | m1_subset_1(sK3(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1)) )).

cnf(u97,axiom,
    ( ~ r1_xboole_0(sK3(X2,k1_zfmisc_1(X3)),X2)
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)
    | v1_xboole_0(sK3(X2,k1_zfmisc_1(X3)))
    | r1_tarski(sK3(X2,k1_zfmisc_1(X3)),X3) )).

cnf(u48,axiom,
    ( ~ r1_xboole_0(sK3(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1
    | v1_xboole_0(sK3(X0,X1))
    | r2_hidden(sK3(X0,X1),X1) )).

cnf(u77,axiom,
    ( ~ r1_xboole_0(sK3(X2,X3),X2)
    | k1_zfmisc_1(X2) = X3
    | v1_xboole_0(sK3(X2,X3))
    | m1_subset_1(sK3(X2,X3),X3) )).

cnf(u66,axiom,
    ( ~ r1_xboole_0(sK2(X0,k1_zfmisc_1(X1)),X1)
    | v1_xboole_0(sK2(X0,k1_zfmisc_1(X1)))
    | r1_xboole_0(X0,k1_zfmisc_1(X1)) )).

cnf(u62,axiom,
    ( ~ r1_xboole_0(sK2(k1_zfmisc_1(X0),X1),X0)
    | v1_xboole_0(sK2(k1_zfmisc_1(X0),X1))
    | r1_xboole_0(k1_zfmisc_1(X0),X1) )).

cnf(u176,axiom,
    ( ~ r1_xboole_0(k1_zfmisc_1(X8),k1_zfmisc_1(X8))
    | r2_hidden(sK3(X8,X9),X9)
    | k1_zfmisc_1(X8) = X9 )).

cnf(u181,axiom,
    ( ~ r1_xboole_0(k1_zfmisc_1(X6),k1_zfmisc_1(X6))
    | k1_zfmisc_1(X6) = X7
    | m1_subset_1(sK3(X6,X7),X7) )).

cnf(u227,axiom,
    ( ~ r1_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X0))
    | r1_tarski(sK3(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u115,negated_conjecture,
    ( ~ r1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),X0)
    | ~ r2_hidden(k1_xboole_0,X0) )).

cnf(u75,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u71,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | r1_xboole_0(X0,X1) )).

cnf(u74,axiom,
    ( ~ r1_xboole_0(X2,X2)
    | r1_xboole_0(X3,X2) )).

cnf(u93,axiom,
    ( ~ r1_xboole_0(X3,X3)
    | r1_tarski(sK3(X2,X3),X2)
    | k1_zfmisc_1(X2) = X3 )).

cnf(u95,axiom,
    ( ~ r1_xboole_0(X1,X1)
    | k1_zfmisc_1(X0) = X1
    | r2_hidden(sK3(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u211,axiom,
    ( ~ r1_xboole_0(X1,X1)
    | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) = X1 )).

cnf(u121,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u27,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u26,axiom,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) )).

cnf(u109,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u112,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (9194)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (9204)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (9197)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (9204)Refutation not found, incomplete strategy% (9204)------------------------------
% 0.20/0.48  % (9204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9204)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (9204)Memory used [KB]: 10618
% 0.20/0.48  % (9204)Time elapsed: 0.007 s
% 0.20/0.48  % (9204)------------------------------
% 0.20/0.48  % (9204)------------------------------
% 0.20/0.48  % (9195)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (9190)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (9190)Refutation not found, incomplete strategy% (9190)------------------------------
% 0.20/0.49  % (9190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (9190)Memory used [KB]: 10618
% 0.20/0.49  % (9190)Time elapsed: 0.071 s
% 0.20/0.49  % (9190)------------------------------
% 0.20/0.49  % (9190)------------------------------
% 0.20/0.49  % (9192)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (9191)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (9193)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (9198)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (9189)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (9189)Refutation not found, incomplete strategy% (9189)------------------------------
% 0.20/0.50  % (9189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9189)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9189)Memory used [KB]: 6140
% 0.20/0.50  % (9189)Time elapsed: 0.087 s
% 0.20/0.50  % (9189)------------------------------
% 0.20/0.50  % (9189)------------------------------
% 0.20/0.50  % (9207)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % (9205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (9201)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (9196)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.51  % (9211)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (9200)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (9211)Refutation not found, incomplete strategy% (9211)------------------------------
% 0.20/0.51  % (9211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9211)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9211)Memory used [KB]: 10618
% 0.20/0.51  % (9211)Time elapsed: 0.095 s
% 0.20/0.51  % (9211)------------------------------
% 0.20/0.51  % (9211)------------------------------
% 0.20/0.51  % (9200)Refutation not found, incomplete strategy% (9200)------------------------------
% 0.20/0.51  % (9200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9200)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9200)Memory used [KB]: 10618
% 0.20/0.51  % (9200)Time elapsed: 0.095 s
% 0.20/0.51  % (9200)------------------------------
% 0.20/0.51  % (9200)------------------------------
% 0.20/0.51  % (9199)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (9192)Refutation not found, incomplete strategy% (9192)------------------------------
% 0.20/0.51  % (9192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9192)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9192)Memory used [KB]: 10618
% 0.20/0.51  % (9192)Time elapsed: 0.085 s
% 0.20/0.51  % (9192)------------------------------
% 0.20/0.51  % (9192)------------------------------
% 0.20/0.51  % (9199)Refutation not found, incomplete strategy% (9199)------------------------------
% 0.20/0.51  % (9199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9191)Refutation not found, incomplete strategy% (9191)------------------------------
% 0.20/0.51  % (9191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9191)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9191)Memory used [KB]: 10618
% 0.20/0.51  % (9191)Time elapsed: 0.085 s
% 0.20/0.51  % (9191)------------------------------
% 0.20/0.51  % (9191)------------------------------
% 0.20/0.51  % (9205)Refutation not found, incomplete strategy% (9205)------------------------------
% 0.20/0.51  % (9205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9199)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9199)Memory used [KB]: 6012
% 0.20/0.51  % (9208)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (9199)Time elapsed: 0.097 s
% 0.20/0.51  % (9199)------------------------------
% 0.20/0.51  % (9199)------------------------------
% 0.20/0.51  % (9202)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (9205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9205)Memory used [KB]: 6140
% 0.20/0.51  % (9205)Time elapsed: 0.098 s
% 0.20/0.51  % (9205)------------------------------
% 0.20/0.51  % (9205)------------------------------
% 0.20/0.51  % (9202)Refutation not found, incomplete strategy% (9202)------------------------------
% 0.20/0.51  % (9202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9202)Memory used [KB]: 1663
% 0.20/0.51  % (9202)Time elapsed: 0.108 s
% 0.20/0.51  % (9202)------------------------------
% 0.20/0.51  % (9202)------------------------------
% 0.20/0.51  % (9210)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (9207)# SZS output start Saturation.
% 0.20/0.51  cnf(u111,negated_conjecture,
% 0.20/0.51      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u42,axiom,
% 0.20/0.51      m1_subset_1(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u40,axiom,
% 0.20/0.51      m1_subset_1(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u146,axiom,
% 0.20/0.51      m1_subset_1(sK3(X7,k1_zfmisc_1(X8)),k1_zfmisc_1(X7)) | r1_tarski(sK3(X7,k1_zfmisc_1(X8)),X8) | k1_zfmisc_1(X7) = k1_zfmisc_1(X8)).
% 0.20/0.51  
% 0.20/0.51  cnf(u87,axiom,
% 0.20/0.51      r2_hidden(sK3(X5,X6),X6) | m1_subset_1(sK3(X5,X6),k1_zfmisc_1(X5)) | k1_zfmisc_1(X5) = X6).
% 0.20/0.51  
% 0.20/0.51  cnf(u141,axiom,
% 0.20/0.51      m1_subset_1(sK3(X7,X8),X8) | m1_subset_1(sK3(X7,X8),k1_zfmisc_1(X7)) | k1_zfmisc_1(X7) = X8).
% 0.20/0.51  
% 0.20/0.51  cnf(u51,axiom,
% 0.20/0.51      r1_tarski(sK3(X3,X4),X3) | m1_subset_1(sK3(X3,X4),X4) | k1_zfmisc_1(X3) = X4).
% 0.20/0.51  
% 0.20/0.51  cnf(u78,axiom,
% 0.20/0.51      m1_subset_1(sK3(X4,X5),X5) | r2_hidden(sK3(X4,X5),k1_zfmisc_1(X4)) | k1_zfmisc_1(X4) = X5).
% 0.20/0.51  
% 0.20/0.51  cnf(u141,axiom,
% 0.20/0.51      m1_subset_1(sK3(X7,X8),X8) | m1_subset_1(sK3(X7,X8),k1_zfmisc_1(X7)) | k1_zfmisc_1(X7) = X8).
% 0.20/0.51  
% 0.20/0.51  cnf(u110,negated_conjecture,
% 0.20/0.51      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u32,axiom,
% 0.20/0.51      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u114,negated_conjecture,
% 0.20/0.51      r1_tarski(k1_xboole_0,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,axiom,
% 0.20/0.51      r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X5) | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6) | k1_zfmisc_1(X6) = k1_zfmisc_1(X5)).
% 0.20/0.51  
% 0.20/0.51  cnf(u84,axiom,
% 0.20/0.51      r2_hidden(sK3(X5,k1_zfmisc_1(X6)),k1_zfmisc_1(X5)) | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6) | k1_zfmisc_1(X6) = k1_zfmisc_1(X5)).
% 0.20/0.51  
% 0.20/0.51  cnf(u146,axiom,
% 0.20/0.51      m1_subset_1(sK3(X7,k1_zfmisc_1(X8)),k1_zfmisc_1(X7)) | r1_tarski(sK3(X7,k1_zfmisc_1(X8)),X8) | k1_zfmisc_1(X7) = k1_zfmisc_1(X8)).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) | r1_xboole_0(X2,k1_zfmisc_1(X3))).
% 0.20/0.51  
% 0.20/0.51  cnf(u41,axiom,
% 0.20/0.51      r1_tarski(sK2(k1_zfmisc_1(X2),X3),X2) | r1_xboole_0(k1_zfmisc_1(X2),X3)).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,axiom,
% 0.20/0.51      r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X5) | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6) | k1_zfmisc_1(X6) = k1_zfmisc_1(X5)).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,axiom,
% 0.20/0.51      r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u51,axiom,
% 0.20/0.51      r1_tarski(sK3(X3,X4),X3) | m1_subset_1(sK3(X3,X4),X4) | k1_zfmisc_1(X3) = X4).
% 0.20/0.51  
% 0.20/0.51  cnf(u37,axiom,
% 0.20/0.51      ~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u39,axiom,
% 0.20/0.51      ~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,axiom,
% 0.20/0.51      ~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u113,negated_conjecture,
% 0.20/0.51      r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u84,axiom,
% 0.20/0.51      r2_hidden(sK3(X5,k1_zfmisc_1(X6)),k1_zfmisc_1(X5)) | r1_tarski(sK3(X5,k1_zfmisc_1(X6)),X6) | k1_zfmisc_1(X6) = k1_zfmisc_1(X5)).
% 0.20/0.51  
% 0.20/0.51  cnf(u49,axiom,
% 0.20/0.51      r2_hidden(sK3(X2,X3),X3) | r2_hidden(sK3(X2,X3),k1_zfmisc_1(X2)) | k1_zfmisc_1(X2) = X3).
% 0.20/0.51  
% 0.20/0.51  cnf(u78,axiom,
% 0.20/0.51      m1_subset_1(sK3(X4,X5),X5) | r2_hidden(sK3(X4,X5),k1_zfmisc_1(X4)) | k1_zfmisc_1(X4) = X5).
% 0.20/0.51  
% 0.20/0.51  cnf(u36,axiom,
% 0.20/0.51      r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 0.20/0.51  
% 0.20/0.51  cnf(u49,axiom,
% 0.20/0.51      r2_hidden(sK3(X2,X3),X3) | r2_hidden(sK3(X2,X3),k1_zfmisc_1(X2)) | k1_zfmisc_1(X2) = X3).
% 0.20/0.51  
% 0.20/0.51  cnf(u87,axiom,
% 0.20/0.51      r2_hidden(sK3(X5,X6),X6) | m1_subset_1(sK3(X5,X6),k1_zfmisc_1(X5)) | k1_zfmisc_1(X5) = X6).
% 0.20/0.51  
% 0.20/0.51  cnf(u30,axiom,
% 0.20/0.51      r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u29,axiom,
% 0.20/0.51      r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u118,negated_conjecture,
% 0.20/0.51      ~r2_hidden(sK3(X0,u1_struct_0(sK0)),k1_xboole_0) | r1_tarski(sK3(X0,u1_struct_0(sK0)),X0) | k1_zfmisc_1(X0) = u1_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u137,negated_conjecture,
% 0.20/0.51      ~r2_hidden(sK3(X2,u1_struct_0(sK0)),k1_xboole_0) | u1_struct_0(sK0) = k1_zfmisc_1(X2) | r2_hidden(sK3(X2,u1_struct_0(sK0)),k1_zfmisc_1(X2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u185,negated_conjecture,
% 0.20/0.51      ~r2_hidden(sK3(X2,u1_struct_0(sK0)),k1_xboole_0) | u1_struct_0(sK0) = k1_zfmisc_1(X2) | m1_subset_1(sK3(X2,u1_struct_0(sK0)),k1_zfmisc_1(X2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u162,axiom,
% 0.20/0.51      ~r2_hidden(sK3(X6,k1_zfmisc_1(X7)),X8) | k1_zfmisc_1(X6) = k1_zfmisc_1(X7) | r1_tarski(sK3(X6,k1_zfmisc_1(X7)),X7) | ~r1_xboole_0(k1_zfmisc_1(X6),X8)).
% 0.20/0.51  
% 0.20/0.51  cnf(u50,axiom,
% 0.20/0.51      ~r2_hidden(sK3(X0,X1),X2) | k1_zfmisc_1(X0) = X1 | r1_tarski(sK3(X0,X1),X0) | ~r1_xboole_0(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u82,axiom,
% 0.20/0.51      ~r2_hidden(sK3(X0,X1),X2) | k1_zfmisc_1(X0) = X1 | r2_hidden(sK3(X0,X1),k1_zfmisc_1(X0)) | ~r1_xboole_0(X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u86,axiom,
% 0.20/0.51      ~r2_hidden(sK3(X2,X3),X4) | k1_zfmisc_1(X2) = X3 | r2_hidden(sK3(X2,X3),X3) | ~r1_xboole_0(k1_zfmisc_1(X2),X4)).
% 0.20/0.51  
% 0.20/0.51  cnf(u140,axiom,
% 0.20/0.51      ~r2_hidden(sK3(X4,X5),X6) | k1_zfmisc_1(X4) = X5 | m1_subset_1(sK3(X4,X5),X5) | ~r1_xboole_0(k1_zfmisc_1(X4),X6)).
% 0.20/0.51  
% 0.20/0.51  cnf(u144,axiom,
% 0.20/0.51      ~r2_hidden(sK3(X2,X3),X4) | k1_zfmisc_1(X2) = X3 | m1_subset_1(sK3(X2,X3),k1_zfmisc_1(X2)) | ~r1_xboole_0(X3,X4)).
% 0.20/0.51  
% 0.20/0.51  cnf(u117,negated_conjecture,
% 0.20/0.51      ~r2_hidden(sK2(X0,u1_struct_0(sK0)),k1_xboole_0) | r1_xboole_0(X0,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u116,negated_conjecture,
% 0.20/0.51      ~r2_hidden(sK2(u1_struct_0(sK0),X0),k1_xboole_0) | r1_xboole_0(u1_struct_0(sK0),X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u46,axiom,
% 0.20/0.51      ~r2_hidden(sK2(X0,X1),X2) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u47,axiom,
% 0.20/0.51      ~r2_hidden(sK2(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)).
% 0.20/0.51  
% 0.20/0.51  cnf(u38,axiom,
% 0.20/0.51      ~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u33,axiom,
% 0.20/0.51      ~r2_hidden(X0,X1) | m1_subset_1(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,axiom,
% 0.20/0.51      ~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u120,negated_conjecture,
% 0.20/0.51      r1_xboole_0(k1_xboole_0,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u119,negated_conjecture,
% 0.20/0.51      r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u100,axiom,
% 0.20/0.51      ~r1_xboole_0(sK3(X1,k1_zfmisc_1(X2)),X2) | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) | v1_xboole_0(sK3(X1,k1_zfmisc_1(X2))) | r1_tarski(sK3(X1,k1_zfmisc_1(X2)),X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u165,axiom,
% 0.20/0.51      ~r1_xboole_0(sK3(X1,k1_zfmisc_1(X2)),X2) | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) | v1_xboole_0(sK3(X1,k1_zfmisc_1(X2))) | r2_hidden(sK3(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u214,axiom,
% 0.20/0.51      ~r1_xboole_0(sK3(X1,k1_zfmisc_1(X2)),X2) | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) | v1_xboole_0(sK3(X1,k1_zfmisc_1(X2))) | m1_subset_1(sK3(X1,k1_zfmisc_1(X2)),k1_zfmisc_1(X1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u97,axiom,
% 0.20/0.51      ~r1_xboole_0(sK3(X2,k1_zfmisc_1(X3)),X2) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) | v1_xboole_0(sK3(X2,k1_zfmisc_1(X3))) | r1_tarski(sK3(X2,k1_zfmisc_1(X3)),X3)).
% 0.20/0.51  
% 0.20/0.51  cnf(u48,axiom,
% 0.20/0.51      ~r1_xboole_0(sK3(X0,X1),X0) | k1_zfmisc_1(X0) = X1 | v1_xboole_0(sK3(X0,X1)) | r2_hidden(sK3(X0,X1),X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u77,axiom,
% 0.20/0.51      ~r1_xboole_0(sK3(X2,X3),X2) | k1_zfmisc_1(X2) = X3 | v1_xboole_0(sK3(X2,X3)) | m1_subset_1(sK3(X2,X3),X3)).
% 0.20/0.51  
% 0.20/0.52  cnf(u66,axiom,
% 0.20/0.52      ~r1_xboole_0(sK2(X0,k1_zfmisc_1(X1)),X1) | v1_xboole_0(sK2(X0,k1_zfmisc_1(X1))) | r1_xboole_0(X0,k1_zfmisc_1(X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u62,axiom,
% 0.20/0.52      ~r1_xboole_0(sK2(k1_zfmisc_1(X0),X1),X0) | v1_xboole_0(sK2(k1_zfmisc_1(X0),X1)) | r1_xboole_0(k1_zfmisc_1(X0),X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u176,axiom,
% 0.20/0.52      ~r1_xboole_0(k1_zfmisc_1(X8),k1_zfmisc_1(X8)) | r2_hidden(sK3(X8,X9),X9) | k1_zfmisc_1(X8) = X9).
% 0.20/0.52  
% 0.20/0.52  cnf(u181,axiom,
% 0.20/0.52      ~r1_xboole_0(k1_zfmisc_1(X6),k1_zfmisc_1(X6)) | k1_zfmisc_1(X6) = X7 | m1_subset_1(sK3(X6,X7),X7)).
% 0.20/0.52  
% 0.20/0.52  cnf(u227,axiom,
% 0.20/0.52      ~r1_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) | r1_tarski(sK3(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u115,negated_conjecture,
% 0.20/0.52      ~r1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)),X0) | ~r2_hidden(k1_xboole_0,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u75,axiom,
% 0.20/0.52      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u71,axiom,
% 0.20/0.52      ~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u74,axiom,
% 0.20/0.52      ~r1_xboole_0(X2,X2) | r1_xboole_0(X3,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u93,axiom,
% 0.20/0.52      ~r1_xboole_0(X3,X3) | r1_tarski(sK3(X2,X3),X2) | k1_zfmisc_1(X2) = X3).
% 0.20/0.52  
% 0.20/0.52  cnf(u95,axiom,
% 0.20/0.52      ~r1_xboole_0(X1,X1) | k1_zfmisc_1(X0) = X1 | r2_hidden(sK3(X0,X1),k1_zfmisc_1(X0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u211,axiom,
% 0.20/0.52      ~r1_xboole_0(X1,X1) | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(X0)) | k1_zfmisc_1(X0) = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u121,negated_conjecture,
% 0.20/0.52      v1_xboole_0(k1_xboole_0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u27,axiom,
% 0.20/0.52      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u26,axiom,
% 0.20/0.52      ~v1_xboole_0(k1_zfmisc_1(X0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u109,negated_conjecture,
% 0.20/0.52      k1_xboole_0 = sK1).
% 0.20/0.52  
% 0.20/0.52  cnf(u112,negated_conjecture,
% 0.20/0.52      k1_xboole_0 != k1_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  % (9207)# SZS output end Saturation.
% 0.20/0.52  % (9207)------------------------------
% 0.20/0.52  % (9207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9207)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (9207)Memory used [KB]: 1663
% 0.20/0.52  % (9207)Time elapsed: 0.110 s
% 0.20/0.52  % (9207)------------------------------
% 0.20/0.52  % (9207)------------------------------
% 0.20/0.52  % (9184)Success in time 0.16 s
%------------------------------------------------------------------------------
