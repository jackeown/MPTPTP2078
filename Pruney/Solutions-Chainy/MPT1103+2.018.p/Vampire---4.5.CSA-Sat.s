%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:36 EST 2020

% Result     : CounterSatisfiable 1.38s
% Output     : Saturation 1.38s
% Verified   : 
% Statistics : Number of clauses        :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :   66 (  66 expanded)
%              Number of equality atoms :   51 (  51 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u72,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u39,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u36,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u233,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) )).

cnf(u241,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1) )).

cnf(u243,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4) )).

cnf(u242,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0) )).

cnf(u237,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X1,k1_xboole_0) = X1 )).

cnf(u235,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,X3,X4) )).

cnf(u87,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u86,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u115,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) )).

cnf(u62,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0)) )).

cnf(u84,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) )).

cnf(u90,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u347,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u176,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) )).

cnf(u156,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u162,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u85,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2) )).

cnf(u34,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u393,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u343,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u339,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u342,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u250,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u248,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u381,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) )).

cnf(u239,axiom,
    ( k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u238,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u356,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u77,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u80,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u344,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u346,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0)))) )).

cnf(u161,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u152,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) )).

cnf(u89,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u187,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k5_xboole_0(X3,k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3)) )).

cnf(u209,axiom,
    ( k5_xboole_0(X7,k7_subset_1(X6,X6,X7)) = k5_xboole_0(X6,k7_subset_1(k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),X6)) )).

cnf(u91,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u65,axiom,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 )).

cnf(u113,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u305,axiom,
    ( k4_subset_1(X0,k1_xboole_0,X0) = X0 )).

cnf(u307,axiom,
    ( k4_subset_1(X1,X1,X1) = X1 )).

cnf(u240,axiom,
    ( k4_subset_1(X1,X1,k1_xboole_0) = X1 )).

cnf(u61,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u114,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u42,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u71,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (4942)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (4934)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (4944)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (4957)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (4953)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (4936)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (4942)Refutation not found, incomplete strategy% (4942)------------------------------
% 0.21/0.50  % (4942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4942)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4942)Memory used [KB]: 6524
% 0.21/0.50  % (4942)Time elapsed: 0.095 s
% 0.21/0.50  % (4942)------------------------------
% 0.21/0.50  % (4942)------------------------------
% 0.21/0.51  % (4953)Refutation not found, incomplete strategy% (4953)------------------------------
% 0.21/0.51  % (4953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4953)Memory used [KB]: 1791
% 0.21/0.51  % (4953)Time elapsed: 0.044 s
% 0.21/0.51  % (4953)------------------------------
% 0.21/0.51  % (4953)------------------------------
% 0.21/0.51  % (4949)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (4934)Refutation not found, incomplete strategy% (4934)------------------------------
% 0.21/0.51  % (4934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4934)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4934)Memory used [KB]: 6396
% 0.21/0.51  % (4934)Time elapsed: 0.101 s
% 0.21/0.51  % (4934)------------------------------
% 0.21/0.51  % (4934)------------------------------
% 0.21/0.51  % (4937)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4945)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (4945)Refutation not found, incomplete strategy% (4945)------------------------------
% 0.21/0.51  % (4945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4945)Memory used [KB]: 6140
% 0.21/0.51  % (4945)Time elapsed: 0.001 s
% 0.21/0.51  % (4945)------------------------------
% 0.21/0.51  % (4945)------------------------------
% 1.15/0.52  % (4937)Refutation not found, incomplete strategy% (4937)------------------------------
% 1.15/0.52  % (4937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.52  % (4937)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.52  
% 1.15/0.52  % (4937)Memory used [KB]: 6396
% 1.15/0.52  % (4937)Time elapsed: 0.049 s
% 1.15/0.52  % (4937)------------------------------
% 1.15/0.52  % (4937)------------------------------
% 1.15/0.53  % (4952)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.15/0.53  % (4952)Refutation not found, incomplete strategy% (4952)------------------------------
% 1.15/0.53  % (4952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.53  % (4952)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.53  
% 1.15/0.53  % (4952)Memory used [KB]: 10746
% 1.15/0.53  % (4952)Time elapsed: 0.117 s
% 1.15/0.53  % (4952)------------------------------
% 1.15/0.53  % (4952)------------------------------
% 1.38/0.53  % (4940)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.38/0.53  % (4936)# SZS output start Saturation.
% 1.38/0.53  cnf(u72,axiom,
% 1.38/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u39,axiom,
% 1.38/0.53      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u36,negated_conjecture,
% 1.38/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.38/0.53  
% 1.38/0.53  cnf(u233,negated_conjecture,
% 1.38/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u241,negated_conjecture,
% 1.38/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),sK1)).
% 1.38/0.53  
% 1.38/0.53  cnf(u243,axiom,
% 1.38/0.53      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k3_subset_1(X4,k7_subset_1(X4,X3,X4)) = k4_subset_1(X4,k3_subset_1(X4,X3),X4)).
% 1.38/0.53  
% 1.38/0.53  cnf(u242,axiom,
% 1.38/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X1,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X1),k1_xboole_0)).
% 1.38/0.53  
% 1.38/0.53  cnf(u237,axiom,
% 1.38/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k4_subset_1(X2,X1,k1_xboole_0) = X1).
% 1.38/0.53  
% 1.38/0.53  cnf(u235,axiom,
% 1.38/0.53      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k4_subset_1(X4,X3,X4)).
% 1.38/0.53  
% 1.38/0.53  cnf(u87,axiom,
% 1.38/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.38/0.53  
% 1.38/0.53  cnf(u86,axiom,
% 1.38/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 1.38/0.53  
% 1.38/0.53  cnf(u54,axiom,
% 1.38/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)).
% 1.38/0.53  
% 1.38/0.53  cnf(u53,axiom,
% 1.38/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.38/0.53  
% 1.38/0.53  cnf(u115,axiom,
% 1.38/0.53      k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u62,axiom,
% 1.38/0.53      k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,k1_xboole_0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u84,axiom,
% 1.38/0.53      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))).
% 1.38/0.53  
% 1.38/0.53  cnf(u90,negated_conjecture,
% 1.38/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.38/0.53  
% 1.38/0.53  cnf(u347,negated_conjecture,
% 1.38/0.53      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u176,axiom,
% 1.38/0.53      k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))).
% 1.38/0.53  
% 1.38/0.53  cnf(u156,axiom,
% 1.38/0.53      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 1.38/0.53  
% 1.38/0.53  cnf(u162,axiom,
% 1.38/0.53      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 1.38/0.53  
% 1.38/0.53  cnf(u85,axiom,
% 1.38/0.53      k1_xboole_0 = k7_subset_1(X1,k1_xboole_0,X2)).
% 1.38/0.53  
% 1.38/0.53  cnf(u34,negated_conjecture,
% 1.38/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.38/0.53  
% 1.38/0.53  cnf(u393,negated_conjecture,
% 1.38/0.53      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u343,negated_conjecture,
% 1.38/0.53      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.38/0.53  
% 1.38/0.53  cnf(u339,negated_conjecture,
% 1.38/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 1.38/0.54  
% 1.38/0.54  cnf(u342,negated_conjecture,
% 1.38/0.54      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.38/0.54  
% 1.38/0.54  cnf(u250,negated_conjecture,
% 1.38/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 1.38/0.54  
% 1.38/0.54  cnf(u248,negated_conjecture,
% 1.38/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.38/0.54  
% 1.38/0.54  cnf(u381,negated_conjecture,
% 1.38/0.54      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)).
% 1.38/0.54  
% 1.38/0.54  cnf(u239,axiom,
% 1.38/0.54      k1_xboole_0 = k4_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 1.38/0.54  
% 1.38/0.54  cnf(u238,negated_conjecture,
% 1.38/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 1.38/0.54  
% 1.38/0.54  cnf(u356,negated_conjecture,
% 1.38/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 1.38/0.54  
% 1.38/0.54  cnf(u77,negated_conjecture,
% 1.38/0.54      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.38/0.54  
% 1.38/0.54  cnf(u80,axiom,
% 1.38/0.54      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.38/0.54  
% 1.38/0.54  cnf(u344,negated_conjecture,
% 1.38/0.54      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 1.38/0.54  
% 1.38/0.54  cnf(u346,negated_conjecture,
% 1.38/0.54      k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0))))).
% 1.38/0.54  
% 1.38/0.54  cnf(u161,axiom,
% 1.38/0.54      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.38/0.54  
% 1.38/0.54  cnf(u152,axiom,
% 1.38/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))))).
% 1.38/0.54  
% 1.38/0.54  cnf(u89,axiom,
% 1.38/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 1.38/0.54  
% 1.38/0.54  cnf(u187,axiom,
% 1.38/0.54      k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k5_xboole_0(X3,k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3))).
% 1.38/0.54  
% 1.38/0.54  cnf(u209,axiom,
% 1.38/0.54      k5_xboole_0(X7,k7_subset_1(X6,X6,X7)) = k5_xboole_0(X6,k7_subset_1(k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),X6))).
% 1.38/0.54  
% 1.38/0.54  cnf(u91,axiom,
% 1.38/0.54      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 1.38/0.54  
% 1.38/0.54  cnf(u65,axiom,
% 1.38/0.54      k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0).
% 1.38/0.54  
% 1.38/0.54  cnf(u113,axiom,
% 1.38/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.38/0.54  
% 1.38/0.54  cnf(u305,axiom,
% 1.38/0.54      k4_subset_1(X0,k1_xboole_0,X0) = X0).
% 1.38/0.54  
% 1.38/0.54  cnf(u307,axiom,
% 1.38/0.54      k4_subset_1(X1,X1,X1) = X1).
% 1.38/0.54  
% 1.38/0.54  cnf(u240,axiom,
% 1.38/0.54      k4_subset_1(X1,X1,k1_xboole_0) = X1).
% 1.38/0.54  
% 1.38/0.54  cnf(u61,axiom,
% 1.38/0.54      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.38/0.54  
% 1.38/0.54  cnf(u114,axiom,
% 1.38/0.54      k5_xboole_0(k1_xboole_0,X0) = X0).
% 1.38/0.54  
% 1.38/0.54  cnf(u42,axiom,
% 1.38/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.38/0.54  
% 1.38/0.54  cnf(u71,negated_conjecture,
% 1.38/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.38/0.54  
% 1.38/0.54  % (4936)# SZS output end Saturation.
% 1.38/0.54  % (4936)------------------------------
% 1.38/0.54  % (4936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (4936)Termination reason: Satisfiable
% 1.38/0.54  
% 1.38/0.54  % (4936)Memory used [KB]: 6524
% 1.38/0.54  % (4936)Time elapsed: 0.118 s
% 1.38/0.54  % (4936)------------------------------
% 1.38/0.54  % (4936)------------------------------
% 1.38/0.54  % (4929)Success in time 0.172 s
%------------------------------------------------------------------------------
