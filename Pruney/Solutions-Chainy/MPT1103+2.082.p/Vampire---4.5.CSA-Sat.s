%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   47 (  47 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u30,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u38,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u60,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u50,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u33,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | k1_xboole_0 = k7_subset_1(X4,X3,X4) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k3_xboole_0(X1,X2) = k7_subset_1(X2,X1,k1_xboole_0) )).

cnf(u75,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u72,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u39,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u74,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u79,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u78,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u77,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u46,axiom,
    ( k9_subset_1(X3,X4,X3) = k3_xboole_0(X4,X3) )).

cnf(u44,negated_conjecture,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) )).

cnf(u35,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u63,axiom,
    ( k3_xboole_0(X1,X1) = k7_subset_1(X1,X1,k1_xboole_0) )).

cnf(u62,axiom,
    ( k3_xboole_0(k1_xboole_0,X0) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u61,negated_conjecture,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u59,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u58,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X0) )).

cnf(u57,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u73,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k9_subset_1(X1,X2,k1_xboole_0) )).

cnf(u42,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u27,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u37,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (25164)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (25156)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (25156)Refutation not found, incomplete strategy% (25156)------------------------------
% 0.21/0.54  % (25156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25156)Memory used [KB]: 6140
% 0.21/0.54  % (25156)Time elapsed: 0.005 s
% 0.21/0.54  % (25156)------------------------------
% 0.21/0.54  % (25156)------------------------------
% 0.21/0.54  % (25164)Refutation not found, incomplete strategy% (25164)------------------------------
% 0.21/0.54  % (25164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25164)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25164)Memory used [KB]: 1791
% 0.21/0.54  % (25164)Time elapsed: 0.074 s
% 0.21/0.54  % (25164)------------------------------
% 0.21/0.54  % (25164)------------------------------
% 0.21/0.55  % (25148)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (25148)Refutation not found, incomplete strategy% (25148)------------------------------
% 0.21/0.55  % (25148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25148)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25148)Memory used [KB]: 6268
% 0.21/0.55  % (25148)Time elapsed: 0.078 s
% 0.21/0.55  % (25148)------------------------------
% 0.21/0.55  % (25148)------------------------------
% 0.21/0.57  % (25163)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.58  % (25155)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.58  % (25147)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.58  % (25147)# SZS output start Saturation.
% 0.21/0.58  cnf(u23,negated_conjecture,
% 0.21/0.58      l1_struct_0(sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u30,axiom,
% 0.21/0.58      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.58  
% 0.21/0.58  cnf(u38,axiom,
% 0.21/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u26,axiom,
% 0.21/0.58      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u22,negated_conjecture,
% 0.21/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u60,negated_conjecture,
% 0.21/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u50,negated_conjecture,
% 0.21/0.58      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u31,axiom,
% 0.21/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.58  
% 0.21/0.58  cnf(u33,axiom,
% 0.21/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u32,axiom,
% 0.21/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))).
% 0.21/0.58  
% 0.21/0.58  cnf(u56,axiom,
% 0.21/0.58      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | k1_xboole_0 = k7_subset_1(X4,X3,X4)).
% 0.21/0.58  
% 0.21/0.58  cnf(u54,axiom,
% 0.21/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k3_xboole_0(X1,X2) = k7_subset_1(X2,X1,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u75,negated_conjecture,
% 0.21/0.58      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u72,negated_conjecture,
% 0.21/0.58      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u39,negated_conjecture,
% 0.21/0.58      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u74,negated_conjecture,
% 0.21/0.58      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u79,negated_conjecture,
% 0.21/0.58      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u78,negated_conjecture,
% 0.21/0.58      k7_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u77,negated_conjecture,
% 0.21/0.58      k7_subset_1(u1_struct_0(sK0),sK1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u46,axiom,
% 0.21/0.58      k9_subset_1(X3,X4,X3) = k3_xboole_0(X4,X3)).
% 0.21/0.58  
% 0.21/0.58  cnf(u44,negated_conjecture,
% 0.21/0.58      k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u35,axiom,
% 0.21/0.58      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u63,axiom,
% 0.21/0.58      k3_xboole_0(X1,X1) = k7_subset_1(X1,X1,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u62,axiom,
% 0.21/0.58      k3_xboole_0(k1_xboole_0,X0) = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u61,negated_conjecture,
% 0.21/0.58      k3_xboole_0(sK1,u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u59,axiom,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u58,axiom,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u57,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u73,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u20,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u47,axiom,
% 0.21/0.58      k1_xboole_0 = k9_subset_1(X1,X2,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u42,axiom,
% 0.21/0.58      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u27,axiom,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u37,negated_conjecture,
% 0.21/0.58      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.58  
% 0.21/0.58  % (25147)# SZS output end Saturation.
% 0.21/0.58  % (25147)------------------------------
% 0.21/0.58  % (25147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (25147)Termination reason: Satisfiable
% 0.21/0.58  
% 0.21/0.58  % (25147)Memory used [KB]: 6268
% 0.21/0.58  % (25147)Time elapsed: 0.144 s
% 0.21/0.58  % (25147)------------------------------
% 0.21/0.58  % (25147)------------------------------
% 0.21/0.58  % (25140)Success in time 0.213 s
%------------------------------------------------------------------------------
