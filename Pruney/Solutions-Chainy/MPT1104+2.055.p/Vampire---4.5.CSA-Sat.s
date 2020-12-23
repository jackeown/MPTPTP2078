%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:57 EST 2020

% Result     : CounterSatisfiable 1.30s
% Output     : Saturation 1.30s
% Verified   : 
% Statistics : Number of clauses        :   57 (  57 expanded)
%              Number of leaves         :   57 (  57 expanded)
%              Depth                    :    0
%              Number of atoms          :   64 (  64 expanded)
%              Number of equality atoms :   53 (  53 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u46,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u107,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u108,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u67,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u109,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

% (27447)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
cnf(u24,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u71,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0) )).

cnf(u164,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u163,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u159,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u117,negated_conjecture,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) )).

cnf(u118,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u113,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u131,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u23,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u143,axiom,
    ( k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))) = X2 )).

cnf(u54,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u52,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 )).

cnf(u42,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 )).

cnf(u126,negated_conjecture,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) )).

cnf(u119,negated_conjecture,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u150,axiom,
    ( k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),X0) )).

cnf(u101,axiom,
    ( k7_subset_1(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X3,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X3,X2)),X2) )).

cnf(u100,axiom,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) )).

cnf(u75,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u80,axiom,
    ( k7_subset_1(X5,X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) )).

cnf(u70,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u69,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u161,negated_conjecture,
    ( k4_subset_1(sK2,sK2,sK2) = k7_subset_1(k4_subset_1(sK2,sK2,sK2),k4_subset_1(sK2,sK2,sK2),sK1) )).

cnf(u137,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u136,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u132,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u114,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u27,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u153,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) = k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1) )).

cnf(u134,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u133,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u135,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u48,axiom,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

cnf(u40,axiom,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

cnf(u31,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u56,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u55,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) )).

cnf(u116,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u115,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u141,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0)) )).

cnf(u83,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) )).

% (27442)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
cnf(u82,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) )).

cnf(u85,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k7_subset_1(X4,X4,X4) )).

cnf(u138,axiom,
    ( k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u66,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u25,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.19/0.51  % (27444)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.19/0.51  % (27436)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.19/0.52  % (27428)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.52  % (27431)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.19/0.53  % (27439)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.30/0.53  % (27431)Refutation not found, incomplete strategy% (27431)------------------------------
% 1.30/0.53  % (27431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (27423)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.53  % (27439)Refutation not found, incomplete strategy% (27439)------------------------------
% 1.30/0.53  % (27439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (27431)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (27431)Memory used [KB]: 10746
% 1.30/0.53  % (27431)Time elapsed: 0.116 s
% 1.30/0.53  % (27431)------------------------------
% 1.30/0.53  % (27431)------------------------------
% 1.30/0.53  % (27439)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (27439)Memory used [KB]: 10618
% 1.30/0.53  % (27439)Time elapsed: 0.121 s
% 1.30/0.53  % (27439)------------------------------
% 1.30/0.53  % (27439)------------------------------
% 1.30/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.30/0.53  % (27424)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (27425)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.53  % (27426)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.53  % (27428)# SZS output start Saturation.
% 1.30/0.53  cnf(u46,axiom,
% 1.30/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u26,negated_conjecture,
% 1.30/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u22,negated_conjecture,
% 1.30/0.53      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u107,negated_conjecture,
% 1.30/0.53      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 1.30/0.53  
% 1.30/0.53  cnf(u108,negated_conjecture,
% 1.30/0.53      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 1.30/0.53  
% 1.30/0.53  cnf(u67,axiom,
% 1.30/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.30/0.53  
% 1.30/0.53  cnf(u45,axiom,
% 1.30/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 1.30/0.53  
% 1.30/0.53  cnf(u109,axiom,
% 1.30/0.53      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 1.30/0.53  
% 1.30/0.53  % (27447)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.53  cnf(u24,negated_conjecture,
% 1.30/0.53      r1_xboole_0(sK1,sK2)).
% 1.30/0.53  
% 1.30/0.53  cnf(u71,axiom,
% 1.30/0.53      ~r1_xboole_0(X0,X1) | k3_tarski(k2_tarski(k7_subset_1(X2,X2,X0),X1)) = k7_subset_1(k3_tarski(k2_tarski(X2,X1)),k3_tarski(k2_tarski(X2,X1)),X0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u164,negated_conjecture,
% 1.30/0.53      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u163,negated_conjecture,
% 1.30/0.53      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u159,negated_conjecture,
% 1.30/0.53      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u117,negated_conjecture,
% 1.30/0.53      sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u118,negated_conjecture,
% 1.30/0.53      sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u113,negated_conjecture,
% 1.30/0.53      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 1.30/0.53  
% 1.30/0.53  cnf(u131,negated_conjecture,
% 1.30/0.53      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u23,negated_conjecture,
% 1.30/0.53      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.30/0.53  
% 1.30/0.53  cnf(u143,axiom,
% 1.30/0.53      k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))) = X2).
% 1.30/0.53  
% 1.30/0.53  cnf(u54,axiom,
% 1.30/0.53      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.30/0.53  
% 1.30/0.53  cnf(u52,axiom,
% 1.30/0.53      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0).
% 1.30/0.53  
% 1.30/0.53  cnf(u42,axiom,
% 1.30/0.53      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0).
% 1.30/0.53  
% 1.30/0.53  cnf(u126,negated_conjecture,
% 1.30/0.53      k7_subset_1(k3_tarski(k2_tarski(X0,sK2)),k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u119,negated_conjecture,
% 1.30/0.53      k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 1.30/0.53  
% 1.30/0.53  cnf(u150,axiom,
% 1.30/0.53      k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),X0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u101,axiom,
% 1.30/0.53      k7_subset_1(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X3,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X3,X2)),X2)).
% 1.30/0.53  
% 1.30/0.53  cnf(u100,axiom,
% 1.30/0.53      k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u75,axiom,
% 1.30/0.53      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u80,axiom,
% 1.30/0.53      k7_subset_1(X5,X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u70,negated_conjecture,
% 1.30/0.53      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u69,negated_conjecture,
% 1.30/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u161,negated_conjecture,
% 1.30/0.53      k4_subset_1(sK2,sK2,sK2) = k7_subset_1(k4_subset_1(sK2,sK2,sK2),k4_subset_1(sK2,sK2,sK2),sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u137,negated_conjecture,
% 1.30/0.53      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 1.30/0.53  
% 1.30/0.53  cnf(u136,negated_conjecture,
% 1.30/0.53      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u132,negated_conjecture,
% 1.30/0.53      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u114,negated_conjecture,
% 1.30/0.53      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 1.30/0.53  
% 1.30/0.53  cnf(u27,axiom,
% 1.30/0.53      k2_subset_1(X0) = X0).
% 1.30/0.53  
% 1.30/0.53  cnf(u153,negated_conjecture,
% 1.30/0.53      k3_tarski(k2_tarski(sK2,k7_subset_1(X0,X0,sK1))) = k7_subset_1(k3_tarski(k2_tarski(sK2,X0)),k3_tarski(k2_tarski(sK2,X0)),sK1)).
% 1.30/0.53  
% 1.30/0.53  cnf(u134,negated_conjecture,
% 1.30/0.53      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u133,negated_conjecture,
% 1.30/0.53      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u135,axiom,
% 1.30/0.53      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u48,axiom,
% 1.30/0.53      k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0).
% 1.30/0.53  
% 1.30/0.53  cnf(u40,axiom,
% 1.30/0.53      k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0).
% 1.30/0.53  
% 1.30/0.53  cnf(u31,axiom,
% 1.30/0.53      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.30/0.53  
% 1.30/0.53  cnf(u56,axiom,
% 1.30/0.53      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u55,axiom,
% 1.30/0.53      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))).
% 1.30/0.53  
% 1.30/0.53  cnf(u116,negated_conjecture,
% 1.30/0.53      k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u115,negated_conjecture,
% 1.30/0.53      k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u141,axiom,
% 1.30/0.53      k1_xboole_0 = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0))).
% 1.30/0.53  
% 1.30/0.53  cnf(u83,axiom,
% 1.30/0.53      k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2)))).
% 1.30/0.53  
% 1.30/0.54  % (27442)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  cnf(u82,axiom,
% 1.30/0.54      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1)))).
% 1.30/0.54  
% 1.30/0.54  cnf(u85,axiom,
% 1.30/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X6)).
% 1.30/0.54  
% 1.30/0.54  cnf(u84,axiom,
% 1.30/0.54      k1_xboole_0 = k7_subset_1(X4,X4,X4)).
% 1.30/0.54  
% 1.30/0.54  cnf(u138,axiom,
% 1.30/0.54      k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)).
% 1.30/0.54  
% 1.30/0.54  cnf(u47,axiom,
% 1.30/0.54      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.30/0.54  
% 1.30/0.54  cnf(u66,axiom,
% 1.30/0.54      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.30/0.54  
% 1.30/0.54  cnf(u25,negated_conjecture,
% 1.30/0.54      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.30/0.54  
% 1.30/0.54  % (27428)# SZS output end Saturation.
% 1.30/0.54  % (27428)------------------------------
% 1.30/0.54  % (27428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (27428)Termination reason: Satisfiable
% 1.30/0.54  
% 1.30/0.54  % (27428)Memory used [KB]: 6396
% 1.30/0.54  % (27428)Time elapsed: 0.081 s
% 1.30/0.54  % (27428)------------------------------
% 1.30/0.54  % (27428)------------------------------
% 1.30/0.54  % (27438)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.54  % (27418)Success in time 0.179 s
%------------------------------------------------------------------------------
