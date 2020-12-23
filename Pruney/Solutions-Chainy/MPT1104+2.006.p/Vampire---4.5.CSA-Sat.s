%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:51 EST 2020

% Result     : CounterSatisfiable 1.27s
% Output     : Saturation 1.27s
% Verified   : 
% Statistics : Number of clauses        :   44 (  44 expanded)
%              Number of leaves         :   44 (  44 expanded)
%              Depth                    :    0
%              Number of atoms          :   52 (  52 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u42,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u79,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) )).

cnf(u80,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) )).

cnf(u57,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u81,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3) )).

cnf(u44,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u34,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u48,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u95,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u90,negated_conjecture,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) )).

cnf(u86,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u96,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u89,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u87,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u85,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u107,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u23,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u46,axiom,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))) = X0 )).

cnf(u39,axiom,
    ( k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0 )).

cnf(u73,axiom,
    ( k7_subset_1(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),X0) )).

cnf(u63,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u65,axiom,
    ( k7_subset_1(X0,X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0) )).

cnf(u59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u108,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u88,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u104,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u82,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u27,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u29,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u92,negated_conjecture,
    ( k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u91,negated_conjecture,
    ( k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u74,axiom,
    ( k7_subset_1(k2_xboole_0(X3,X2),k2_xboole_0(X3,X2),X2) = k5_xboole_0(k2_xboole_0(X3,X2),X2) )).

cnf(u66,axiom,
    ( k7_subset_1(X2,X2,k2_xboole_0(X3,X2)) = k5_xboole_0(X2,X2) )).

cnf(u56,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u110,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u109,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u111,axiom,
    ( k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

cnf(u30,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u25,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (25541)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (25534)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (25541)Refutation not found, incomplete strategy% (25541)------------------------------
% 0.19/0.50  % (25541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (25542)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  % (25542)Refutation not found, incomplete strategy% (25542)------------------------------
% 0.19/0.51  % (25542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (25542)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (25542)Memory used [KB]: 10746
% 0.19/0.51  % (25542)Time elapsed: 0.105 s
% 0.19/0.51  % (25542)------------------------------
% 0.19/0.51  % (25542)------------------------------
% 0.19/0.51  % (25541)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (25541)Memory used [KB]: 10746
% 0.19/0.51  % (25541)Time elapsed: 0.093 s
% 0.19/0.51  % (25541)------------------------------
% 0.19/0.51  % (25541)------------------------------
% 0.19/0.51  % (25543)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (25549)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (25538)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (25554)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (25557)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.51  % (25554)Refutation not found, incomplete strategy% (25554)------------------------------
% 0.19/0.51  % (25554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (25554)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (25554)Memory used [KB]: 10746
% 0.19/0.51  % (25554)Time elapsed: 0.091 s
% 0.19/0.51  % (25554)------------------------------
% 0.19/0.51  % (25554)------------------------------
% 1.27/0.51  % SZS status CounterSatisfiable for theBenchmark
% 1.27/0.51  % (25538)# SZS output start Saturation.
% 1.27/0.51  cnf(u42,axiom,
% 1.27/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u26,negated_conjecture,
% 1.27/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.27/0.51  
% 1.27/0.51  cnf(u22,negated_conjecture,
% 1.27/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.27/0.51  
% 1.27/0.51  cnf(u79,negated_conjecture,
% 1.27/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u80,negated_conjecture,
% 1.27/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u57,axiom,
% 1.27/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u37,axiom,
% 1.27/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u81,axiom,
% 1.27/0.51      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3)).
% 1.27/0.51  
% 1.27/0.51  cnf(u44,negated_conjecture,
% 1.27/0.51      r1_xboole_0(sK2,sK1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u24,negated_conjecture,
% 1.27/0.51      r1_xboole_0(sK1,sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u34,axiom,
% 1.27/0.51      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u48,axiom,
% 1.27/0.51      ~r1_xboole_0(X0,X1) | k5_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 1.27/0.51  
% 1.27/0.51  cnf(u95,negated_conjecture,
% 1.27/0.51      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u90,negated_conjecture,
% 1.27/0.51      sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))).
% 1.27/0.51  
% 1.27/0.51  cnf(u86,negated_conjecture,
% 1.27/0.51      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u96,negated_conjecture,
% 1.27/0.51      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u89,negated_conjecture,
% 1.27/0.51      sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))).
% 1.27/0.51  
% 1.27/0.51  cnf(u87,negated_conjecture,
% 1.27/0.51      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u85,negated_conjecture,
% 1.27/0.51      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u107,negated_conjecture,
% 1.27/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u23,negated_conjecture,
% 1.27/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u46,axiom,
% 1.27/0.51      k1_setfam_1(k2_tarski(X0,k2_xboole_0(X1,X0))) = X0).
% 1.27/0.51  
% 1.27/0.51  cnf(u39,axiom,
% 1.27/0.51      k1_setfam_1(k2_tarski(X0,k2_xboole_0(X0,X1))) = X0).
% 1.27/0.51  
% 1.27/0.51  cnf(u73,axiom,
% 1.27/0.51      k7_subset_1(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1),X0) = k5_xboole_0(k2_xboole_0(X0,X1),X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u63,axiom,
% 1.27/0.51      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.27/0.51  
% 1.27/0.51  cnf(u65,axiom,
% 1.27/0.51      k7_subset_1(X0,X0,k2_xboole_0(X0,X1)) = k5_xboole_0(X0,X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u59,negated_conjecture,
% 1.27/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u58,negated_conjecture,
% 1.27/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u108,negated_conjecture,
% 1.27/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u88,negated_conjecture,
% 1.27/0.51      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u104,negated_conjecture,
% 1.27/0.51      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 1.27/0.51  
% 1.27/0.51  cnf(u82,negated_conjecture,
% 1.27/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u27,axiom,
% 1.27/0.51      k2_subset_1(X0) = X0).
% 1.27/0.51  
% 1.27/0.51  cnf(u29,axiom,
% 1.27/0.51      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u92,negated_conjecture,
% 1.27/0.51      k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u91,negated_conjecture,
% 1.27/0.51      k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u74,axiom,
% 1.27/0.51      k7_subset_1(k2_xboole_0(X3,X2),k2_xboole_0(X3,X2),X2) = k5_xboole_0(k2_xboole_0(X3,X2),X2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u66,axiom,
% 1.27/0.51      k7_subset_1(X2,X2,k2_xboole_0(X3,X2)) = k5_xboole_0(X2,X2)).
% 1.27/0.51  
% 1.27/0.51  cnf(u56,axiom,
% 1.27/0.51      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.27/0.51  
% 1.27/0.51  cnf(u110,negated_conjecture,
% 1.27/0.51      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u109,negated_conjecture,
% 1.27/0.51      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.27/0.51  
% 1.27/0.51  cnf(u111,axiom,
% 1.27/0.51      k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u30,axiom,
% 1.27/0.51      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 1.27/0.51  
% 1.27/0.51  cnf(u25,negated_conjecture,
% 1.27/0.51      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.27/0.51  
% 1.27/0.51  % (25538)# SZS output end Saturation.
% 1.27/0.51  % (25538)------------------------------
% 1.27/0.51  % (25538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.51  % (25538)Termination reason: Satisfiable
% 1.27/0.51  
% 1.27/0.51  % (25538)Memory used [KB]: 6268
% 1.27/0.51  % (25538)Time elapsed: 0.075 s
% 1.27/0.51  % (25538)------------------------------
% 1.27/0.51  % (25538)------------------------------
% 1.27/0.51  % (25549)Refutation not found, incomplete strategy% (25549)------------------------------
% 1.27/0.51  % (25549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.51  % (25546)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.51  % (25549)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.51  
% 1.27/0.51  % (25549)Memory used [KB]: 10618
% 1.27/0.51  % (25549)Time elapsed: 0.103 s
% 1.27/0.51  % (25549)------------------------------
% 1.27/0.51  % (25549)------------------------------
% 1.27/0.51  % (25537)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.52  % (25533)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.52  % (25534)Refutation not found, incomplete strategy% (25534)------------------------------
% 1.27/0.52  % (25534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25534)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25534)Memory used [KB]: 10746
% 1.27/0.52  % (25534)Time elapsed: 0.110 s
% 1.27/0.52  % (25534)------------------------------
% 1.27/0.52  % (25534)------------------------------
% 1.27/0.52  % (25537)Refutation not found, incomplete strategy% (25537)------------------------------
% 1.27/0.52  % (25537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25537)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25537)Memory used [KB]: 6268
% 1.27/0.52  % (25537)Time elapsed: 0.117 s
% 1.27/0.52  % (25537)------------------------------
% 1.27/0.52  % (25537)------------------------------
% 1.27/0.52  % (25535)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.27/0.52  % (25557)Refutation not found, incomplete strategy% (25557)------------------------------
% 1.27/0.52  % (25557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25557)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25557)Memory used [KB]: 6396
% 1.27/0.52  % (25557)Time elapsed: 0.106 s
% 1.27/0.52  % (25557)------------------------------
% 1.27/0.52  % (25557)------------------------------
% 1.27/0.52  % (25532)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.52  % (25536)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.52  % (25532)Refutation not found, incomplete strategy% (25532)------------------------------
% 1.27/0.52  % (25532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25532)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25532)Memory used [KB]: 1791
% 1.27/0.52  % (25532)Time elapsed: 0.090 s
% 1.27/0.52  % (25532)------------------------------
% 1.27/0.52  % (25532)------------------------------
% 1.27/0.52  % (25536)Refutation not found, incomplete strategy% (25536)------------------------------
% 1.27/0.52  % (25536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25536)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25536)Memory used [KB]: 6268
% 1.27/0.52  % (25536)Time elapsed: 0.119 s
% 1.27/0.52  % (25536)------------------------------
% 1.27/0.52  % (25536)------------------------------
% 1.27/0.52  % (25547)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.52  % (25535)Refutation not found, incomplete strategy% (25535)------------------------------
% 1.27/0.52  % (25535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25535)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25535)Memory used [KB]: 10746
% 1.27/0.52  % (25535)Time elapsed: 0.119 s
% 1.27/0.52  % (25535)------------------------------
% 1.27/0.52  % (25535)------------------------------
% 1.27/0.52  % (25547)Refutation not found, incomplete strategy% (25547)------------------------------
% 1.27/0.52  % (25547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (25547)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (25547)Memory used [KB]: 6140
% 1.27/0.52  % (25547)Time elapsed: 0.001 s
% 1.27/0.52  % (25547)------------------------------
% 1.27/0.52  % (25547)------------------------------
% 1.27/0.52  % (25556)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.27/0.52  % (25553)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.52  % (25539)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (25550)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.27/0.53  % (25558)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.27/0.53  % (25539)Refutation not found, incomplete strategy% (25539)------------------------------
% 1.27/0.53  % (25539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (25539)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (25539)Memory used [KB]: 6268
% 1.27/0.53  % (25539)Time elapsed: 0.132 s
% 1.27/0.53  % (25539)------------------------------
% 1.27/0.53  % (25539)------------------------------
% 1.27/0.53  % (25561)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.27/0.53  % (25560)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.53  % (25545)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.53  % (25531)Success in time 0.173 s
%------------------------------------------------------------------------------
