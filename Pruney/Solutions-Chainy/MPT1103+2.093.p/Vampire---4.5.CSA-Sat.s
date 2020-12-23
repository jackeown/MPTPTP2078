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
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 1.32s
% Output     : Saturation 1.32s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u28,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u44,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u132,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u69,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u38,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u135,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u133,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u134,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1)) )).

cnf(u74,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)) )).

cnf(u106,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u68,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u76,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1)))) )).

cnf(u50,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)))) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u52,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u40,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u77,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u24,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u26,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u43,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:02:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.16/0.52  % (23288)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.52  % (23292)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.53  % (23295)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.16/0.53  % (23311)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.16/0.53  % (23287)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.53  % (23286)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.53  % (23291)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.53  % (23303)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.54  % (23289)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (23290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.32/0.54  % (23292)# SZS output start Saturation.
% 1.32/0.54  cnf(u23,negated_conjecture,
% 1.32/0.54      l1_struct_0(sK0)).
% 1.32/0.54  
% 1.32/0.54  cnf(u28,axiom,
% 1.32/0.54      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 1.32/0.54  
% 1.32/0.54  cnf(u44,axiom,
% 1.32/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.32/0.54  
% 1.32/0.54  cnf(u22,negated_conjecture,
% 1.32/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.32/0.54  
% 1.32/0.54  cnf(u132,negated_conjecture,
% 1.32/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 1.32/0.54  
% 1.32/0.54  cnf(u69,axiom,
% 1.32/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.32/0.54  
% 1.32/0.54  cnf(u38,axiom,
% 1.32/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.32/0.54  
% 1.32/0.54  cnf(u135,negated_conjecture,
% 1.32/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 1.32/0.54  
% 1.32/0.54  cnf(u133,negated_conjecture,
% 1.32/0.54      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.32/0.54  
% 1.32/0.54  cnf(u134,negated_conjecture,
% 1.32/0.54      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 1.32/0.54  
% 1.32/0.54  cnf(u71,negated_conjecture,
% 1.32/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.32/0.54  
% 1.32/0.54  cnf(u84,axiom,
% 1.32/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1))).
% 1.32/0.54  
% 1.32/0.54  cnf(u74,axiom,
% 1.32/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))).
% 1.32/0.54  
% 1.32/0.54  cnf(u106,axiom,
% 1.32/0.54      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 1.32/0.54  
% 1.32/0.54  cnf(u78,axiom,
% 1.32/0.54      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 1.32/0.54  
% 1.32/0.54  cnf(u20,negated_conjecture,
% 1.32/0.54      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.32/0.54  
% 1.32/0.54  cnf(u68,axiom,
% 1.32/0.54      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.32/0.54  
% 1.32/0.54  cnf(u76,axiom,
% 1.32/0.54      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X1))))).
% 1.32/0.54  
% 1.32/0.54  cnf(u50,axiom,
% 1.32/0.54      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))))).
% 1.32/0.54  
% 1.32/0.54  cnf(u70,axiom,
% 1.32/0.54      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 1.32/0.54  
% 1.32/0.54  cnf(u52,axiom,
% 1.32/0.54      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 1.32/0.54  
% 1.32/0.54  cnf(u40,axiom,
% 1.32/0.54      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.32/0.54  
% 1.32/0.54  cnf(u77,axiom,
% 1.32/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.32/0.54  
% 1.32/0.54  cnf(u24,axiom,
% 1.32/0.54      k2_subset_1(X0) = X0).
% 1.32/0.54  
% 1.32/0.54  cnf(u26,axiom,
% 1.32/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.32/0.54  
% 1.32/0.54  cnf(u43,negated_conjecture,
% 1.32/0.54      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.32/0.54  
% 1.32/0.54  % (23292)# SZS output end Saturation.
% 1.32/0.54  % (23292)------------------------------
% 1.32/0.54  % (23292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (23292)Termination reason: Satisfiable
% 1.32/0.54  
% 1.32/0.54  % (23292)Memory used [KB]: 6268
% 1.32/0.54  % (23292)Time elapsed: 0.118 s
% 1.32/0.54  % (23292)------------------------------
% 1.32/0.54  % (23292)------------------------------
% 1.32/0.54  % (23291)Refutation not found, incomplete strategy% (23291)------------------------------
% 1.32/0.54  % (23291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (23291)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (23291)Memory used [KB]: 6268
% 1.32/0.54  % (23291)Time elapsed: 0.129 s
% 1.32/0.54  % (23291)------------------------------
% 1.32/0.54  % (23291)------------------------------
% 1.32/0.54  % (23285)Success in time 0.172 s
%------------------------------------------------------------------------------
