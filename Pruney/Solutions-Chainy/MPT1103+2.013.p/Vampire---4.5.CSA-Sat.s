%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:35 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :   44 (  44 expanded)
%              Number of equality atoms :   36 (  36 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u49,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u39,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u171,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u50,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u51,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u46,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u56,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u232,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u174,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) )).

cnf(u169,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u173,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u185,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u24,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u214,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_setfam_1(k2_tarski(X12,X11)),k1_setfam_1(k2_tarski(X12,X11)),X11) )).

cnf(u213,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_setfam_1(k2_tarski(X9,X10)),k1_setfam_1(k2_tarski(X9,X10)),X9) )).

cnf(u179,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) )).

cnf(u178,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) )).

cnf(u184,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u135,axiom,
    ( k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(X3,X2)) )).

cnf(u97,axiom,
    ( k3_tarski(k2_tarski(X2,X1)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) )).

cnf(u84,axiom,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )).

cnf(u62,negated_conjecture,
    ( u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u31,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u128,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u93,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_setfam_1(k2_tarski(X3,X2)),k1_setfam_1(k2_tarski(X2,k1_setfam_1(k2_tarski(X3,X2))))) )).

cnf(u92,axiom,
    ( k1_xboole_0 = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))) )).

cnf(u170,axiom,
    ( k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) )).

cnf(u172,axiom,
    ( k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) )).

cnf(u69,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u63,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))) )).

cnf(u43,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )).

cnf(u42,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u27,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u54,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 )).

cnf(u52,axiom,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 )).

cnf(u44,axiom,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 )).

cnf(u28,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u48,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (500)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (481)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (489)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (500)Refutation not found, incomplete strategy% (500)------------------------------
% 0.20/0.50  % (500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (500)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (500)Memory used [KB]: 10746
% 0.20/0.50  % (500)Time elapsed: 0.056 s
% 0.20/0.50  % (500)------------------------------
% 0.20/0.50  % (500)------------------------------
% 0.20/0.50  % (506)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (469)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (498)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (474)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (474)Refutation not found, incomplete strategy% (474)------------------------------
% 0.20/0.51  % (474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (474)Memory used [KB]: 10618
% 0.20/0.51  % (474)Time elapsed: 0.108 s
% 0.20/0.51  % (474)------------------------------
% 0.20/0.51  % (474)------------------------------
% 0.20/0.51  % (486)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (469)# SZS output start Saturation.
% 0.20/0.51  cnf(u49,axiom,
% 0.20/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u26,negated_conjecture,
% 0.20/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u39,axiom,
% 0.20/0.51      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u171,axiom,
% 0.20/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u50,negated_conjecture,
% 0.20/0.51      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u51,axiom,
% 0.20/0.51      r1_tarski(X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u46,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u56,negated_conjecture,
% 0.20/0.51      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u232,negated_conjecture,
% 0.20/0.51      k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u174,axiom,
% 0.20/0.51      k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u169,axiom,
% 0.20/0.51      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.20/0.51  
% 0.20/0.51  cnf(u173,negated_conjecture,
% 0.20/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u185,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u24,negated_conjecture,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u214,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(k1_setfam_1(k2_tarski(X12,X11)),k1_setfam_1(k2_tarski(X12,X11)),X11)).
% 0.20/0.51  
% 0.20/0.51  cnf(u213,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(k1_setfam_1(k2_tarski(X9,X10)),k1_setfam_1(k2_tarski(X9,X10)),X9)).
% 0.20/0.51  
% 0.20/0.51  cnf(u179,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u178,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u184,axiom,
% 0.20/0.51      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u135,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X2,X3)) = k3_tarski(k2_tarski(X3,X2))).
% 0.20/0.51  
% 0.20/0.51  cnf(u97,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X2,X1)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X2,X1))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u84,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u62,negated_conjecture,
% 0.20/0.51      u1_struct_0(sK0) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.51  
% 0.20/0.51  cnf(u31,axiom,
% 0.20/0.51      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u128,negated_conjecture,
% 0.20/0.51      u1_struct_0(sK0) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.51  
% 0.20/0.51  cnf(u93,axiom,
% 0.20/0.51      k1_xboole_0 = k5_xboole_0(k1_setfam_1(k2_tarski(X3,X2)),k1_setfam_1(k2_tarski(X2,k1_setfam_1(k2_tarski(X3,X2)))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u92,axiom,
% 0.20/0.51      k1_xboole_0 = k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u170,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X1,X0)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u172,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0))).
% 0.20/0.51  
% 0.20/0.51  cnf(u69,axiom,
% 0.20/0.51      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u63,axiom,
% 0.20/0.51      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u43,axiom,
% 0.20/0.51      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))).
% 0.20/0.51  
% 0.20/0.51  cnf(u42,axiom,
% 0.20/0.51      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u27,axiom,
% 0.20/0.51      k2_subset_1(X0) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u54,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,X0)) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u52,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u44,axiom,
% 0.20/0.51      k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u28,axiom,
% 0.20/0.51      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.51  
% 0.20/0.51  cnf(u48,negated_conjecture,
% 0.20/0.51      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.51  
% 0.20/0.51  % (469)# SZS output end Saturation.
% 0.20/0.51  % (469)------------------------------
% 0.20/0.51  % (469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (469)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (469)Memory used [KB]: 6268
% 0.20/0.51  % (469)Time elapsed: 0.077 s
% 0.20/0.51  % (469)------------------------------
% 0.20/0.51  % (469)------------------------------
% 0.20/0.51  % (481)Refutation not found, incomplete strategy% (481)------------------------------
% 0.20/0.51  % (481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (461)Success in time 0.162 s
%------------------------------------------------------------------------------
