%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:50 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :   66 (  66 expanded)
%              Number of equality atoms :   49 (  49 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u56,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u29,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u146,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) )).

cnf(u147,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k5_xboole_0(X1,k7_subset_1(sK1,sK1,X1)) )).

cnf(u84,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u83,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) )).

cnf(u148,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = k4_subset_1(X3,X2,X3) )).

cnf(u52,axiom,
    ( r1_xboole_0(X0,X1)
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u68,axiom,
    ( r1_xboole_0(X3,X2)
    | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u58,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u27,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u39,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u51,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u95,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = X0 )).

cnf(u64,negated_conjecture,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2)) )).

cnf(u60,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u163,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u106,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u160,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u98,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,sK2) )).

cnf(u88,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u87,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u82,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u205,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u97,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u209,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u208,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u172,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u26,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u180,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u182,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u183,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u181,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u178,negated_conjecture,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u177,negated_conjecture,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u190,axiom,
    ( k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

cnf(u34,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u154,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK2,sK1) )).

cnf(u153,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK1,sK2) )).

cnf(u90,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u89,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u96,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u207,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u30,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u117,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u55,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u69,axiom,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
    | k1_xboole_0 = k1_setfam_1(k2_tarski(X1,X0)) )).

cnf(u158,axiom,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X3))
    | k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X3) = X2 )).

cnf(u157,axiom,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X0))
    | k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = X0 )).

cnf(u28,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:03:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (26243)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (26225)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (26234)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (26234)Refutation not found, incomplete strategy% (26234)------------------------------
% 0.22/0.53  % (26234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26234)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26234)Memory used [KB]: 6140
% 0.22/0.53  % (26234)Time elapsed: 0.001 s
% 0.22/0.53  % (26234)------------------------------
% 0.22/0.53  % (26234)------------------------------
% 0.22/0.53  % (26227)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (26221)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (26233)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (26243)Refutation not found, incomplete strategy% (26243)------------------------------
% 0.22/0.54  % (26243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26243)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26243)Memory used [KB]: 1791
% 0.22/0.54  % (26243)Time elapsed: 0.114 s
% 0.22/0.54  % (26243)------------------------------
% 0.22/0.54  % (26243)------------------------------
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (26225)# SZS output start Saturation.
% 0.22/0.54  cnf(u56,axiom,
% 0.22/0.54      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u29,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u25,negated_conjecture,
% 0.22/0.54      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u146,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u147,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k5_xboole_0(X1,k7_subset_1(sK1,sK1,X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u84,axiom,
% 0.22/0.54      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u83,axiom,
% 0.22/0.54      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u148,axiom,
% 0.22/0.54      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = k4_subset_1(X3,X2,X3)).
% 0.22/0.54  
% 0.22/0.54  cnf(u52,axiom,
% 0.22/0.54      r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u68,axiom,
% 0.22/0.54      r1_xboole_0(X3,X2) | k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X3))).
% 0.22/0.54  
% 0.22/0.54  cnf(u58,negated_conjecture,
% 0.22/0.54      r1_xboole_0(sK2,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u27,negated_conjecture,
% 0.22/0.54      r1_xboole_0(sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u39,axiom,
% 0.22/0.54      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u51,axiom,
% 0.22/0.54      ~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u95,axiom,
% 0.22/0.54      ~r1_xboole_0(X0,X1) | k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u64,negated_conjecture,
% 0.22/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(sK1,sK2))).
% 0.22/0.54  
% 0.22/0.54  cnf(u60,axiom,
% 0.22/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u47,axiom,
% 0.22/0.54      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u163,negated_conjecture,
% 0.22/0.54      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u106,negated_conjecture,
% 0.22/0.54      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u160,negated_conjecture,
% 0.22/0.54      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u98,negated_conjecture,
% 0.22/0.54      sK1 = k7_subset_1(sK1,sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u88,negated_conjecture,
% 0.22/0.54      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u87,negated_conjecture,
% 0.22/0.54      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u82,axiom,
% 0.22/0.54      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u205,axiom,
% 0.22/0.54      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u97,axiom,
% 0.22/0.54      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u209,negated_conjecture,
% 0.22/0.54      sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u208,negated_conjecture,
% 0.22/0.54      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u172,negated_conjecture,
% 0.22/0.54      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u26,negated_conjecture,
% 0.22/0.54      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u180,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u182,negated_conjecture,
% 0.22/0.54      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u183,negated_conjecture,
% 0.22/0.54      k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u181,negated_conjecture,
% 0.22/0.54      k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u178,negated_conjecture,
% 0.22/0.54      k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u177,negated_conjecture,
% 0.22/0.54      k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u190,axiom,
% 0.22/0.54      k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u34,axiom,
% 0.22/0.54      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u154,negated_conjecture,
% 0.22/0.54      k2_struct_0(sK0) = k5_xboole_0(sK2,sK1)).
% 0.22/0.54  
% 0.22/0.54  cnf(u153,negated_conjecture,
% 0.22/0.54      k2_struct_0(sK0) = k5_xboole_0(sK1,sK2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u90,axiom,
% 0.22/0.54      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u89,axiom,
% 0.22/0.54      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 0.22/0.54  
% 0.22/0.54  cnf(u96,axiom,
% 0.22/0.54      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u207,axiom,
% 0.22/0.54      k4_subset_1(X0,X0,X0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u30,axiom,
% 0.22/0.54      k2_subset_1(X0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u117,axiom,
% 0.22/0.54      k5_xboole_0(k1_xboole_0,X0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u55,axiom,
% 0.22/0.54      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u69,axiom,
% 0.22/0.54      k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | k1_xboole_0 = k1_setfam_1(k2_tarski(X1,X0))).
% 0.22/0.54  
% 0.22/0.54  cnf(u158,axiom,
% 0.22/0.54      k1_xboole_0 != k1_setfam_1(k2_tarski(X2,X3)) | k7_subset_1(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X3) = X2).
% 0.22/0.54  
% 0.22/0.54  cnf(u157,axiom,
% 0.22/0.54      k1_xboole_0 != k1_setfam_1(k2_tarski(X1,X0)) | k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u28,negated_conjecture,
% 0.22/0.54      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.22/0.54  
% 0.22/0.54  % (26225)# SZS output end Saturation.
% 0.22/0.54  % (26225)------------------------------
% 0.22/0.54  % (26225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26225)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (26225)Memory used [KB]: 6268
% 0.22/0.54  % (26225)Time elapsed: 0.119 s
% 0.22/0.54  % (26225)------------------------------
% 0.22/0.54  % (26225)------------------------------
% 0.22/0.54  % (26216)Success in time 0.173 s
%------------------------------------------------------------------------------
