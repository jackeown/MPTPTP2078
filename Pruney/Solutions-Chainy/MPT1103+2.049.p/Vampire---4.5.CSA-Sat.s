%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   41 (  41 expanded)
%              Number of equality atoms :   26 (  26 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u54,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u43,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u49,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u56,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u50,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u63,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u48,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u41,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u46,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u68,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u61,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u53,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u34,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u40,axiom,
    ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u32,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u77,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k1_subset_1(X0) )).

cnf(u75,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u71,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u35,axiom,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 )).

cnf(u60,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u38,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u73,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u64,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u39,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u29,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:18:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (31885)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (31908)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (31899)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (31901)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (31891)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (31893)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (31891)# SZS output start Saturation.
% 0.20/0.53  cnf(u54,axiom,
% 0.20/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u28,negated_conjecture,
% 0.20/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.53  
% 0.20/0.53  cnf(u47,axiom,
% 0.20/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u42,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u43,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.20/0.53  
% 0.20/0.53  cnf(u49,axiom,
% 0.20/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u56,negated_conjecture,
% 0.20/0.53      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u50,axiom,
% 0.20/0.53      r1_tarski(X1,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u63,negated_conjecture,
% 0.20/0.53      ~r1_tarski(u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u48,axiom,
% 0.20/0.53      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u41,axiom,
% 0.20/0.53      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u46,axiom,
% 0.20/0.53      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u68,negated_conjecture,
% 0.20/0.53      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u61,negated_conjecture,
% 0.20/0.53      sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u72,negated_conjecture,
% 0.20/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u53,axiom,
% 0.20/0.53      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u34,axiom,
% 0.20/0.53      k2_subset_1(X0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u40,axiom,
% 0.20/0.53      k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u32,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u77,axiom,
% 0.20/0.53      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u33,axiom,
% 0.20/0.53      k1_xboole_0 = k1_subset_1(X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u75,axiom,
% 0.20/0.53      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u71,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,axiom,
% 0.20/0.53      k5_xboole_0(X0,X0) = k1_xboole_0).
% 0.20/0.53  
% 0.20/0.53  cnf(u60,axiom,
% 0.20/0.53      k3_xboole_0(X0,X0) = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u38,axiom,
% 0.20/0.53      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u73,axiom,
% 0.20/0.53      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.53  
% 0.20/0.53  cnf(u64,negated_conjecture,
% 0.20/0.53      k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u39,axiom,
% 0.20/0.53      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.20/0.53  
% 0.20/0.53  cnf(u29,negated_conjecture,
% 0.20/0.53      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.20/0.53  
% 0.20/0.53  % (31891)# SZS output end Saturation.
% 0.20/0.53  % (31891)------------------------------
% 0.20/0.53  % (31891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (31891)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (31891)Memory used [KB]: 1791
% 0.20/0.53  % (31891)Time elapsed: 0.065 s
% 0.20/0.53  % (31891)------------------------------
% 0.20/0.53  % (31891)------------------------------
% 0.20/0.53  % (31890)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (31880)Success in time 0.168 s
%------------------------------------------------------------------------------
