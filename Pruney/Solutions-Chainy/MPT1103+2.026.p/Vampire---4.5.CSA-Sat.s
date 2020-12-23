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
% DateTime   : Thu Dec  3 13:08:37 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 1.32s
% Verified   : 
% Statistics : Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u40,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u32,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u47,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u41,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u42,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u37,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u44,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u59,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u43,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u49,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u23,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u54,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u53,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u24,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u50,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u46,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u25,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u39,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (10164)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (10161)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (10144)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (10144)# SZS output start Saturation.
% 0.21/0.53  cnf(u40,axiom,
% 0.21/0.53      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u22,negated_conjecture,
% 0.21/0.53      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.53  
% 0.21/0.53  cnf(u32,axiom,
% 0.21/0.53      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u47,axiom,
% 0.21/0.53      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.53  
% 0.21/0.53  cnf(u41,negated_conjecture,
% 0.21/0.53      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.53  
% 0.21/0.53  cnf(u42,axiom,
% 0.21/0.53      r1_tarski(X0,X0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u37,axiom,
% 0.21/0.53      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.21/0.53  
% 1.32/0.53  cnf(u44,negated_conjecture,
% 1.32/0.53      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.32/0.53  
% 1.32/0.53  cnf(u59,negated_conjecture,
% 1.32/0.53      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 1.32/0.53  
% 1.32/0.53  cnf(u43,axiom,
% 1.32/0.53      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.32/0.53  
% 1.32/0.53  cnf(u49,negated_conjecture,
% 1.32/0.53      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.32/0.53  
% 1.32/0.53  cnf(u23,axiom,
% 1.32/0.53      k2_subset_1(X0) = X0).
% 1.32/0.53  
% 1.32/0.53  cnf(u54,axiom,
% 1.32/0.53      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.32/0.53  
% 1.32/0.53  cnf(u53,negated_conjecture,
% 1.32/0.53      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 1.32/0.53  
% 1.32/0.53  cnf(u20,negated_conjecture,
% 1.32/0.53      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.32/0.53  
% 1.32/0.53  cnf(u24,axiom,
% 1.32/0.53      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.32/0.53  
% 1.32/0.53  cnf(u50,axiom,
% 1.32/0.53      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 1.32/0.53  
% 1.32/0.53  cnf(u46,axiom,
% 1.32/0.53      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.32/0.53  
% 1.32/0.53  cnf(u25,axiom,
% 1.32/0.53      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.32/0.53  
% 1.32/0.53  cnf(u39,negated_conjecture,
% 1.32/0.53      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.32/0.53  
% 1.32/0.53  % (10144)# SZS output end Saturation.
% 1.32/0.53  % (10144)------------------------------
% 1.32/0.53  % (10144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (10144)Termination reason: Satisfiable
% 1.32/0.53  
% 1.32/0.53  % (10144)Memory used [KB]: 6268
% 1.32/0.53  % (10144)Time elapsed: 0.118 s
% 1.32/0.53  % (10144)------------------------------
% 1.32/0.53  % (10144)------------------------------
% 1.32/0.53  % (10137)Success in time 0.173 s
%------------------------------------------------------------------------------
