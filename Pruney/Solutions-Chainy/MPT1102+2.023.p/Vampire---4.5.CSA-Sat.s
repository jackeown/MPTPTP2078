%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:31 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u30,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u32,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u31,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u26,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u29,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )).

cnf(u35,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) )).

cnf(u37,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u20,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u38,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u28,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

cnf(u36,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u19,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (28096)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.43  % (28083)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.44  % (28092)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.44  % (28092)# SZS output start Saturation.
% 0.20/0.44  cnf(u17,negated_conjecture,
% 0.20/0.44      l1_struct_0(sK0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u30,axiom,
% 0.20/0.44      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.44  
% 0.20/0.44  cnf(u18,negated_conjecture,
% 0.20/0.44      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.44  
% 0.20/0.44  cnf(u25,axiom,
% 0.20/0.44      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.20/0.44  
% 0.20/0.44  cnf(u27,axiom,
% 0.20/0.44      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.44  
% 0.20/0.44  cnf(u32,axiom,
% 0.20/0.44      r1_tarski(X0,X0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u31,negated_conjecture,
% 0.20/0.44      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.44  
% 0.20/0.44  cnf(u26,axiom,
% 0.20/0.44      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.20/0.44  
% 0.20/0.44  cnf(u29,axiom,
% 0.20/0.44      ~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0).
% 0.20/0.44  
% 0.20/0.44  cnf(u35,negated_conjecture,
% 0.20/0.44      sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0)))).
% 0.20/0.44  
% 0.20/0.44  cnf(u37,negated_conjecture,
% 0.20/0.44      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u20,axiom,
% 0.20/0.44      k2_subset_1(X0) = X0).
% 0.20/0.44  
% 0.20/0.44  cnf(u38,axiom,
% 0.20/0.44      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.44  
% 0.20/0.44  cnf(u28,axiom,
% 0.20/0.44      k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))).
% 0.20/0.44  
% 0.20/0.44  cnf(u36,axiom,
% 0.20/0.44      k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0).
% 0.20/0.44  
% 0.20/0.44  cnf(u19,negated_conjecture,
% 0.20/0.44      sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.44  
% 0.20/0.44  % (28092)# SZS output end Saturation.
% 0.20/0.44  % (28092)------------------------------
% 0.20/0.44  % (28092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (28092)Termination reason: Satisfiable
% 0.20/0.44  
% 0.20/0.44  % (28092)Memory used [KB]: 1535
% 0.20/0.44  % (28092)Time elapsed: 0.057 s
% 0.20/0.44  % (28092)------------------------------
% 0.20/0.44  % (28092)------------------------------
% 0.20/0.44  % (28079)Success in time 0.086 s
%------------------------------------------------------------------------------
