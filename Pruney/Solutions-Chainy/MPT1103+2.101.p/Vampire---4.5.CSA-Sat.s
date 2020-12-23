%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:47 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u26,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u28,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u27,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u21,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u23,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u20,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )).

cnf(u34,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u14,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u36,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u30,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u37,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u35,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) )).

cnf(u18,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u17,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u15,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

cnf(u24,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:21:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (1249)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (1249)# SZS output start Saturation.
% 0.22/0.47  cnf(u16,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.47  
% 0.22/0.47  cnf(u26,axiom,
% 0.22/0.47      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u22,axiom,
% 0.22/0.47      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u25,axiom,
% 0.22/0.47      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u28,negated_conjecture,
% 0.22/0.47      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u27,axiom,
% 0.22/0.47      r1_tarski(X0,X0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u21,axiom,
% 0.22/0.47      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.22/0.47  
% 0.22/0.47  cnf(u23,axiom,
% 0.22/0.47      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.22/0.47  
% 0.22/0.47  cnf(u20,axiom,
% 0.22/0.47      ~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1).
% 0.22/0.47  
% 0.22/0.47  cnf(u34,axiom,
% 0.22/0.47      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u14,negated_conjecture,
% 0.22/0.47      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u36,negated_conjecture,
% 0.22/0.47      u1_struct_0(sK0) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.22/0.47  
% 0.22/0.47  cnf(u30,axiom,
% 0.22/0.47      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u37,negated_conjecture,
% 0.22/0.47      k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u35,negated_conjecture,
% 0.22/0.47      k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u18,axiom,
% 0.22/0.47      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.47  
% 0.22/0.47  cnf(u17,axiom,
% 0.22/0.47      k2_subset_1(X0) = X0).
% 0.22/0.47  
% 0.22/0.47  cnf(u15,negated_conjecture,
% 0.22/0.47      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u24,axiom,
% 0.22/0.47      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.22/0.47  
% 0.22/0.47  % (1249)# SZS output end Saturation.
% 0.22/0.47  % (1249)------------------------------
% 0.22/0.47  % (1249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (1249)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (1249)Memory used [KB]: 1663
% 0.22/0.47  % (1249)Time elapsed: 0.055 s
% 0.22/0.47  % (1249)------------------------------
% 0.22/0.47  % (1249)------------------------------
% 0.22/0.47  % (1231)Success in time 0.104 s
%------------------------------------------------------------------------------
