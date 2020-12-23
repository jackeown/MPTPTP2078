%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:40 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   33 (  33 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u201,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u200,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 )).

tff(u199,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_subset_1(X1,X1,X2) )).

tff(u198,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u197,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u196,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u195,negated_conjecture,(
    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u194,negated_conjecture,(
    k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

tff(u193,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u192,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u191,negated_conjecture,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) )).

tff(u190,negated_conjecture,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u189,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u188,axiom,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 )).

tff(u187,negated_conjecture,(
    sK1 = k1_setfam_1(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) )).

tff(u186,negated_conjecture,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u185,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5) ) )).

tff(u184,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u183,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) )).

tff(u182,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) )).

tff(u181,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u180,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u179,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u178,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u177,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u176,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u175,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) )).

tff(u174,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u173,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u172,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u171,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u170,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u169,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (16979)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (16979)# SZS output start Saturation.
% 0.21/0.47  tff(u201,negated_conjecture,
% 0.21/0.47      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u200,axiom,
% 0.21/0.47      (![X0] : ((k5_xboole_0(X0,X0) = k1_xboole_0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u199,axiom,
% 0.21/0.47      (![X1, X2] : ((k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u198,axiom,
% 0.21/0.47      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u197,negated_conjecture,
% 0.21/0.47      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u196,negated_conjecture,
% 0.21/0.47      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u195,negated_conjecture,
% 0.21/0.47      (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u194,negated_conjecture,
% 0.21/0.47      (k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u193,axiom,
% 0.21/0.47      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u192,axiom,
% 0.21/0.47      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u191,negated_conjecture,
% 0.21/0.47      (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k1_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u190,negated_conjecture,
% 0.21/0.47      (k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u189,negated_conjecture,
% 0.21/0.47      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u188,axiom,
% 0.21/0.47      (![X0] : ((k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u187,negated_conjecture,
% 0.21/0.47      (sK1 = k1_setfam_1(k1_enumset1(sK1,sK1,u1_struct_0(sK0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u186,negated_conjecture,
% 0.21/0.47      (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u185,axiom,
% 0.21/0.47      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u184,axiom,
% 0.21/0.47      (![X1, X2] : ((~r1_tarski(X2,X1) | (k3_subset_1(X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u183,axiom,
% 0.21/0.47      (![X1, X2] : ((~r1_tarski(X2,X1) | (k3_subset_1(X1,k3_subset_1(X1,X2)) = X2))))).
% 0.21/0.47  
% 0.21/0.47  tff(u182,axiom,
% 0.21/0.47      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u181,axiom,
% 0.21/0.47      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u180,negated_conjecture,
% 0.21/0.47      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u179,negated_conjecture,
% 0.21/0.47      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u178,axiom,
% 0.21/0.47      (![X1] : (r1_tarski(X1,X1)))).
% 0.21/0.47  
% 0.21/0.47  tff(u177,negated_conjecture,
% 0.21/0.47      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.47  
% 0.21/0.47  tff(u176,axiom,
% 0.21/0.47      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u175,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u174,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u173,axiom,
% 0.21/0.47      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u172,negated_conjecture,
% 0.21/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u171,axiom,
% 0.21/0.47      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u170,axiom,
% 0.21/0.47      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.47  
% 0.21/0.47  tff(u169,negated_conjecture,
% 0.21/0.47      l1_struct_0(sK0)).
% 0.21/0.47  
% 0.21/0.47  % (16979)# SZS output end Saturation.
% 0.21/0.47  % (16979)------------------------------
% 0.21/0.47  % (16979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16979)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (16979)Memory used [KB]: 10746
% 0.21/0.47  % (16979)Time elapsed: 0.080 s
% 0.21/0.47  % (16979)------------------------------
% 0.21/0.47  % (16979)------------------------------
% 0.21/0.48  % (16970)Success in time 0.118 s
%------------------------------------------------------------------------------
