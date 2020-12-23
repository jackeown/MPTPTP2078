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
% DateTime   : Thu Dec  3 13:08:33 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u136,negated_conjecture,(
    sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

tff(u135,axiom,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u134,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) )).

tff(u133,negated_conjecture,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

tff(u132,axiom,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) )).

tff(u131,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) )).

tff(u130,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

tff(u129,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u128,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u127,axiom,(
    ! [X0] : k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u126,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u125,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) )).

tff(u124,negated_conjecture,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u123,negated_conjecture,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u122,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_tarski(X4,X3)
      | k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5) ) )).

tff(u121,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,X1)
      | k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) )).

tff(u120,axiom,(
    ! [X1,X2] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) )).

tff(u119,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u118,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u117,axiom,(
    ! [X2] : r1_tarski(X2,X2) )).

tff(u116,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u115,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u114,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) )).

tff(u113,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u112,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u111,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u110,axiom,(
    ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:22:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (3946)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (3950)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.42  % (3946)# SZS output start Saturation.
% 0.20/0.42  tff(u136,negated_conjecture,
% 0.20/0.42      (sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.42  
% 0.20/0.42  tff(u135,axiom,
% 0.20/0.42      (![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))).
% 0.20/0.42  
% 0.20/0.42  tff(u134,axiom,
% 0.20/0.42      (![X3, X2] : ((k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))))))).
% 0.20/0.42  
% 0.20/0.42  tff(u133,negated_conjecture,
% 0.20/0.42      (k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.20/0.42  
% 0.20/0.42  tff(u132,axiom,
% 0.20/0.42      (![X0] : ((k4_xboole_0(X0,X0) = k3_subset_1(X0,X0))))).
% 0.20/0.42  
% 0.20/0.42  tff(u131,axiom,
% 0.20/0.42      (![X1, X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u130,axiom,
% 0.20/0.42      (![X1, X0] : ((k4_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 0.20/0.42  
% 0.20/0.42  tff(u129,axiom,
% 0.20/0.42      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 0.20/0.42  
% 0.20/0.42  tff(u128,axiom,
% 0.20/0.42      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.42  
% 0.20/0.42  tff(u127,axiom,
% 0.20/0.42      (![X0] : ((k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0)))).
% 0.20/0.42  
% 0.20/0.42  tff(u126,negated_conjecture,
% 0.20/0.42      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0))))).
% 0.20/0.42  
% 0.20/0.42  tff(u125,axiom,
% 0.20/0.42      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2))))).
% 0.20/0.42  
% 0.20/0.42  tff(u124,negated_conjecture,
% 0.20/0.42      (sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.20/0.42  
% 0.20/0.42  tff(u123,negated_conjecture,
% 0.20/0.42      (sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.20/0.42  
% 0.20/0.42  tff(u122,axiom,
% 0.20/0.42      (![X3, X5, X4] : ((~r1_tarski(X4,X3) | (k7_subset_1(X3,X4,X5) = k4_xboole_0(X4,X5)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u121,axiom,
% 0.20/0.42      (![X1, X2] : ((~r1_tarski(X2,X1) | (k3_subset_1(X1,k3_subset_1(X1,X2)) = X2))))).
% 0.20/0.42  
% 0.20/0.42  tff(u120,axiom,
% 0.20/0.42      (![X1, X2] : ((~r1_tarski(X2,X1) | (k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u119,axiom,
% 0.20/0.42      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 0.20/0.42  
% 0.20/0.42  tff(u118,negated_conjecture,
% 0.20/0.42      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.42  
% 0.20/0.42  tff(u117,axiom,
% 0.20/0.42      (![X2] : (r1_tarski(X2,X2)))).
% 0.20/0.42  
% 0.20/0.42  tff(u116,axiom,
% 0.20/0.42      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u115,axiom,
% 0.20/0.42      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.20/0.42  
% 0.20/0.42  tff(u114,axiom,
% 0.20/0.42      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u113,negated_conjecture,
% 0.20/0.42      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.42  
% 0.20/0.42  tff(u112,axiom,
% 0.20/0.42      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.42  
% 0.20/0.42  tff(u111,axiom,
% 0.20/0.42      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 0.20/0.42  
% 0.20/0.42  tff(u110,axiom,
% 0.20/0.42      (![X1, X0] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))))).
% 0.20/0.42  
% 0.20/0.42  % (3946)# SZS output end Saturation.
% 0.20/0.42  % (3946)------------------------------
% 0.20/0.42  % (3946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (3946)Termination reason: Satisfiable
% 0.20/0.42  
% 0.20/0.42  % (3946)Memory used [KB]: 6140
% 0.20/0.42  % (3946)Time elapsed: 0.006 s
% 0.20/0.42  % (3946)------------------------------
% 0.20/0.42  % (3946)------------------------------
% 0.20/0.42  % (3941)Success in time 0.063 s
%------------------------------------------------------------------------------
