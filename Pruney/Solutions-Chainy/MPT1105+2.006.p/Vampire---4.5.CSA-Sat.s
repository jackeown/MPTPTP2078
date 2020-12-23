%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:04 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u25,negated_conjecture,(
    k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) )).

tff(u24,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u23,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u22,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) )).

tff(u21,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.39  % (13453)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.39  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.39  % (13453)# SZS output start Saturation.
% 0.20/0.39  tff(u25,negated_conjecture,
% 0.20/0.39      (k2_struct_0(sK0) != k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)))).
% 0.20/0.39  
% 0.20/0.39  tff(u24,axiom,
% 0.20/0.39      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.39  
% 0.20/0.39  tff(u23,axiom,
% 0.20/0.39      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.20/0.39  
% 0.20/0.39  tff(u22,axiom,
% 0.20/0.39      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)))))).
% 0.20/0.39  
% 0.20/0.39  tff(u21,axiom,
% 0.20/0.39      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.20/0.39  
% 0.20/0.39  % (13453)# SZS output end Saturation.
% 0.20/0.39  % (13453)------------------------------
% 0.20/0.39  % (13453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.39  % (13453)Termination reason: Satisfiable
% 0.20/0.39  
% 0.20/0.39  % (13453)Memory used [KB]: 6012
% 0.20/0.39  % (13453)Time elapsed: 0.002 s
% 0.20/0.39  % (13453)------------------------------
% 0.20/0.39  % (13453)------------------------------
% 0.20/0.39  % (13447)Success in time 0.039 s
%------------------------------------------------------------------------------
