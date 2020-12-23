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
% DateTime   : Thu Dec  3 12:29:39 EST 2020

% Result     : CounterSatisfiable 0.18s
% Output     : Saturation 0.18s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u16,negated_conjecture,(
    sK0 != k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )).

tff(u15,axiom,(
    ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) )).

tff(u14,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) )).

tff(u13,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:03:45 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.18/0.39  % (23755)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.18/0.41  % (23753)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.18/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.18/0.41  % (23753)# SZS output start Saturation.
% 0.18/0.41  tff(u16,negated_conjecture,
% 0.18/0.41      (sK0 != k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)))).
% 0.18/0.41  
% 0.18/0.41  tff(u15,axiom,
% 0.18/0.41      (![X1, X0] : (r1_tarski(X0,k2_xboole_0(X0,X1))))).
% 0.18/0.41  
% 0.18/0.41  tff(u14,axiom,
% 0.18/0.41      (![X1, X0, X2] : ((r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))).
% 0.18/0.41  
% 0.18/0.41  tff(u13,axiom,
% 0.18/0.41      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))).
% 0.18/0.41  
% 0.18/0.41  % (23753)# SZS output end Saturation.
% 0.18/0.41  % (23753)------------------------------
% 0.18/0.41  % (23753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.41  % (23753)Termination reason: Satisfiable
% 0.18/0.41  
% 0.18/0.41  % (23753)Memory used [KB]: 10490
% 0.18/0.41  % (23753)Time elapsed: 0.003 s
% 0.18/0.41  % (23753)------------------------------
% 0.18/0.41  % (23753)------------------------------
% 0.18/0.41  % (23752)Success in time 0.084 s
%------------------------------------------------------------------------------
