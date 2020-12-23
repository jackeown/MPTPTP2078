%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:39 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u34,negated_conjecture,(
    sK0 != k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )).

tff(u33,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(sK2(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) )).

tff(u32,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ) )).

tff(u31,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X0)
      | k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ) )).

tff(u30,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X0) = X0 ) )).

tff(u29,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u28,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(X2,X2)
      | ~ r1_tarski(X2,X3)
      | k3_xboole_0(X3,X2) = X2 ) )).

tff(u27,axiom,(
    ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) )).

tff(u26,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK2(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) )).

tff(u25,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(sK2(X0,X1,X2),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (7787)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (7780)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (7780)# SZS output start Saturation.
% 0.21/0.43  tff(u34,negated_conjecture,
% 0.21/0.43      (sK0 != k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u33,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((~r1_tarski(sK2(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | (k3_xboole_0(X1,X2) = X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u32,axiom,
% 0.21/0.43      (![X1, X0] : ((~r1_tarski(X0,X0) | (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u31,axiom,
% 0.21/0.43      (![X1, X0] : ((~r1_tarski(X0,X0) | (k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u30,axiom,
% 0.21/0.43      (![X0] : ((~r1_tarski(X0,X0) | (k3_xboole_0(X0,X0) = X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u29,axiom,
% 0.21/0.43      (![X1, X0] : ((~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | (k3_xboole_0(X0,X1) = X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u28,axiom,
% 0.21/0.43      (![X3, X2] : ((~r1_tarski(X2,X2) | ~r1_tarski(X2,X3) | (k3_xboole_0(X3,X2) = X2))))).
% 0.21/0.43  
% 0.21/0.43  tff(u27,axiom,
% 0.21/0.43      (![X1, X0] : (r1_tarski(X0,k2_xboole_0(X0,X1))))).
% 0.21/0.43  
% 0.21/0.43  tff(u26,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((r1_tarski(sK2(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | (k3_xboole_0(X1,X2) = X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u25,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((r1_tarski(sK2(X0,X1,X2),X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | (k3_xboole_0(X1,X2) = X0))))).
% 0.21/0.43  
% 0.21/0.43  % (7780)# SZS output end Saturation.
% 0.21/0.43  % (7780)------------------------------
% 0.21/0.43  % (7780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (7780)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (7780)Memory used [KB]: 10490
% 0.21/0.43  % (7780)Time elapsed: 0.005 s
% 0.21/0.43  % (7780)------------------------------
% 0.21/0.43  % (7780)------------------------------
% 0.21/0.43  % (7784)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (7779)Success in time 0.072 s
%------------------------------------------------------------------------------
