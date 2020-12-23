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
% DateTime   : Thu Dec  3 12:29:34 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u28,negated_conjecture,(
    sK1 != k2_xboole_0(sK0,sK1) )).

tff(u27,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u26,negated_conjecture,(
    r1_tarski(sK0,sK1) )).

tff(u25,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u24,axiom,(
    ! [X1,X0] :
      ( r1_tarski(X0,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X0,X1) ) )).

tff(u23,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) )).

tff(u22,axiom,(
    ! [X1,X0] :
      ( r1_tarski(k2_xboole_0(X1,X0),X0)
      | ~ r1_tarski(X1,X0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n025.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:37:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.41  % (17391)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.41  % (17391)# SZS output start Saturation.
% 0.21/0.41  tff(u28,negated_conjecture,
% 0.21/0.41      (sK1 != k2_xboole_0(sK0,sK1))).
% 0.21/0.41  
% 0.21/0.41  tff(u27,axiom,
% 0.21/0.41      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 0.21/0.41  
% 0.21/0.41  tff(u26,negated_conjecture,
% 0.21/0.41      r1_tarski(sK0,sK1)).
% 0.21/0.41  
% 0.21/0.41  tff(u25,axiom,
% 0.21/0.41      (![X1, X0, X2] : ((r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u24,axiom,
% 0.21/0.41      (![X1, X0] : ((r1_tarski(X0,k2_xboole_0(X1,X0)) | ~r1_tarski(X0,X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u23,axiom,
% 0.21/0.41      (![X1, X0, X2] : ((r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u22,axiom,
% 0.21/0.41      (![X1, X0] : ((r1_tarski(k2_xboole_0(X1,X0),X0) | ~r1_tarski(X1,X0))))).
% 0.21/0.41  
% 0.21/0.41  % (17391)# SZS output end Saturation.
% 0.21/0.41  % (17391)------------------------------
% 0.21/0.41  % (17391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (17391)Termination reason: Satisfiable
% 0.21/0.41  
% 0.21/0.41  % (17391)Memory used [KB]: 10490
% 0.21/0.41  % (17391)Time elapsed: 0.003 s
% 0.21/0.41  % (17391)------------------------------
% 0.21/0.41  % (17391)------------------------------
% 0.21/0.42  % (17379)Success in time 0.057 s
%------------------------------------------------------------------------------
