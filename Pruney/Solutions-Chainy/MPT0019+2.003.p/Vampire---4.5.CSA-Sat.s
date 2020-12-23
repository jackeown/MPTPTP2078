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
% DateTime   : Thu Dec  3 12:29:34 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u54,negated_conjecture,
    ( ~ ( sK1 != k2_xboole_0(sK0,sK1) )
    | sK1 != k2_xboole_0(sK0,sK1) )).

tff(u53,axiom,
    ( ~ ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u52,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) )).

tff(u51,axiom,
    ( ~ ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) )).

tff(u50,axiom,
    ( ~ ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0))
    | ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X1,X0)) )).

tff(u49,axiom,
    ( ~ ! [X1,X0,X2] :
          ( r1_tarski(k2_xboole_0(X0,X2),X1)
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( r1_tarski(k2_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (24733)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.43  % (24733)# SZS output start Saturation.
% 0.22/0.43  tff(u54,negated_conjecture,
% 0.22/0.43      ((~(sK1 != k2_xboole_0(sK0,sK1))) | (sK1 != k2_xboole_0(sK0,sK1)))).
% 0.22/0.43  
% 0.22/0.43  tff(u53,axiom,
% 0.22/0.43      ((~(![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))) | (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)))))).
% 0.22/0.43  
% 0.22/0.43  tff(u52,negated_conjecture,
% 0.22/0.43      ((~r1_tarski(sK0,sK1)) | r1_tarski(sK0,sK1))).
% 0.22/0.43  
% 0.22/0.43  tff(u51,axiom,
% 0.22/0.43      ((~(![X1, X0] : (r1_tarski(X0,k2_xboole_0(X0,X1))))) | (![X1, X0] : (r1_tarski(X0,k2_xboole_0(X0,X1)))))).
% 0.22/0.43  
% 0.22/0.43  tff(u50,axiom,
% 0.22/0.43      ((~(![X1, X0] : (r1_tarski(X0,k2_xboole_0(X1,X0))))) | (![X1, X0] : (r1_tarski(X0,k2_xboole_0(X1,X0)))))).
% 0.22/0.43  
% 0.22/0.43  tff(u49,axiom,
% 0.22/0.43      ((~(![X1, X0, X2] : ((r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))))).
% 0.22/0.43  
% 0.22/0.43  % (24733)# SZS output end Saturation.
% 0.22/0.43  % (24733)------------------------------
% 0.22/0.43  % (24733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (24733)Termination reason: Satisfiable
% 0.22/0.43  
% 0.22/0.43  % (24733)Memory used [KB]: 10490
% 0.22/0.43  % (24733)Time elapsed: 0.004 s
% 0.22/0.43  % (24733)------------------------------
% 0.22/0.43  % (24733)------------------------------
% 0.22/0.44  % (24727)Success in time 0.072 s
%------------------------------------------------------------------------------
