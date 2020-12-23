%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:44 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   62 (  62 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   11 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u76,negated_conjecture,
    ( ~ ( sK0 != k3_xboole_0(sK0,sK1) )
    | sK0 != k3_xboole_0(sK0,sK1) )).

tff(u75,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(sK2(X0,X1,X2),X0)
          | k3_xboole_0(X1,X2) = X0
          | ~ r1_tarski(X0,X2)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(sK2(X0,X1,X2),X0)
        | k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) )).

tff(u74,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(X1,X1)
          | k3_xboole_0(X0,X1) = X1
          | ~ r1_tarski(X1,X0) )
    | ! [X1,X0] :
        ( ~ r1_tarski(X1,X1)
        | k3_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X1,X0) ) )).

tff(u73,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_tarski(X0,X1)
          | k3_xboole_0(X0,X1) = X0
          | ~ r1_tarski(X0,X0) )
    | ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X0) ) )).

tff(u72,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK0) )).

tff(u71,axiom,
    ( ~ ! [X3,X5,X4] :
          ( ~ r1_tarski(sK2(X3,X4,X5),sK2(X3,X4,X5))
          | sK2(X3,X4,X5) = k3_xboole_0(sK2(X3,X4,X5),X4)
          | k3_xboole_0(X4,X5) = X3
          | ~ r1_tarski(X3,X5)
          | ~ r1_tarski(X3,X4) )
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(sK2(X3,X4,X5),sK2(X3,X4,X5))
        | sK2(X3,X4,X5) = k3_xboole_0(sK2(X3,X4,X5),X4)
        | k3_xboole_0(X4,X5) = X3
        | ~ r1_tarski(X3,X5)
        | ~ r1_tarski(X3,X4) ) )).

tff(u70,axiom,
    ( ~ ! [X1,X0,X2] :
          ( ~ r1_tarski(sK2(X0,X1,X2),sK2(X0,X1,X2))
          | sK2(X0,X1,X2) = k3_xboole_0(sK2(X0,X1,X2),X2)
          | k3_xboole_0(X1,X2) = X0
          | ~ r1_tarski(X0,X2)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(sK2(X0,X1,X2),sK2(X0,X1,X2))
        | sK2(X0,X1,X2) = k3_xboole_0(sK2(X0,X1,X2),X2)
        | k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) )).

tff(u69,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) )).

tff(u68,axiom,
    ( ~ ! [X1,X0,X2] :
          ( r1_tarski(sK2(X0,X1,X2),X2)
          | k3_xboole_0(X1,X2) = X0
          | ~ r1_tarski(X0,X2)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( r1_tarski(sK2(X0,X1,X2),X2)
        | k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) )).

tff(u67,axiom,
    ( ~ ! [X1,X0,X2] :
          ( r1_tarski(sK2(X0,X1,X2),X1)
          | k3_xboole_0(X1,X2) = X0
          | ~ r1_tarski(X0,X2)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X0,X2] :
        ( r1_tarski(sK2(X0,X1,X2),X1)
        | k3_xboole_0(X1,X2) = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (22300)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.41  % (22298)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (22302)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (22302)# SZS output start Saturation.
% 0.21/0.43  tff(u76,negated_conjecture,
% 0.21/0.43      ((~(sK0 != k3_xboole_0(sK0,sK1))) | (sK0 != k3_xboole_0(sK0,sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u75,axiom,
% 0.21/0.43      ((~(![X1, X0, X2] : ((~r1_tarski(sK2(X0,X1,X2),X0) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((~r1_tarski(sK2(X0,X1,X2),X0) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u74,axiom,
% 0.21/0.43      ((~(![X1, X0] : ((~r1_tarski(X1,X1) | (k3_xboole_0(X0,X1) = X1) | ~r1_tarski(X1,X0))))) | (![X1, X0] : ((~r1_tarski(X1,X1) | (k3_xboole_0(X0,X1) = X1) | ~r1_tarski(X1,X0)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u73,axiom,
% 0.21/0.43      ((~(![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0) | ~r1_tarski(X0,X0))))) | (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0) | ~r1_tarski(X0,X0)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u72,negated_conjecture,
% 0.21/0.43      ((~~r1_tarski(sK0,sK0)) | ~r1_tarski(sK0,sK0))).
% 0.21/0.43  
% 0.21/0.43  tff(u71,axiom,
% 0.21/0.43      ((~(![X3, X5, X4] : ((~r1_tarski(sK2(X3,X4,X5),sK2(X3,X4,X5)) | (sK2(X3,X4,X5) = k3_xboole_0(sK2(X3,X4,X5),X4)) | (k3_xboole_0(X4,X5) = X3) | ~r1_tarski(X3,X5) | ~r1_tarski(X3,X4))))) | (![X3, X5, X4] : ((~r1_tarski(sK2(X3,X4,X5),sK2(X3,X4,X5)) | (sK2(X3,X4,X5) = k3_xboole_0(sK2(X3,X4,X5),X4)) | (k3_xboole_0(X4,X5) = X3) | ~r1_tarski(X3,X5) | ~r1_tarski(X3,X4)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u70,axiom,
% 0.21/0.43      ((~(![X1, X0, X2] : ((~r1_tarski(sK2(X0,X1,X2),sK2(X0,X1,X2)) | (sK2(X0,X1,X2) = k3_xboole_0(sK2(X0,X1,X2),X2)) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((~r1_tarski(sK2(X0,X1,X2),sK2(X0,X1,X2)) | (sK2(X0,X1,X2) = k3_xboole_0(sK2(X0,X1,X2),X2)) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u69,negated_conjecture,
% 0.21/0.43      ((~r1_tarski(sK0,sK1)) | r1_tarski(sK0,sK1))).
% 0.21/0.43  
% 0.21/0.43  tff(u68,axiom,
% 0.21/0.43      ((~(![X1, X0, X2] : ((r1_tarski(sK2(X0,X1,X2),X2) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((r1_tarski(sK2(X0,X1,X2),X2) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u67,axiom,
% 0.21/0.43      ((~(![X1, X0, X2] : ((r1_tarski(sK2(X0,X1,X2),X1) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))) | (![X1, X0, X2] : ((r1_tarski(sK2(X0,X1,X2),X1) | (k3_xboole_0(X1,X2) = X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))))).
% 0.21/0.43  
% 0.21/0.43  % (22302)# SZS output end Saturation.
% 0.21/0.43  % (22302)------------------------------
% 0.21/0.43  % (22302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (22302)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (22302)Memory used [KB]: 6140
% 0.21/0.43  % (22302)Time elapsed: 0.025 s
% 0.21/0.43  % (22302)------------------------------
% 0.21/0.43  % (22302)------------------------------
% 0.21/0.43  % (22291)Success in time 0.074 s
%------------------------------------------------------------------------------
