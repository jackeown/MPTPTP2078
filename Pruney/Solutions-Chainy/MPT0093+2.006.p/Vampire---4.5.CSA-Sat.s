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
% DateTime   : Thu Dec  3 12:31:43 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u74,negated_conjecture,
    ( sK0 != k4_xboole_0(sK0,sK2)
    | sK0 = k4_xboole_0(sK0,sK2) )).

tff(u73,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) )).

tff(u72,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,sK2) )).

tff(u71,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) )).

tff(u70,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( r1_tarski(sK0,k4_xboole_0(X0,X1))
          | ~ r1_tarski(X1,sK2)
          | ~ r1_tarski(sK0,X0) )
    | ! [X1,X0] :
        ( r1_tarski(sK0,k4_xboole_0(X0,X1))
        | ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(sK0,X0) ) )).

tff(u69,axiom,
    ( ~ ! [X1,X3,X0,X2] :
          ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X1) )
    | ! [X1,X3,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) )).

tff(u68,negated_conjecture,
    ( ~ ! [X1,X0] :
          ( r1_tarski(k4_xboole_0(X0,X1),sK0)
          | ~ r1_tarski(sK2,X1)
          | ~ r1_tarski(X0,sK0) )
    | ! [X1,X0] :
        ( r1_tarski(k4_xboole_0(X0,X1),sK0)
        | ~ r1_tarski(sK2,X1)
        | ~ r1_tarski(X0,sK0) ) )).

tff(u67,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_xboole_0(X0,X1)
          | k4_xboole_0(X0,X1) = X0 )
    | ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 ) )).

tff(u66,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,sK2) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (5602)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (5600)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (5601)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (5596)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (5596)Refutation not found, incomplete strategy% (5596)------------------------------
% 0.20/0.43  % (5596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (5596)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (5596)Memory used [KB]: 10490
% 0.20/0.43  % (5596)Time elapsed: 0.004 s
% 0.20/0.43  % (5596)------------------------------
% 0.20/0.43  % (5596)------------------------------
% 0.20/0.44  % (5605)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.44  % (5605)# SZS output start Saturation.
% 0.20/0.44  tff(u74,negated_conjecture,
% 0.20/0.44      ((~(sK0 = k4_xboole_0(sK0,sK2))) | (sK0 = k4_xboole_0(sK0,sK2)))).
% 0.20/0.44  
% 0.20/0.44  tff(u73,negated_conjecture,
% 0.20/0.44      ((~~r1_tarski(sK0,k4_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)))).
% 0.20/0.44  
% 0.20/0.44  tff(u72,negated_conjecture,
% 0.20/0.44      ((~~r1_tarski(sK2,sK2)) | ~r1_tarski(sK2,sK2))).
% 0.20/0.44  
% 0.20/0.44  tff(u71,negated_conjecture,
% 0.20/0.44      ((~r1_tarski(sK0,sK1)) | r1_tarski(sK0,sK1))).
% 0.20/0.44  
% 0.20/0.44  tff(u70,negated_conjecture,
% 0.20/0.44      ((~(![X1, X0] : ((r1_tarski(sK0,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,sK2) | ~r1_tarski(sK0,X0))))) | (![X1, X0] : ((r1_tarski(sK0,k4_xboole_0(X0,X1)) | ~r1_tarski(X1,sK2) | ~r1_tarski(sK0,X0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u69,axiom,
% 0.20/0.44      ((~(![X1, X3, X0, X2] : ((r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))))) | (![X1, X3, X0, X2] : ((r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u68,negated_conjecture,
% 0.20/0.44      ((~(![X1, X0] : ((r1_tarski(k4_xboole_0(X0,X1),sK0) | ~r1_tarski(sK2,X1) | ~r1_tarski(X0,sK0))))) | (![X1, X0] : ((r1_tarski(k4_xboole_0(X0,X1),sK0) | ~r1_tarski(sK2,X1) | ~r1_tarski(X0,sK0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u67,axiom,
% 0.20/0.44      ((~(![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))) | (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u66,negated_conjecture,
% 0.20/0.44      ((~r1_xboole_0(sK0,sK2)) | r1_xboole_0(sK0,sK2))).
% 0.20/0.44  
% 0.20/0.44  % (5605)# SZS output end Saturation.
% 0.20/0.44  % (5605)------------------------------
% 0.20/0.44  % (5605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (5605)Termination reason: Satisfiable
% 0.20/0.44  
% 0.20/0.44  % (5605)Memory used [KB]: 6012
% 0.20/0.44  % (5605)Time elapsed: 0.035 s
% 0.20/0.44  % (5605)------------------------------
% 0.20/0.44  % (5605)------------------------------
% 0.20/0.44  % (5594)Success in time 0.084 s
%------------------------------------------------------------------------------
