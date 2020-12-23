%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:34 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u64,negated_conjecture,(
    sK1 != k2_xboole_0(sK0,sK1) )).

tff(u63,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u62,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u61,negated_conjecture,(
    r1_tarski(sK0,sK1) )).

tff(u60,axiom,(
    ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) )).

tff(u59,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X2,X1)) )).

tff(u58,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

% (22233)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
tff(u57,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) )).

tff(u56,axiom,(
    ! [X3,X2,X4] :
      ( r1_tarski(k2_xboole_0(X3,X2),k2_xboole_0(X4,X3))
      | ~ r1_tarski(X2,X4) ) )).

tff(u55,axiom,(
    ! [X3,X2,X4] :
      ( r1_tarski(k2_xboole_0(X4,X3),k2_xboole_0(X3,X2))
      | ~ r1_tarski(X4,X2) ) )).

tff(u54,axiom,(
    ! [X3,X2,X4] :
      ( r1_tarski(k2_xboole_0(X3,X4),k2_xboole_0(X3,X2))
      | ~ r1_tarski(X4,X2) ) )).

tff(u53,axiom,(
    ! [X1,X0] :
      ( r1_tarski(k2_xboole_0(X1,X0),X0)
      | ~ r1_tarski(X1,X0) ) )).

tff(u52,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(X2,X1),X2)
      | ~ r1_tarski(X1,X2) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (22227)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.41  % (22232)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (22235)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.41  % (22227)# SZS output start Saturation.
% 0.21/0.41  tff(u64,negated_conjecture,
% 0.21/0.41      (sK1 != k2_xboole_0(sK0,sK1))).
% 0.21/0.41  
% 0.21/0.41  tff(u63,axiom,
% 0.21/0.41      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 0.21/0.41  
% 0.21/0.41  tff(u62,axiom,
% 0.21/0.41      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 0.21/0.41  
% 0.21/0.41  tff(u61,negated_conjecture,
% 0.21/0.41      r1_tarski(sK0,sK1)).
% 0.21/0.41  
% 0.21/0.41  tff(u60,axiom,
% 0.21/0.41      (![X1, X0] : (r1_tarski(X0,k2_xboole_0(X0,X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u59,axiom,
% 0.21/0.41      (![X1, X2] : (r1_tarski(X1,k2_xboole_0(X2,X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u58,axiom,
% 0.21/0.41      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.41  
% 0.21/0.41  % (22233)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  tff(u57,axiom,
% 0.21/0.41      (![X1, X0, X2] : ((r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u56,axiom,
% 0.21/0.41      (![X3, X2, X4] : ((r1_tarski(k2_xboole_0(X3,X2),k2_xboole_0(X4,X3)) | ~r1_tarski(X2,X4))))).
% 0.21/0.41  
% 0.21/0.41  tff(u55,axiom,
% 0.21/0.41      (![X3, X2, X4] : ((r1_tarski(k2_xboole_0(X4,X3),k2_xboole_0(X3,X2)) | ~r1_tarski(X4,X2))))).
% 0.21/0.41  
% 0.21/0.41  tff(u54,axiom,
% 0.21/0.41      (![X3, X2, X4] : ((r1_tarski(k2_xboole_0(X3,X4),k2_xboole_0(X3,X2)) | ~r1_tarski(X4,X2))))).
% 0.21/0.41  
% 0.21/0.41  tff(u53,axiom,
% 0.21/0.41      (![X1, X0] : ((r1_tarski(k2_xboole_0(X1,X0),X0) | ~r1_tarski(X1,X0))))).
% 0.21/0.41  
% 0.21/0.41  tff(u52,axiom,
% 0.21/0.41      (![X1, X2] : ((r1_tarski(k2_xboole_0(X2,X1),X2) | ~r1_tarski(X1,X2))))).
% 0.21/0.41  
% 0.21/0.41  % (22227)# SZS output end Saturation.
% 0.21/0.41  % (22227)------------------------------
% 0.21/0.41  % (22227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (22227)Termination reason: Satisfiable
% 0.21/0.41  
% 0.21/0.41  % (22227)Memory used [KB]: 10490
% 0.21/0.41  % (22227)Time elapsed: 0.004 s
% 0.21/0.41  % (22227)------------------------------
% 0.21/0.41  % (22227)------------------------------
% 0.21/0.41  % (22226)Success in time 0.059 s
%------------------------------------------------------------------------------
