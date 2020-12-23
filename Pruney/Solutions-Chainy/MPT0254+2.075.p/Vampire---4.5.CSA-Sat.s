%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:22 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   15 (  15 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u79,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)) )).

tff(u78,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )).

tff(u77,axiom,(
    ! [X1,X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) )).

tff(u76,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
      | v1_xboole_0(X1) ) )).

tff(u75,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) )).

tff(u74,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u73,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK1) )).

tff(u72,negated_conjecture,
    ( ~ v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:56:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.41  % (8939)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (8939)Refutation not found, incomplete strategy% (8939)------------------------------
% 0.20/0.41  % (8939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (8939)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (8939)Memory used [KB]: 10618
% 0.20/0.41  % (8939)Time elapsed: 0.004 s
% 0.20/0.41  % (8939)------------------------------
% 0.20/0.41  % (8939)------------------------------
% 0.20/0.42  % (8934)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.42  % (8934)# SZS output start Saturation.
% 0.20/0.42  tff(u79,negated_conjecture,
% 0.20/0.42      ((~(k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)))) | (k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))))).
% 0.20/0.42  
% 0.20/0.42  tff(u78,negated_conjecture,
% 0.20/0.42      ((~(k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))) | (k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u77,axiom,
% 0.20/0.42      (![X1, X0] : ((k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))))).
% 0.20/0.42  
% 0.20/0.42  tff(u76,axiom,
% 0.20/0.42      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X1))))).
% 0.20/0.42  
% 0.20/0.42  tff(u75,axiom,
% 0.20/0.42      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X0))))).
% 0.20/0.42  
% 0.20/0.42  tff(u74,axiom,
% 0.20/0.42      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.20/0.42  
% 0.20/0.42  tff(u73,negated_conjecture,
% 0.20/0.42      ((~v1_xboole_0(sK1)) | v1_xboole_0(sK1))).
% 0.20/0.42  
% 0.20/0.42  tff(u72,negated_conjecture,
% 0.20/0.42      ((~v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))).
% 0.20/0.42  
% 0.20/0.42  % (8934)# SZS output end Saturation.
% 0.20/0.42  % (8934)------------------------------
% 0.20/0.42  % (8934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (8934)Termination reason: Satisfiable
% 0.20/0.42  
% 0.20/0.42  % (8934)Memory used [KB]: 6140
% 0.20/0.42  % (8934)Time elapsed: 0.005 s
% 0.20/0.42  % (8934)------------------------------
% 0.20/0.42  % (8934)------------------------------
% 0.20/0.42  % (8927)Success in time 0.073 s
%------------------------------------------------------------------------------
