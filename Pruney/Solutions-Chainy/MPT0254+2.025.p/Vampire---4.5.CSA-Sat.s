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
% DateTime   : Thu Dec  3 12:39:16 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u68,axiom,(
    ! [X1,X0] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) )).

tff(u67,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))) )).

tff(u66,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | v1_xboole_0(X1) ) )).

tff(u65,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) )).

tff(u64,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u63,negated_conjecture,
    ( ~ v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) )).

tff(u62,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (19576)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.13/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.43  % (19576)# SZS output start Saturation.
% 0.20/0.43  tff(u68,axiom,
% 0.20/0.43      (![X1, X0] : ((k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0))))).
% 0.20/0.43  
% 0.20/0.43  tff(u67,negated_conjecture,
% 0.20/0.43      ((~(k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0))))) | (k1_xboole_0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k2_enumset1(sK0,sK0,sK0,sK0)))))).
% 0.20/0.43  
% 0.20/0.43  tff(u66,axiom,
% 0.20/0.43      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0))) | v1_xboole_0(X1))))).
% 0.20/0.43  
% 0.20/0.43  tff(u65,axiom,
% 0.20/0.43      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0))) | v1_xboole_0(X0))))).
% 0.20/0.43  
% 0.20/0.43  tff(u64,axiom,
% 0.20/0.43      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.20/0.43  
% 0.20/0.43  tff(u63,negated_conjecture,
% 0.20/0.43      ((~v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))) | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)))).
% 0.20/0.43  
% 0.20/0.43  tff(u62,negated_conjecture,
% 0.20/0.43      ((~v1_xboole_0(sK1)) | v1_xboole_0(sK1))).
% 0.20/0.43  
% 0.20/0.43  % (19576)# SZS output end Saturation.
% 0.20/0.43  % (19576)------------------------------
% 0.20/0.43  % (19576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (19576)Termination reason: Satisfiable
% 0.20/0.43  
% 0.20/0.43  % (19576)Memory used [KB]: 10618
% 0.20/0.43  % (19576)Time elapsed: 0.005 s
% 0.20/0.43  % (19576)------------------------------
% 0.20/0.43  % (19576)------------------------------
% 0.20/0.43  % (19560)Success in time 0.073 s
%------------------------------------------------------------------------------
