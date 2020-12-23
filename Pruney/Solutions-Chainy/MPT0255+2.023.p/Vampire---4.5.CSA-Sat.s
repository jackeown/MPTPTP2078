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
% DateTime   : Thu Dec  3 12:39:37 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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
tff(u64,axiom,(
    ! [X1,X0] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) )).

tff(u63,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1)))
    | k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))) )).

tff(u62,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | v1_xboole_0(X1) ) )).

tff(u61,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) )).

tff(u60,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u59,negated_conjecture,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK2) )).

tff(u58,negated_conjecture,
    ( ~ v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1))
    | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:37:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19522)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (19522)Refutation not found, incomplete strategy% (19522)------------------------------
% 0.22/0.46  % (19522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (19522)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (19522)Memory used [KB]: 6140
% 0.22/0.46  % (19522)Time elapsed: 0.042 s
% 0.22/0.46  % (19522)------------------------------
% 0.22/0.46  % (19522)------------------------------
% 0.22/0.47  % (19523)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (19524)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (19523)Refutation not found, incomplete strategy% (19523)------------------------------
% 0.22/0.47  % (19523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19523)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (19523)Memory used [KB]: 6140
% 0.22/0.47  % (19523)Time elapsed: 0.052 s
% 0.22/0.47  % (19523)------------------------------
% 0.22/0.47  % (19523)------------------------------
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (19524)# SZS output start Saturation.
% 0.22/0.47  tff(u64,axiom,
% 0.22/0.47      (![X1, X0] : ((k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u63,negated_conjecture,
% 0.22/0.47      ((~(k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1))))) | (k1_xboole_0 = k3_tarski(k2_enumset1(sK2,sK2,sK2,k2_enumset1(sK0,sK0,sK0,sK1)))))).
% 0.22/0.47  
% 0.22/0.47  tff(u62,axiom,
% 0.22/0.47      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0))) | v1_xboole_0(X1))))).
% 0.22/0.47  
% 0.22/0.47  tff(u61,axiom,
% 0.22/0.47      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0))) | v1_xboole_0(X0))))).
% 0.22/0.47  
% 0.22/0.47  tff(u60,axiom,
% 0.22/0.47      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.22/0.47  
% 0.22/0.47  tff(u59,negated_conjecture,
% 0.22/0.47      ((~v1_xboole_0(sK2)) | v1_xboole_0(sK2))).
% 0.22/0.47  
% 0.22/0.47  tff(u58,negated_conjecture,
% 0.22/0.47      ((~v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1))) | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1)))).
% 0.22/0.47  
% 0.22/0.47  % (19524)# SZS output end Saturation.
% 0.22/0.47  % (19524)------------------------------
% 0.22/0.47  % (19524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19524)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (19524)Memory used [KB]: 6140
% 0.22/0.47  % (19524)Time elapsed: 0.050 s
% 0.22/0.47  % (19524)------------------------------
% 0.22/0.47  % (19524)------------------------------
% 0.22/0.48  % (19517)Success in time 0.114 s
%------------------------------------------------------------------------------
