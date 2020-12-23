%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:31 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u45,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)) )).

tff(u44,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | v1_xboole_0(X0) ) )).

tff(u43,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u42,negated_conjecture,
    ( ~ v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))
    | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (13769)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (13769)# SZS output start Saturation.
% 0.21/0.43  tff(u45,negated_conjecture,
% 0.21/0.43      ((~(k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) | (k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0),sK1))))).
% 0.21/0.43  
% 0.21/0.43  tff(u44,axiom,
% 0.21/0.43      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | v1_xboole_0(X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u43,axiom,
% 0.21/0.43      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.43  
% 0.21/0.43  tff(u42,negated_conjecture,
% 0.21/0.43      ((~v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0))) | v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0)))).
% 0.21/0.43  
% 0.21/0.43  % (13769)# SZS output end Saturation.
% 0.21/0.43  % (13769)------------------------------
% 0.21/0.43  % (13769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (13769)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (13769)Memory used [KB]: 10618
% 0.21/0.43  % (13769)Time elapsed: 0.004 s
% 0.21/0.43  % (13769)------------------------------
% 0.21/0.43  % (13769)------------------------------
% 0.21/0.43  % (13753)Success in time 0.072 s
%------------------------------------------------------------------------------
