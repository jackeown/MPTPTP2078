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
% DateTime   : Thu Dec  3 12:31:48 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u25,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) )).

tff(u24,negated_conjecture,
    ( ~ ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) )
    | k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) )).

tff(u23,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u22,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (24387)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.42  % (24387)Refutation not found, incomplete strategy% (24387)------------------------------
% 0.20/0.42  % (24387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (24387)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (24387)Memory used [KB]: 10490
% 0.20/0.42  % (24387)Time elapsed: 0.003 s
% 0.20/0.42  % (24387)------------------------------
% 0.20/0.42  % (24387)------------------------------
% 0.21/0.45  % (24393)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.45  % (24393)# SZS output start Saturation.
% 0.21/0.45  tff(u25,axiom,
% 0.21/0.45      (![X1, X0] : (((k4_xboole_0(X0,X1) != k1_xboole_0) | r1_tarski(X0,X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u24,negated_conjecture,
% 0.21/0.45      ((~(k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)))) | (k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u23,axiom,
% 0.21/0.45      (![X1, X0] : ((~r1_tarski(X0,X1) | (k4_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u22,axiom,
% 0.21/0.45      (![X1, X0] : ((~r1_tarski(X0,X1) | (k2_xboole_0(X0,X1) = X1))))).
% 0.21/0.45  
% 0.21/0.45  % (24393)# SZS output end Saturation.
% 0.21/0.45  % (24393)------------------------------
% 0.21/0.45  % (24393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (24393)Termination reason: Satisfiable
% 0.21/0.45  
% 0.21/0.45  % (24393)Memory used [KB]: 10490
% 0.21/0.45  % (24393)Time elapsed: 0.042 s
% 0.21/0.45  % (24393)------------------------------
% 0.21/0.45  % (24393)------------------------------
% 0.21/0.45  % (24374)Success in time 0.094 s
%------------------------------------------------------------------------------
