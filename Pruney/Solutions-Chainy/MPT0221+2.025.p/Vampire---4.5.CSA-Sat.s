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
% DateTime   : Thu Dec  3 12:35:48 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u71,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u70,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u69,negated_conjecture,
    ( k1_xboole_0 != k3_enumset1(sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

tff(u68,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u67,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u66,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) )).

tff(u65,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (4245)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (4246)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (4246)# SZS output start Saturation.
% 0.21/0.46  tff(u71,axiom,
% 0.21/0.46      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u70,axiom,
% 0.21/0.46      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u69,negated_conjecture,
% 0.21/0.46      ((~(k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | (k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)))).
% 0.21/0.46  
% 0.21/0.46  tff(u68,axiom,
% 0.21/0.46      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.46  
% 0.21/0.46  tff(u67,axiom,
% 0.21/0.46      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u66,axiom,
% 0.21/0.46      (![X1, X0] : ((r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) != X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u65,axiom,
% 0.21/0.46      (![X0] : (r1_xboole_0(X0,k1_xboole_0)))).
% 0.21/0.46  
% 0.21/0.46  % (4246)# SZS output end Saturation.
% 0.21/0.46  % (4246)------------------------------
% 0.21/0.46  % (4246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4246)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (4246)Memory used [KB]: 6140
% 0.21/0.46  % (4246)Time elapsed: 0.032 s
% 0.21/0.46  % (4246)------------------------------
% 0.21/0.46  % (4246)------------------------------
% 0.21/0.46  % (4239)Success in time 0.099 s
%------------------------------------------------------------------------------
