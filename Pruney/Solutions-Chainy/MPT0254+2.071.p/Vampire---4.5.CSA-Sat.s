%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u45,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) )).

tff(u44,negated_conjecture,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) )).

tff(u43,negated_conjecture,(
    k1_xboole_0 = k5_xboole_0(sK1,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)) )).

tff(u42,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)))
      | v1_xboole_0(X1) ) )).

tff(u41,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)))
      | v1_xboole_0(X0) ) )).

tff(u40,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u39,negated_conjecture,(
    v1_xboole_0(sK1) )).

tff(u38,negated_conjecture,(
    v1_xboole_0(k1_enumset1(sK0,sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (14554)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.41  % (14554)# SZS output start Saturation.
% 0.21/0.41  tff(u45,axiom,
% 0.21/0.41      (![X1, X0] : ((k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)))))).
% 0.21/0.41  
% 0.21/0.41  tff(u44,negated_conjecture,
% 0.21/0.41      (k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))).
% 0.21/0.41  
% 0.21/0.41  tff(u43,negated_conjecture,
% 0.21/0.41      (k1_xboole_0 = k5_xboole_0(sK1,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)))).
% 0.21/0.41  
% 0.21/0.41  tff(u42,axiom,
% 0.21/0.41      (![X1, X0] : ((~v1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1))) | v1_xboole_0(X1))))).
% 0.21/0.41  
% 0.21/0.41  tff(u41,axiom,
% 0.21/0.41      (![X1, X0] : ((~v1_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1))) | v1_xboole_0(X0))))).
% 0.21/0.41  
% 0.21/0.41  tff(u40,axiom,
% 0.21/0.41      v1_xboole_0(k1_xboole_0)).
% 0.21/0.41  
% 0.21/0.41  tff(u39,negated_conjecture,
% 0.21/0.41      v1_xboole_0(sK1)).
% 0.21/0.41  
% 0.21/0.41  tff(u38,negated_conjecture,
% 0.21/0.41      v1_xboole_0(k1_enumset1(sK0,sK0,sK0))).
% 0.21/0.41  
% 0.21/0.41  % (14554)# SZS output end Saturation.
% 0.21/0.41  % (14554)------------------------------
% 0.21/0.41  % (14554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (14554)Termination reason: Satisfiable
% 0.21/0.41  
% 0.21/0.41  % (14554)Memory used [KB]: 10618
% 0.21/0.41  % (14554)Time elapsed: 0.004 s
% 0.21/0.41  % (14554)------------------------------
% 0.21/0.41  % (14554)------------------------------
% 0.21/0.41  % (14544)Success in time 0.058 s
%------------------------------------------------------------------------------
