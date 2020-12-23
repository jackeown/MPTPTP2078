%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u107,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u106,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k4_xboole_0(X0,X0) = X0 ) )).

tff(u105,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) != X1
      | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) )).

tff(u104,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u103,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u102,negated_conjecture,(
    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

tff(u101,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u100,axiom,
    ( ~ ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ! [X1] : ~ r2_hidden(X1,k1_xboole_0) )).

tff(u99,axiom,(
    ! [X3,X2] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) )).

tff(u98,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) )).

tff(u97,axiom,(
    ! [X1] :
      ( r2_hidden(sK2(X1,X1),X1)
      | r1_xboole_0(X1,X1) ) )).

tff(u96,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) )).

tff(u95,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u94,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))
      | r1_xboole_0(X2,X3) ) )).

tff(u93,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

tff(u92,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) )).

tff(u91,axiom,(
    ! [X1] :
      ( r1_xboole_0(X1,X1)
      | k1_xboole_0 != X1 ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:04:15 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.47  % (11814)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (11814)# SZS output start Saturation.
% 0.22/0.48  tff(u107,axiom,
% 0.22/0.48      (![X1, X0] : (((k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u106,axiom,
% 0.22/0.48      (![X0] : (((k1_xboole_0 != X0) | (k4_xboole_0(X0,X0) = X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u105,axiom,
% 0.22/0.48      (![X1, X2] : (((k4_xboole_0(X1,X2) != X1) | r1_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))))))).
% 0.22/0.48  
% 0.22/0.48  tff(u104,axiom,
% 0.22/0.48      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u103,axiom,
% 0.22/0.48      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u102,negated_conjecture,
% 0.22/0.48      (k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1))).
% 0.22/0.48  
% 0.22/0.48  tff(u101,axiom,
% 0.22/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u100,axiom,
% 0.22/0.48      ((~(![X1] : (~r2_hidden(X1,k1_xboole_0)))) | (![X1] : (~r2_hidden(X1,k1_xboole_0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u99,axiom,
% 0.22/0.48      (![X3, X2] : ((~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u98,axiom,
% 0.22/0.48      (![X1, X0] : ((r2_hidden(sK2(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u97,axiom,
% 0.22/0.48      (![X1] : ((r2_hidden(sK2(X1,X1),X1) | r1_xboole_0(X1,X1))))).
% 0.22/0.48  
% 0.22/0.48  tff(u96,axiom,
% 0.22/0.48      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 0.22/0.48  
% 0.22/0.48  tff(u95,axiom,
% 0.22/0.48      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u94,axiom,
% 0.22/0.48      (![X3, X2] : ((~r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) | r1_xboole_0(X2,X3))))).
% 0.22/0.48  
% 0.22/0.48  tff(u93,axiom,
% 0.22/0.48      (![X0] : (r1_xboole_0(X0,k1_xboole_0)))).
% 0.22/0.48  
% 0.22/0.48  tff(u92,axiom,
% 0.22/0.48      (![X1, X0] : ((r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) != X0))))).
% 0.22/0.48  
% 0.22/0.48  tff(u91,axiom,
% 0.22/0.48      (![X1] : ((r1_xboole_0(X1,X1) | (k1_xboole_0 != X1))))).
% 0.22/0.48  
% 0.22/0.48  % (11814)# SZS output end Saturation.
% 0.22/0.48  % (11814)------------------------------
% 0.22/0.48  % (11814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (11814)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (11814)Memory used [KB]: 6140
% 0.22/0.48  % (11814)Time elapsed: 0.035 s
% 0.22/0.48  % (11814)------------------------------
% 0.22/0.48  % (11814)------------------------------
% 0.22/0.48  % (11811)Success in time 0.11 s
%------------------------------------------------------------------------------
