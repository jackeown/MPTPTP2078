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

% Result     : CounterSatisfiable 0.23s
% Output     : Saturation 0.23s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u38,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u37,negated_conjecture,(
    k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

tff(u36,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u35,negated_conjecture,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:34:37 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.45  % (3340)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.23/0.45  % (3340)# SZS output start Saturation.
% 0.23/0.46  tff(u38,axiom,
% 0.23/0.46      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.23/0.46  
% 0.23/0.46  tff(u37,negated_conjecture,
% 0.23/0.46      (k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1))).
% 0.23/0.46  
% 0.23/0.46  tff(u36,axiom,
% 0.23/0.46      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 0.23/0.46  
% 0.23/0.46  tff(u35,negated_conjecture,
% 0.23/0.46      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.23/0.46  
% 0.23/0.46  % (3340)# SZS output end Saturation.
% 0.23/0.46  % (3340)------------------------------
% 0.23/0.46  % (3340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.46  % (3340)Termination reason: Satisfiable
% 0.23/0.46  
% 0.23/0.46  % (3340)Memory used [KB]: 6012
% 0.23/0.46  % (3340)Time elapsed: 0.005 s
% 0.23/0.46  % (3340)------------------------------
% 0.23/0.46  % (3340)------------------------------
% 0.23/0.46  % (3320)Success in time 0.086 s
%------------------------------------------------------------------------------
