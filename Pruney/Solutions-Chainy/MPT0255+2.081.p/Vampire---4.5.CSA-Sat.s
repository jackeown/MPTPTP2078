%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:45 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u68,axiom,(
    ! [X1,X2] :
      ( k1_xboole_0 != k3_tarski(k2_tarski(X2,X1))
      | k1_xboole_0 = X1 ) )).

tff(u67,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k3_tarski(k2_tarski(X0,X1))
      | k1_xboole_0 = X0 ) )).

tff(u66,negated_conjecture,
    ( ~ ( k1_xboole_0 != k3_tarski(k1_xboole_0) )
    | k1_xboole_0 != k3_tarski(k1_xboole_0) )).

tff(u65,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

tff(u64,axiom,(
    ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) )).

tff(u63,axiom,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

tff(u62,negated_conjecture,(
    k1_xboole_0 = sK2 )).

tff(u61,negated_conjecture,(
    k1_xboole_0 = k2_tarski(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (19489)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.44  % (19474)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.44  % (19474)# SZS output start Saturation.
% 0.20/0.44  tff(u68,axiom,
% 0.20/0.44      (![X1, X2] : (((k1_xboole_0 != k3_tarski(k2_tarski(X2,X1))) | (k1_xboole_0 = X1))))).
% 0.20/0.44  
% 0.20/0.44  tff(u67,axiom,
% 0.20/0.44      (![X1, X0] : (((k1_xboole_0 != k3_tarski(k2_tarski(X0,X1))) | (k1_xboole_0 = X0))))).
% 0.20/0.44  
% 0.20/0.44  tff(u66,negated_conjecture,
% 0.20/0.44      ((~(k1_xboole_0 != k3_tarski(k1_xboole_0))) | (k1_xboole_0 != k3_tarski(k1_xboole_0)))).
% 0.20/0.44  
% 0.20/0.44  tff(u65,axiom,
% 0.20/0.44      (![X0] : ((k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0)))).
% 0.20/0.44  
% 0.20/0.44  tff(u64,axiom,
% 0.20/0.44      (![X1, X0] : ((k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)))))).
% 0.20/0.44  
% 0.20/0.44  tff(u63,axiom,
% 0.20/0.44      (![X0] : ((k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0)))).
% 0.20/0.44  
% 0.20/0.44  tff(u62,negated_conjecture,
% 0.20/0.44      (k1_xboole_0 = sK2)).
% 0.20/0.44  
% 0.20/0.44  tff(u61,negated_conjecture,
% 0.20/0.44      (k1_xboole_0 = k2_tarski(sK0,sK1))).
% 0.20/0.44  
% 0.20/0.44  % (19474)# SZS output end Saturation.
% 0.20/0.44  % (19474)------------------------------
% 0.20/0.44  % (19474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (19474)Termination reason: Satisfiable
% 0.20/0.44  
% 0.20/0.44  % (19474)Memory used [KB]: 6140
% 0.20/0.44  % (19474)Time elapsed: 0.005 s
% 0.20/0.44  % (19474)------------------------------
% 0.20/0.44  % (19474)------------------------------
% 0.20/0.45  % (19471)Success in time 0.099 s
%------------------------------------------------------------------------------
