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
% DateTime   : Thu Dec  3 12:29:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    3 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u18,negated_conjecture,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )).

tff(u17,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) )).

tff(u16,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) )).

tff(u15,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (23361)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (23358)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (23356)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (23366)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.44  % (23366)# SZS output start Saturation.
% 0.21/0.44  tff(u18,negated_conjecture,
% 0.21/0.44      (k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))).
% 0.21/0.44  
% 0.21/0.44  tff(u17,axiom,
% 0.21/0.44      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1))))).
% 0.21/0.44  
% 0.21/0.44  tff(u16,axiom,
% 0.21/0.44      (![X1, X0] : ((k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)))))).
% 0.21/0.44  
% 0.21/0.44  tff(u15,axiom,
% 0.21/0.44      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 0.21/0.44  
% 0.21/0.44  % (23366)# SZS output end Saturation.
% 0.21/0.44  % (23366)------------------------------
% 0.21/0.44  % (23366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (23366)Termination reason: Satisfiable
% 0.21/0.44  
% 0.21/0.44  % (23366)Memory used [KB]: 10490
% 0.21/0.44  % (23366)Time elapsed: 0.004 s
% 0.21/0.44  % (23366)------------------------------
% 0.21/0.44  % (23366)------------------------------
% 0.21/0.44  % (23354)Success in time 0.082 s
%------------------------------------------------------------------------------
