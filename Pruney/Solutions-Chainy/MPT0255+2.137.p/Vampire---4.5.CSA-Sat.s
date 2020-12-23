%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:52 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u27,negated_conjecture,(
    k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)) )).

tff(u26,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | v1_xboole_0(X0) ) )).

tff(u25,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u24,negated_conjecture,(
    v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:21:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (20514)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (20506)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (20517)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (20507)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (20516)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (20503)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (20507)Refutation not found, incomplete strategy% (20507)------------------------------
% 0.21/0.47  % (20507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20507)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20507)Memory used [KB]: 6012
% 0.21/0.47  % (20507)Time elapsed: 0.047 s
% 0.21/0.47  % (20507)------------------------------
% 0.21/0.47  % (20507)------------------------------
% 0.21/0.47  % (20504)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (20506)Refutation not found, incomplete strategy% (20506)------------------------------
% 0.21/0.47  % (20506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20506)Memory used [KB]: 1535
% 0.21/0.47  % (20506)Time elapsed: 0.060 s
% 0.21/0.47  % (20506)------------------------------
% 0.21/0.47  % (20506)------------------------------
% 0.21/0.48  % (20509)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (20514)Refutation not found, incomplete strategy% (20514)------------------------------
% 0.21/0.48  % (20514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (20514)Memory used [KB]: 10490
% 0.21/0.48  % (20514)Time elapsed: 0.063 s
% 0.21/0.48  % (20514)------------------------------
% 0.21/0.48  % (20514)------------------------------
% 0.21/0.48  % (20508)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (20508)Refutation not found, incomplete strategy% (20508)------------------------------
% 0.21/0.48  % (20508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (20508)Memory used [KB]: 6140
% 0.21/0.48  % (20508)Time elapsed: 0.060 s
% 0.21/0.48  % (20508)------------------------------
% 0.21/0.48  % (20508)------------------------------
% 0.21/0.48  % (20518)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (20520)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (20513)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (20510)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (20517)# SZS output start Saturation.
% 0.21/0.48  tff(u27,negated_conjecture,
% 0.21/0.48      (k1_xboole_0 = k3_tarski(k2_enumset1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1),sK2)))).
% 0.21/0.48  
% 0.21/0.48  tff(u26,axiom,
% 0.21/0.48      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1))) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u25,axiom,
% 0.21/0.48      v1_xboole_0(k1_xboole_0)).
% 0.21/0.48  
% 0.21/0.48  tff(u24,negated_conjecture,
% 0.21/0.48      v1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1))).
% 0.21/0.48  
% 0.21/0.48  % (20517)# SZS output end Saturation.
% 0.21/0.48  % (20517)------------------------------
% 0.21/0.48  % (20517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20517)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (20517)Memory used [KB]: 6012
% 0.21/0.48  % (20517)Time elapsed: 0.004 s
% 0.21/0.48  % (20517)------------------------------
% 0.21/0.48  % (20517)------------------------------
% 0.21/0.48  % (20502)Success in time 0.123 s
%------------------------------------------------------------------------------
