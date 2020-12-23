%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:05 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    2 (   2 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u23,negated_conjecture,(
    k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) != k2_yellow_0(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2))) )).

tff(u22,axiom,(
    ! [X1,X0] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (22399)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (22402)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (22397)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (22402)Refutation not found, incomplete strategy% (22402)------------------------------
% 0.22/0.48  % (22402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22402)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (22402)Memory used [KB]: 6140
% 0.22/0.48  % (22402)Time elapsed: 0.005 s
% 0.22/0.48  % (22402)------------------------------
% 0.22/0.48  % (22402)------------------------------
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (22399)# SZS output start Saturation.
% 0.22/0.48  tff(u23,negated_conjecture,
% 0.22/0.48      (k11_lattice3(sK0,k2_yellow_0(sK0,sK1),k2_yellow_0(sK0,sK2)) != k2_yellow_0(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2))))).
% 0.22/0.48  
% 0.22/0.48  tff(u22,axiom,
% 0.22/0.48      (![X1, X0] : ((k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)))))).
% 0.22/0.48  
% 0.22/0.48  % (22399)# SZS output end Saturation.
% 0.22/0.48  % (22399)------------------------------
% 0.22/0.48  % (22399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22399)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (22399)Memory used [KB]: 6012
% 0.22/0.48  % (22399)Time elapsed: 0.051 s
% 0.22/0.48  % (22399)------------------------------
% 0.22/0.48  % (22399)------------------------------
% 0.22/0.48  % (22396)Success in time 0.111 s
%------------------------------------------------------------------------------
