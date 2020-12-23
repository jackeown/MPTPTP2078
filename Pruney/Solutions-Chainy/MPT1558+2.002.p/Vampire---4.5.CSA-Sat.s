%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:05 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
tff(u20,negated_conjecture,(
    k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))) )).

tff(u19,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17223)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (17220)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (17225)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (17225)# SZS output start Saturation.
% 0.21/0.46  tff(u20,negated_conjecture,
% 0.21/0.46      (k10_lattice3(sK0,k1_yellow_0(sK0,sK1),k1_yellow_0(sK0,sK2)) != k1_yellow_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK2,sK1))))).
% 0.21/0.46  
% 0.21/0.46  tff(u19,axiom,
% 0.21/0.46      (![X1, X0] : ((k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)))))).
% 0.21/0.46  
% 0.21/0.46  % (17225)# SZS output end Saturation.
% 0.21/0.46  % (17225)------------------------------
% 0.21/0.46  % (17225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (17225)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (17225)Memory used [KB]: 6012
% 0.21/0.46  % (17225)Time elapsed: 0.051 s
% 0.21/0.46  % (17225)------------------------------
% 0.21/0.46  % (17225)------------------------------
% 0.21/0.46  % (17236)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (17227)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17216)Success in time 0.111 s
%------------------------------------------------------------------------------
