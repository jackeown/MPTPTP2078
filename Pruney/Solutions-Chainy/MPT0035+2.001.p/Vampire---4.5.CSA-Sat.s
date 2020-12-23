%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:44 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u15,negated_conjecture,(
    sK0 != k3_xboole_0(sK0,sK1) )).

tff(u14,negated_conjecture,(
    r1_tarski(sK0,sK1) )).

tff(u13,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

tff(u12,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.34  % CPULimit   : 60
% 0.21/0.34  % WCLimit    : 600
% 0.21/0.34  % DateTime   : Tue Dec  1 12:46:07 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.41  % (20557)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.45  % (20555)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (20554)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.46  % (20547)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (20547)# SZS output start Saturation.
% 0.21/0.46  tff(u15,negated_conjecture,
% 0.21/0.46      (sK0 != k3_xboole_0(sK0,sK1))).
% 0.21/0.46  
% 0.21/0.46  tff(u14,negated_conjecture,
% 0.21/0.46      r1_tarski(sK0,sK1)).
% 0.21/0.46  
% 0.21/0.46  tff(u13,axiom,
% 0.21/0.46      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u12,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))).
% 0.21/0.46  
% 0.21/0.46  % (20547)# SZS output end Saturation.
% 0.21/0.46  % (20547)------------------------------
% 0.21/0.46  % (20547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20547)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (20547)Memory used [KB]: 10490
% 0.21/0.46  % (20547)Time elapsed: 0.005 s
% 0.21/0.46  % (20547)------------------------------
% 0.21/0.46  % (20547)------------------------------
% 0.21/0.47  % (20541)Success in time 0.11 s
%------------------------------------------------------------------------------
