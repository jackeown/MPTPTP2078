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
% DateTime   : Thu Dec  3 12:39:16 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u60,axiom,(
    ! [X1,X0] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) )).

tff(u59,negated_conjecture,(
    k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )).

tff(u58,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
      | v1_xboole_0(X1) ) )).

tff(u57,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) )).

tff(u56,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u55,negated_conjecture,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK1) )).

tff(u54,negated_conjecture,
    ( ~ v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:13:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (15530)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.45  % (15524)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.45  % (15524)# SZS output start Saturation.
% 0.21/0.45  tff(u60,axiom,
% 0.21/0.45      (![X1, X0] : ((k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u59,negated_conjecture,
% 0.21/0.45      (k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u58,axiom,
% 0.21/0.45      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X1))))).
% 0.21/0.45  
% 0.21/0.45  tff(u57,axiom,
% 0.21/0.45      (![X1, X0] : ((~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X0))))).
% 0.21/0.45  
% 0.21/0.45  tff(u56,axiom,
% 0.21/0.45      v1_xboole_0(k1_xboole_0)).
% 0.21/0.45  
% 0.21/0.45  tff(u55,negated_conjecture,
% 0.21/0.45      ((~v1_xboole_0(sK1)) | v1_xboole_0(sK1))).
% 0.21/0.45  
% 0.21/0.45  tff(u54,negated_conjecture,
% 0.21/0.45      ((~v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))).
% 0.21/0.45  
% 0.21/0.45  % (15524)# SZS output end Saturation.
% 0.21/0.45  % (15524)------------------------------
% 0.21/0.45  % (15524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (15524)Termination reason: Satisfiable
% 0.21/0.45  
% 0.21/0.45  % (15524)Memory used [KB]: 6140
% 0.21/0.45  % (15524)Time elapsed: 0.003 s
% 0.21/0.45  % (15524)------------------------------
% 0.21/0.45  % (15524)------------------------------
% 0.21/0.46  % (15521)Success in time 0.093 s
%------------------------------------------------------------------------------
