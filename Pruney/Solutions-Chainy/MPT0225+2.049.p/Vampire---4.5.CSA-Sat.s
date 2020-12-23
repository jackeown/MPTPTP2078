%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:12 EST 2020

% Result     : CounterSatisfiable 0.23s
% Output     : Saturation 0.23s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :    9 (   9 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u44,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 )).

cnf(u45,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )).

cnf(u52,negated_conjecture,
    ( sK0 = sK1 )).

cnf(u55,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )).

cnf(u48,axiom,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | X0 = X1 )).

cnf(u26,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:44:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.52  % (17553)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.23/0.52  % (17552)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.52  % (17552)Refutation not found, incomplete strategy% (17552)------------------------------
% 0.23/0.52  % (17552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (17552)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (17552)Memory used [KB]: 1663
% 0.23/0.52  % (17552)Time elapsed: 0.104 s
% 0.23/0.52  % (17552)------------------------------
% 0.23/0.52  % (17552)------------------------------
% 0.23/0.52  % (17546)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.23/0.52  % (17538)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.52  % (17554)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.23/0.52  % (17554)Refutation not found, incomplete strategy% (17554)------------------------------
% 0.23/0.52  % (17554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (17538)Refutation not found, incomplete strategy% (17538)------------------------------
% 0.23/0.52  % (17538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (17538)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (17538)Memory used [KB]: 6268
% 0.23/0.52  % (17538)Time elapsed: 0.095 s
% 0.23/0.52  % (17538)------------------------------
% 0.23/0.52  % (17538)------------------------------
% 0.23/0.53  % (17546)Refutation not found, incomplete strategy% (17546)------------------------------
% 0.23/0.53  % (17546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (17554)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (17554)Memory used [KB]: 1663
% 0.23/0.53  % (17554)Time elapsed: 0.098 s
% 0.23/0.53  % (17554)------------------------------
% 0.23/0.53  % (17554)------------------------------
% 0.23/0.53  % (17546)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  % (17537)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.53  
% 0.23/0.53  % (17546)Memory used [KB]: 6140
% 0.23/0.53  % (17546)Time elapsed: 0.005 s
% 0.23/0.53  % (17546)------------------------------
% 0.23/0.53  % (17546)------------------------------
% 0.23/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.23/0.53  % (17537)# SZS output start Saturation.
% 0.23/0.53  cnf(u44,axiom,
% 0.23/0.53      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1).
% 0.23/0.53  
% 0.23/0.53  cnf(u45,axiom,
% 0.23/0.53      ~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0).
% 0.23/0.53  
% 0.23/0.53  cnf(u52,negated_conjecture,
% 0.23/0.53      sK0 = sK1).
% 0.23/0.53  
% 0.23/0.53  cnf(u55,negated_conjecture,
% 0.23/0.53      k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))).
% 0.23/0.53  
% 0.23/0.53  cnf(u48,axiom,
% 0.23/0.53      k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) | X0 = X1).
% 0.23/0.53  
% 0.23/0.53  cnf(u26,axiom,
% 0.23/0.53      k3_xboole_0(X0,X0) = X0).
% 0.23/0.53  
% 0.23/0.53  % (17537)# SZS output end Saturation.
% 0.23/0.53  % (17537)------------------------------
% 0.23/0.53  % (17537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (17537)Termination reason: Satisfiable
% 0.23/0.53  
% 0.23/0.53  % (17537)Memory used [KB]: 6140
% 0.23/0.53  % (17537)Time elapsed: 0.100 s
% 0.23/0.53  % (17537)------------------------------
% 0.23/0.53  % (17537)------------------------------
% 0.23/0.53  % (17530)Success in time 0.15 s
%------------------------------------------------------------------------------
