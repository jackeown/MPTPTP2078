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
% DateTime   : Thu Dec  3 12:36:58 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u58,negated_conjecture,
    ( r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) )).

cnf(u29,axiom,
    ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) )).

cnf(u35,axiom,
    ( r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1)) )).

cnf(u57,negated_conjecture,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k1_xboole_0)
    | sK0 = X0
    | sK1 = X0 )).

cnf(u33,axiom,
    ( ~ r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 )).

cnf(u32,axiom,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 )).

cnf(u54,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) )).

cnf(u15,negated_conjecture,
    ( sK0 != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (16311)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (16327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (16320)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (16312)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (16319)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (16303)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (16304)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (16320)Refutation not found, incomplete strategy% (16320)------------------------------
% 0.21/0.51  % (16320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16320)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16320)Memory used [KB]: 10746
% 0.21/0.51  % (16320)Time elapsed: 0.069 s
% 0.21/0.51  % (16320)------------------------------
% 0.21/0.51  % (16320)------------------------------
% 0.21/0.51  % (16327)Refutation not found, incomplete strategy% (16327)------------------------------
% 0.21/0.51  % (16327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16327)Memory used [KB]: 1791
% 0.21/0.51  % (16327)Time elapsed: 0.116 s
% 0.21/0.51  % (16327)------------------------------
% 0.21/0.51  % (16327)------------------------------
% 0.21/0.51  % (16303)Refutation not found, incomplete strategy% (16303)------------------------------
% 0.21/0.51  % (16303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16303)Memory used [KB]: 6268
% 0.21/0.51  % (16303)Time elapsed: 0.117 s
% 0.21/0.51  % (16303)------------------------------
% 0.21/0.51  % (16303)------------------------------
% 0.21/0.52  % (16310)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (16310)Refutation not found, incomplete strategy% (16310)------------------------------
% 0.21/0.52  % (16310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16310)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16310)Memory used [KB]: 6140
% 0.21/0.52  % (16310)Time elapsed: 0.120 s
% 0.21/0.52  % (16310)------------------------------
% 0.21/0.52  % (16310)------------------------------
% 0.21/0.52  % (16321)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (16319)Refutation not found, incomplete strategy% (16319)------------------------------
% 0.21/0.52  % (16319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16319)Memory used [KB]: 1663
% 0.21/0.52  % (16319)Time elapsed: 0.117 s
% 0.21/0.52  % (16319)------------------------------
% 0.21/0.52  % (16319)------------------------------
% 0.21/0.53  % (16299)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (16301)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (16300)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (16300)Refutation not found, incomplete strategy% (16300)------------------------------
% 0.21/0.53  % (16300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16300)Memory used [KB]: 10618
% 0.21/0.53  % (16300)Time elapsed: 0.126 s
% 0.21/0.53  % (16300)------------------------------
% 0.21/0.53  % (16300)------------------------------
% 0.21/0.53  % (16301)Refutation not found, incomplete strategy% (16301)------------------------------
% 0.21/0.53  % (16301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16301)Memory used [KB]: 10618
% 0.21/0.53  % (16301)Time elapsed: 0.126 s
% 0.21/0.53  % (16301)------------------------------
% 0.21/0.53  % (16301)------------------------------
% 0.21/0.53  % (16308)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.53  % (16307)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (16304)# SZS output start Saturation.
% 0.21/0.53  cnf(u58,negated_conjecture,
% 0.21/0.53      r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)).
% 0.21/0.53  
% 0.21/0.53  cnf(u29,axiom,
% 0.21/0.53      r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u35,axiom,
% 0.21/0.53      r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X1))).
% 0.21/0.53  
% 0.21/0.53  cnf(u57,negated_conjecture,
% 0.21/0.53      ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k1_xboole_0) | sK0 = X0 | sK1 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u33,axiom,
% 0.21/0.53      ~r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2).
% 0.21/0.53  
% 0.21/0.53  cnf(u32,axiom,
% 0.21/0.53      ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0).
% 0.21/0.53  
% 0.21/0.53  cnf(u54,negated_conjecture,
% 0.21/0.53      k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)).
% 0.21/0.53  
% 0.21/0.53  cnf(u15,negated_conjecture,
% 0.21/0.53      sK0 != sK2).
% 0.21/0.53  
% 0.21/0.53  % (16304)# SZS output end Saturation.
% 0.21/0.53  % (16304)------------------------------
% 0.21/0.53  % (16304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16304)Termination reason: Satisfiable
% 0.21/0.53  
% 0.21/0.53  % (16304)Memory used [KB]: 6268
% 0.21/0.53  % (16304)Time elapsed: 0.089 s
% 0.21/0.53  % (16304)------------------------------
% 0.21/0.53  % (16304)------------------------------
% 0.21/0.53  % (16297)Success in time 0.174 s
%------------------------------------------------------------------------------
