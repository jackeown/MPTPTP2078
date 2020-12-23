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
% DateTime   : Thu Dec  3 12:32:31 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :    9 (   9 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u16,negated_conjecture,
    ( r1_tarski(sK0,sK1) )).

cnf(u14,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u10,negated_conjecture,
    ( r2_xboole_0(sK0,sK1) )).

cnf(u12,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

% (3177)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
cnf(u15,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1) )).

cnf(u11,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:09:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.47  % (3183)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (3199)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (3179)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (3199)Refutation not found, incomplete strategy% (3199)------------------------------
% 0.21/0.48  % (3199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3199)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3199)Memory used [KB]: 6012
% 0.21/0.48  % (3199)Time elapsed: 0.034 s
% 0.21/0.48  % (3199)------------------------------
% 0.21/0.48  % (3199)------------------------------
% 0.21/0.48  % (3179)Refutation not found, incomplete strategy% (3179)------------------------------
% 0.21/0.48  % (3179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3179)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3179)Memory used [KB]: 10618
% 0.21/0.48  % (3179)Time elapsed: 0.071 s
% 0.21/0.48  % (3179)------------------------------
% 0.21/0.48  % (3179)------------------------------
% 0.21/0.48  % (3200)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (3200)Refutation not found, incomplete strategy% (3200)------------------------------
% 0.21/0.48  % (3200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3200)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3200)Memory used [KB]: 10490
% 0.21/0.48  % (3200)Time elapsed: 0.061 s
% 0.21/0.48  % (3200)------------------------------
% 0.21/0.48  % (3200)------------------------------
% 0.21/0.48  % (3191)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3188)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (3176)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (3191)Refutation not found, incomplete strategy% (3191)------------------------------
% 0.21/0.48  % (3191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3191)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3191)Memory used [KB]: 6012
% 0.21/0.48  % (3191)Time elapsed: 0.001 s
% 0.21/0.48  % (3191)------------------------------
% 0.21/0.48  % (3191)------------------------------
% 0.21/0.48  % (3188)Refutation not found, incomplete strategy% (3188)------------------------------
% 0.21/0.48  % (3188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3188)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3188)Memory used [KB]: 6012
% 0.21/0.48  % (3188)Time elapsed: 0.084 s
% 0.21/0.48  % (3188)------------------------------
% 0.21/0.48  % (3188)------------------------------
% 0.21/0.49  % (3176)Refutation not found, incomplete strategy% (3176)------------------------------
% 0.21/0.49  % (3176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3176)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3176)Memory used [KB]: 6140
% 0.21/0.49  % (3176)Time elapsed: 0.067 s
% 0.21/0.49  % (3176)------------------------------
% 0.21/0.49  % (3176)------------------------------
% 0.21/0.49  % (3181)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3198)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (3198)Refutation not found, incomplete strategy% (3198)------------------------------
% 0.21/0.49  % (3198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3198)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3198)Memory used [KB]: 1535
% 0.21/0.49  % (3198)Time elapsed: 0.083 s
% 0.21/0.49  % (3198)------------------------------
% 0.21/0.49  % (3198)------------------------------
% 0.21/0.49  % (3190)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (3196)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (3190)Refutation not found, incomplete strategy% (3190)------------------------------
% 0.21/0.50  % (3190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3190)Memory used [KB]: 10490
% 0.21/0.50  % (3190)Time elapsed: 0.088 s
% 0.21/0.50  % (3190)------------------------------
% 0.21/0.50  % (3190)------------------------------
% 0.21/0.50  % (3193)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (3193)Refutation not found, incomplete strategy% (3193)------------------------------
% 0.21/0.50  % (3193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3193)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3193)Memory used [KB]: 1535
% 0.21/0.50  % (3193)Time elapsed: 0.089 s
% 0.21/0.50  % (3193)------------------------------
% 0.21/0.50  % (3193)------------------------------
% 0.21/0.50  % (3196)Refutation not found, incomplete strategy% (3196)------------------------------
% 0.21/0.50  % (3196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3196)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3196)Memory used [KB]: 10618
% 0.21/0.50  % (3196)Time elapsed: 0.045 s
% 0.21/0.50  % (3196)------------------------------
% 0.21/0.50  % (3196)------------------------------
% 0.21/0.50  % (3178)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (3182)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (3178)Refutation not found, incomplete strategy% (3178)------------------------------
% 0.21/0.50  % (3178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3178)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3178)Memory used [KB]: 10490
% 0.21/0.50  % (3178)Time elapsed: 0.084 s
% 0.21/0.50  % (3178)------------------------------
% 0.21/0.50  % (3178)------------------------------
% 0.21/0.50  % (3197)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (3182)Refutation not found, incomplete strategy% (3182)------------------------------
% 0.21/0.50  % (3182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3182)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3182)Memory used [KB]: 10490
% 0.21/0.50  % (3182)Time elapsed: 0.052 s
% 0.21/0.50  % (3182)------------------------------
% 0.21/0.50  % (3182)------------------------------
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (3197)# SZS output start Saturation.
% 0.21/0.50  cnf(u16,negated_conjecture,
% 0.21/0.50      r1_tarski(sK0,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u14,axiom,
% 0.21/0.50      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.50  
% 0.21/0.50  cnf(u10,negated_conjecture,
% 0.21/0.50      r2_xboole_0(sK0,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u12,axiom,
% 0.21/0.50      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.21/0.50  
% 0.21/0.50  % (3177)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  cnf(u15,axiom,
% 0.21/0.50      ~r2_xboole_0(X1,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u17,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k4_xboole_0(sK0,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u11,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k4_xboole_0(sK1,sK0)).
% 0.21/0.50  
% 0.21/0.50  % (3197)# SZS output end Saturation.
% 0.21/0.50  % (3197)------------------------------
% 0.21/0.50  % (3197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3197)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (3197)Memory used [KB]: 1535
% 0.21/0.50  % (3197)Time elapsed: 0.088 s
% 0.21/0.50  % (3197)------------------------------
% 0.21/0.50  % (3197)------------------------------
% 0.21/0.50  % (3194)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (3172)Success in time 0.143 s
%------------------------------------------------------------------------------
