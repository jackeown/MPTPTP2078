%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:24 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,axiom,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) )).

cnf(u20,axiom,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3)) )).

cnf(u12,axiom,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) )).

cnf(u14,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u13,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u22,axiom,
    ( r2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u17,axiom,
    ( r2_xboole_0(k4_xboole_0(X0,X1),X0)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u11,negated_conjecture,
    ( ~ r2_xboole_0(k1_xboole_0,sK0) )).

cnf(u26,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u18,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) )).

cnf(u16,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) )).

cnf(u15,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

cnf(u10,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (29723)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (29731)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (29737)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (29728)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (29723)Refutation not found, incomplete strategy% (29723)------------------------------
% 0.20/0.48  % (29723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29723)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29723)Memory used [KB]: 6012
% 0.20/0.48  % (29723)Time elapsed: 0.070 s
% 0.20/0.48  % (29723)------------------------------
% 0.20/0.48  % (29723)------------------------------
% 0.20/0.48  % (29729)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (29729)Refutation not found, incomplete strategy% (29729)------------------------------
% 0.20/0.48  % (29729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29729)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29729)Memory used [KB]: 10618
% 0.20/0.48  % (29729)Time elapsed: 0.081 s
% 0.20/0.48  % (29729)------------------------------
% 0.20/0.48  % (29729)------------------------------
% 0.20/0.49  % (29726)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (29733)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (29730)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (29738)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (29733)Refutation not found, incomplete strategy% (29733)------------------------------
% 0.20/0.49  % (29733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29733)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29733)Memory used [KB]: 6012
% 0.20/0.49  % (29733)Time elapsed: 0.024 s
% 0.20/0.49  % (29733)------------------------------
% 0.20/0.49  % (29733)------------------------------
% 0.20/0.49  % (29738)Refutation not found, incomplete strategy% (29738)------------------------------
% 0.20/0.49  % (29738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29738)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29738)Memory used [KB]: 6012
% 0.20/0.49  % (29738)Time elapsed: 0.053 s
% 0.20/0.49  % (29738)------------------------------
% 0.20/0.49  % (29738)------------------------------
% 0.20/0.49  % (29743)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (29743)Refutation not found, incomplete strategy% (29743)------------------------------
% 0.20/0.49  % (29743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29743)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29743)Memory used [KB]: 10490
% 0.20/0.49  % (29743)Time elapsed: 0.093 s
% 0.20/0.49  % (29743)------------------------------
% 0.20/0.49  % (29743)------------------------------
% 0.20/0.50  % (29725)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (29725)Refutation not found, incomplete strategy% (29725)------------------------------
% 0.20/0.50  % (29725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29725)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29725)Memory used [KB]: 10490
% 0.20/0.50  % (29725)Time elapsed: 0.091 s
% 0.20/0.50  % (29725)------------------------------
% 0.20/0.50  % (29725)------------------------------
% 0.20/0.50  % (29740)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (29736)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.50  % (29740)# SZS output start Saturation.
% 0.20/0.50  cnf(u25,axiom,
% 0.20/0.50      r1_tarski(k1_xboole_0,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u20,axiom,
% 0.20/0.50      r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3))).
% 0.20/0.50  
% 0.20/0.50  cnf(u12,axiom,
% 0.20/0.50      r1_tarski(k4_xboole_0(X0,X1),X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u14,axiom,
% 0.20/0.50      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.50  
% 0.20/0.50  cnf(u13,axiom,
% 0.20/0.50      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u22,axiom,
% 0.20/0.50      r2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.50  
% 0.20/0.50  cnf(u17,axiom,
% 0.20/0.50      r2_xboole_0(k4_xboole_0(X0,X1),X0) | k4_xboole_0(X0,X1) = X0).
% 0.20/0.50  
% 0.20/0.50  cnf(u11,negated_conjecture,
% 0.20/0.50      ~r2_xboole_0(k1_xboole_0,sK0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u26,axiom,
% 0.20/0.50      k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u18,axiom,
% 0.20/0.50      k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))).
% 0.20/0.50  
% 0.20/0.50  cnf(u16,axiom,
% 0.20/0.50      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)).
% 0.20/0.50  
% 0.20/0.50  cnf(u15,axiom,
% 0.20/0.50      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.20/0.50  
% 0.20/0.50  cnf(u10,negated_conjecture,
% 0.20/0.50      k1_xboole_0 != sK0).
% 0.20/0.50  
% 0.20/0.50  % (29740)# SZS output end Saturation.
% 0.20/0.50  % (29740)------------------------------
% 0.20/0.50  % (29740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29740)Termination reason: Satisfiable
% 0.20/0.50  
% 0.20/0.50  % (29740)Memory used [KB]: 1663
% 0.20/0.50  % (29740)Time elapsed: 0.084 s
% 0.20/0.50  % (29740)------------------------------
% 0.20/0.50  % (29740)------------------------------
% 0.20/0.50  % (29735)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (29736)Refutation not found, incomplete strategy% (29736)------------------------------
% 0.20/0.50  % (29736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29736)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29736)Memory used [KB]: 1535
% 0.20/0.50  % (29736)Time elapsed: 0.097 s
% 0.20/0.50  % (29736)------------------------------
% 0.20/0.50  % (29736)------------------------------
% 0.20/0.50  % (29722)Success in time 0.148 s
%------------------------------------------------------------------------------
