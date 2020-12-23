%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:24 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
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

% (12057)Refutation not found, incomplete strategy% (12057)------------------------------
% (12057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12057)Termination reason: Refutation not found, incomplete strategy

% (12057)Memory used [KB]: 10490
% (12057)Time elapsed: 0.099 s
% (12057)------------------------------
% (12057)------------------------------
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (12060)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (12071)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (12071)Refutation not found, incomplete strategy% (12071)------------------------------
% 0.22/0.48  % (12071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (12071)Memory used [KB]: 6012
% 0.22/0.48  % (12071)Time elapsed: 0.006 s
% 0.22/0.48  % (12071)------------------------------
% 0.22/0.48  % (12071)------------------------------
% 0.22/0.48  % (12063)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (12076)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (12060)Refutation not found, incomplete strategy% (12060)------------------------------
% 0.22/0.49  % (12060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12060)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12060)Memory used [KB]: 1535
% 0.22/0.49  % (12060)Time elapsed: 0.071 s
% 0.22/0.49  % (12060)------------------------------
% 0.22/0.49  % (12060)------------------------------
% 0.22/0.49  % (12069)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (12069)Refutation not found, incomplete strategy% (12069)------------------------------
% 0.22/0.49  % (12069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12069)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12069)Memory used [KB]: 1535
% 0.22/0.49  % (12069)Time elapsed: 0.077 s
% 0.22/0.49  % (12069)------------------------------
% 0.22/0.49  % (12069)------------------------------
% 0.22/0.49  % (12058)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (12058)Refutation not found, incomplete strategy% (12058)------------------------------
% 0.22/0.49  % (12058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12058)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12058)Memory used [KB]: 10490
% 0.22/0.49  % (12058)Time elapsed: 0.078 s
% 0.22/0.49  % (12058)------------------------------
% 0.22/0.49  % (12058)------------------------------
% 0.22/0.50  % (12070)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (12076)Refutation not found, incomplete strategy% (12076)------------------------------
% 0.22/0.50  % (12076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12076)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12076)Memory used [KB]: 10490
% 0.22/0.50  % (12076)Time elapsed: 0.080 s
% 0.22/0.50  % (12076)------------------------------
% 0.22/0.50  % (12076)------------------------------
% 0.22/0.50  % (12074)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (12074)Refutation not found, incomplete strategy% (12074)------------------------------
% 0.22/0.50  % (12074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12074)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12074)Memory used [KB]: 1535
% 0.22/0.50  % (12074)Time elapsed: 0.093 s
% 0.22/0.50  % (12074)------------------------------
% 0.22/0.50  % (12074)------------------------------
% 0.22/0.50  % (12061)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (12068)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12068)Refutation not found, incomplete strategy% (12068)------------------------------
% 0.22/0.50  % (12068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12068)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12068)Memory used [KB]: 6012
% 0.22/0.50  % (12068)Time elapsed: 0.091 s
% 0.22/0.50  % (12068)------------------------------
% 0.22/0.50  % (12068)------------------------------
% 0.22/0.50  % (12056)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (12056)Refutation not found, incomplete strategy% (12056)------------------------------
% 0.22/0.51  % (12056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12056)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12056)Memory used [KB]: 6012
% 0.22/0.51  % (12056)Time elapsed: 0.076 s
% 0.22/0.51  % (12056)------------------------------
% 0.22/0.51  % (12056)------------------------------
% 0.22/0.51  % (12075)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (12075)Refutation not found, incomplete strategy% (12075)------------------------------
% 0.22/0.51  % (12075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12075)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12075)Memory used [KB]: 6012
% 0.22/0.51  % (12075)Time elapsed: 0.090 s
% 0.22/0.51  % (12075)------------------------------
% 0.22/0.51  % (12075)------------------------------
% 0.22/0.51  % (12059)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (12073)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (12057)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (12059)Refutation not found, incomplete strategy% (12059)------------------------------
% 0.22/0.51  % (12059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12059)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12059)Memory used [KB]: 10490
% 0.22/0.51  % (12059)Time elapsed: 0.100 s
% 0.22/0.51  % (12059)------------------------------
% 0.22/0.51  % (12059)------------------------------
% 0.22/0.51  % (12066)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (12073)# SZS output start Saturation.
% 0.22/0.51  cnf(u25,axiom,
% 0.22/0.51      r1_tarski(k1_xboole_0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,axiom,
% 0.22/0.51      r1_tarski(k1_xboole_0,k4_xboole_0(X2,X3))).
% 0.22/0.51  
% 0.22/0.51  cnf(u12,axiom,
% 0.22/0.51      r1_tarski(k4_xboole_0(X0,X1),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u14,axiom,
% 0.22/0.51      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.22/0.51  
% 0.22/0.51  cnf(u13,axiom,
% 0.22/0.51      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,axiom,
% 0.22/0.51      r2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.22/0.51  
% 0.22/0.51  cnf(u17,axiom,
% 0.22/0.51      r2_xboole_0(k4_xboole_0(X0,X1),X0) | k4_xboole_0(X0,X1) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u11,negated_conjecture,
% 0.22/0.51      ~r2_xboole_0(k1_xboole_0,sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.22/0.51  
% 0.22/0.51  % (12057)Refutation not found, incomplete strategy% (12057)------------------------------
% 0.22/0.51  % (12057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12057)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12057)Memory used [KB]: 10490
% 0.22/0.51  % (12057)Time elapsed: 0.099 s
% 0.22/0.51  % (12057)------------------------------
% 0.22/0.51  % (12057)------------------------------
% 0.22/0.51  cnf(u18,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,axiom,
% 0.22/0.51      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u10,negated_conjecture,
% 0.22/0.51      k1_xboole_0 != sK0).
% 0.22/0.51  
% 0.22/0.51  % (12073)# SZS output end Saturation.
% 0.22/0.51  % (12073)------------------------------
% 0.22/0.51  % (12073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12073)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (12073)Memory used [KB]: 1663
% 0.22/0.51  % (12073)Time elapsed: 0.101 s
% 0.22/0.51  % (12073)------------------------------
% 0.22/0.51  % (12073)------------------------------
% 0.22/0.51  % (12066)Refutation not found, incomplete strategy% (12066)------------------------------
% 0.22/0.51  % (12066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12066)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12066)Memory used [KB]: 6012
% 0.22/0.51  % (12066)Time elapsed: 0.103 s
% 0.22/0.51  % (12066)------------------------------
% 0.22/0.51  % (12066)------------------------------
% 0.22/0.51  % (12055)Success in time 0.152 s
%------------------------------------------------------------------------------
