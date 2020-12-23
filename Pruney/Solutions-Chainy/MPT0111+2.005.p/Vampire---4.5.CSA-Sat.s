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
% DateTime   : Thu Dec  3 12:32:30 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   16 (  16 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u8,negated_conjecture,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) )).

cnf(u5,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) )).

cnf(u6,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 )).

cnf(u7,negated_conjecture,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) )).

cnf(u11,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u9,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u12,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:41:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (13024)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (13021)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (13024)Refutation not found, incomplete strategy% (13024)------------------------------
% 0.21/0.47  % (13024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13024)Memory used [KB]: 10618
% 0.21/0.47  % (13024)Time elapsed: 0.026 s
% 0.21/0.47  % (13024)------------------------------
% 0.21/0.47  % (13024)------------------------------
% 0.21/0.48  % (13013)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (13013)Refutation not found, incomplete strategy% (13013)------------------------------
% 0.21/0.48  % (13013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13013)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13013)Memory used [KB]: 10490
% 0.21/0.48  % (13013)Time elapsed: 0.003 s
% 0.21/0.48  % (13013)------------------------------
% 0.21/0.48  % (13013)------------------------------
% 0.21/0.48  % (13021)Refutation not found, incomplete strategy% (13021)------------------------------
% 0.21/0.48  % (13021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13021)Memory used [KB]: 10618
% 0.21/0.48  % (13021)Time elapsed: 0.005 s
% 0.21/0.48  % (13021)------------------------------
% 0.21/0.48  % (13021)------------------------------
% 0.21/0.49  % (13017)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (13010)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (13017)Refutation not found, incomplete strategy% (13017)------------------------------
% 0.21/0.49  % (13017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13017)Memory used [KB]: 6012
% 0.21/0.49  % (13017)Time elapsed: 0.074 s
% 0.21/0.49  % (13017)------------------------------
% 0.21/0.49  % (13017)------------------------------
% 0.21/0.49  % (13011)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (13016)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (13011)Refutation not found, incomplete strategy% (13011)------------------------------
% 0.21/0.49  % (13011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13011)Memory used [KB]: 1535
% 0.21/0.49  % (13011)Time elapsed: 0.075 s
% 0.21/0.49  % (13011)------------------------------
% 0.21/0.49  % (13011)------------------------------
% 0.21/0.49  % (13010)Refutation not found, incomplete strategy% (13010)------------------------------
% 0.21/0.49  % (13010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13010)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13010)Memory used [KB]: 10490
% 0.21/0.49  % (13010)Time elapsed: 0.076 s
% 0.21/0.49  % (13010)------------------------------
% 0.21/0.49  % (13010)------------------------------
% 0.21/0.49  % (13016)Refutation not found, incomplete strategy% (13016)------------------------------
% 0.21/0.49  % (13016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13016)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13016)Memory used [KB]: 10618
% 0.21/0.49  % (13016)Time elapsed: 0.070 s
% 0.21/0.49  % (13016)------------------------------
% 0.21/0.49  % (13016)------------------------------
% 0.21/0.49  % (13015)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (13018)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (13018)Refutation not found, incomplete strategy% (13018)------------------------------
% 0.21/0.49  % (13018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13018)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13018)Memory used [KB]: 10490
% 0.21/0.49  % (13018)Time elapsed: 0.090 s
% 0.21/0.49  % (13018)------------------------------
% 0.21/0.49  % (13018)------------------------------
% 0.21/0.49  % (13019)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (13019)Refutation not found, incomplete strategy% (13019)------------------------------
% 0.21/0.49  % (13019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (13019)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (13019)Memory used [KB]: 6012
% 0.21/0.49  % (13019)Time elapsed: 0.001 s
% 0.21/0.49  % (13019)------------------------------
% 0.21/0.49  % (13019)------------------------------
% 0.21/0.50  % (13023)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (13023)Refutation not found, incomplete strategy% (13023)------------------------------
% 0.21/0.50  % (13023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13023)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13012)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (13023)Memory used [KB]: 6012
% 0.21/0.50  % (13023)Time elapsed: 0.087 s
% 0.21/0.50  % (13023)------------------------------
% 0.21/0.50  % (13023)------------------------------
% 0.21/0.50  % (13027)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (13008)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (13014)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (13027)Refutation not found, incomplete strategy% (13027)------------------------------
% 0.21/0.50  % (13027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13027)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13027)Memory used [KB]: 6012
% 0.21/0.50  % (13027)Time elapsed: 0.091 s
% 0.21/0.50  % (13027)------------------------------
% 0.21/0.50  % (13027)------------------------------
% 0.21/0.50  % (13007)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (13008)Refutation not found, incomplete strategy% (13008)------------------------------
% 0.21/0.50  % (13008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13008)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13008)Memory used [KB]: 10490
% 0.21/0.50  % (13008)Time elapsed: 0.086 s
% 0.21/0.50  % (13008)------------------------------
% 0.21/0.50  % (13008)------------------------------
% 0.21/0.50  % (13007)Refutation not found, incomplete strategy% (13007)------------------------------
% 0.21/0.50  % (13007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13007)Memory used [KB]: 6140
% 0.21/0.50  % (13007)Time elapsed: 0.094 s
% 0.21/0.50  % (13007)------------------------------
% 0.21/0.50  % (13007)------------------------------
% 0.21/0.50  % (13026)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (13026)Refutation not found, incomplete strategy% (13026)------------------------------
% 0.21/0.50  % (13026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13026)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13026)Memory used [KB]: 1535
% 0.21/0.50  % (13026)Time elapsed: 0.096 s
% 0.21/0.50  % (13026)------------------------------
% 0.21/0.50  % (13026)------------------------------
% 0.21/0.50  % (13020)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (13020)Refutation not found, incomplete strategy% (13020)------------------------------
% 0.21/0.50  % (13020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13020)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13020)Memory used [KB]: 1535
% 0.21/0.50  % (13020)Time elapsed: 0.098 s
% 0.21/0.50  % (13020)------------------------------
% 0.21/0.50  % (13020)------------------------------
% 0.21/0.51  % (13028)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (13025)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (13025)# SZS output start Saturation.
% 0.21/0.51  cnf(u8,negated_conjecture,
% 0.21/0.51      r3_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u5,negated_conjecture,
% 0.21/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK0,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u6,negated_conjecture,
% 0.21/0.51      ~r3_xboole_0(sK0,sK1) | sK0 != sK1).
% 0.21/0.51  
% 0.21/0.51  cnf(u7,negated_conjecture,
% 0.21/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK1,sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u11,axiom,
% 0.21/0.51      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u9,axiom,
% 0.21/0.51      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u12,axiom,
% 0.21/0.51      ~r2_xboole_0(X1,X1)).
% 0.21/0.51  
% 0.21/0.51  % (13025)# SZS output end Saturation.
% 0.21/0.51  % (13025)------------------------------
% 0.21/0.51  % (13025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13025)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (13025)Memory used [KB]: 1535
% 0.21/0.51  % (13025)Time elapsed: 0.101 s
% 0.21/0.51  % (13025)------------------------------
% 0.21/0.51  % (13025)------------------------------
% 0.21/0.51  % (13028)Refutation not found, incomplete strategy% (13028)------------------------------
% 0.21/0.51  % (13028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13028)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13028)Memory used [KB]: 10490
% 0.21/0.51  % (13028)Time elapsed: 0.099 s
% 0.21/0.51  % (13028)------------------------------
% 0.21/0.51  % (13028)------------------------------
% 0.21/0.51  % (13005)Success in time 0.145 s
%------------------------------------------------------------------------------
