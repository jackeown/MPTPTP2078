%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:29 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
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
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (29790)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (29790)Refutation not found, incomplete strategy% (29790)------------------------------
% 0.20/0.46  % (29790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (29790)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (29790)Memory used [KB]: 6012
% 0.20/0.46  % (29790)Time elapsed: 0.004 s
% 0.20/0.46  % (29790)------------------------------
% 0.20/0.46  % (29790)------------------------------
% 0.20/0.47  % (29792)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (29792)Refutation not found, incomplete strategy% (29792)------------------------------
% 0.20/0.47  % (29792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29792)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (29792)Memory used [KB]: 10618
% 0.20/0.47  % (29792)Time elapsed: 0.003 s
% 0.20/0.47  % (29792)------------------------------
% 0.20/0.47  % (29792)------------------------------
% 0.20/0.47  % (29784)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (29784)Refutation not found, incomplete strategy% (29784)------------------------------
% 0.20/0.48  % (29784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29784)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (29784)Memory used [KB]: 10490
% 0.20/0.48  % (29784)Time elapsed: 0.002 s
% 0.20/0.48  % (29784)------------------------------
% 0.20/0.48  % (29784)------------------------------
% 0.20/0.48  % (29786)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (29794)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  % (29780)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (29779)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (29780)Refutation not found, incomplete strategy% (29780)------------------------------
% 0.20/0.49  % (29780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29780)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29780)Memory used [KB]: 10490
% 0.20/0.49  % (29780)Time elapsed: 0.074 s
% 0.20/0.49  % (29780)------------------------------
% 0.20/0.49  % (29780)------------------------------
% 0.20/0.49  % (29783)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (29779)Refutation not found, incomplete strategy% (29779)------------------------------
% 0.20/0.49  % (29779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29779)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29779)Memory used [KB]: 10490
% 0.20/0.49  % (29779)Time elapsed: 0.077 s
% 0.20/0.49  % (29779)------------------------------
% 0.20/0.49  % (29779)------------------------------
% 0.20/0.49  % (29782)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (29782)Refutation not found, incomplete strategy% (29782)------------------------------
% 0.20/0.49  % (29782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29782)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29782)Memory used [KB]: 1535
% 0.20/0.49  % (29782)Time elapsed: 0.074 s
% 0.20/0.49  % (29782)------------------------------
% 0.20/0.49  % (29782)------------------------------
% 0.20/0.49  % (29794)Refutation not found, incomplete strategy% (29794)------------------------------
% 0.20/0.49  % (29794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29794)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29794)Memory used [KB]: 10618
% 0.20/0.49  % (29794)Time elapsed: 0.089 s
% 0.20/0.49  % (29794)------------------------------
% 0.20/0.49  % (29794)------------------------------
% 0.20/0.49  % (29787)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (29785)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (29793)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (29787)Refutation not found, incomplete strategy% (29787)------------------------------
% 0.20/0.50  % (29787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29787)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29787)Memory used [KB]: 10618
% 0.20/0.50  % (29787)Time elapsed: 0.088 s
% 0.20/0.50  % (29787)------------------------------
% 0.20/0.50  % (29787)------------------------------
% 0.20/0.50  % (29793)Refutation not found, incomplete strategy% (29793)------------------------------
% 0.20/0.50  % (29793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29793)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29793)Memory used [KB]: 6012
% 0.20/0.50  % (29793)Time elapsed: 0.077 s
% 0.20/0.50  % (29793)------------------------------
% 0.20/0.50  % (29793)------------------------------
% 0.20/0.50  % (29796)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (29796)Refutation not found, incomplete strategy% (29796)------------------------------
% 0.20/0.50  % (29796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29796)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29796)Memory used [KB]: 1535
% 0.20/0.50  % (29796)Time elapsed: 0.086 s
% 0.20/0.50  % (29796)------------------------------
% 0.20/0.50  % (29796)------------------------------
% 0.20/0.50  % (29781)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (29797)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (29781)Refutation not found, incomplete strategy% (29781)------------------------------
% 0.20/0.50  % (29781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29781)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29781)Memory used [KB]: 10490
% 0.20/0.50  % (29781)Time elapsed: 0.084 s
% 0.20/0.50  % (29781)------------------------------
% 0.20/0.50  % (29781)------------------------------
% 0.20/0.50  % (29797)Refutation not found, incomplete strategy% (29797)------------------------------
% 0.20/0.50  % (29797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29797)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29797)Memory used [KB]: 6012
% 0.20/0.50  % (29797)Time elapsed: 0.087 s
% 0.20/0.50  % (29797)------------------------------
% 0.20/0.50  % (29797)------------------------------
% 0.20/0.50  % (29798)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (29798)Refutation not found, incomplete strategy% (29798)------------------------------
% 0.20/0.50  % (29798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29798)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29798)Memory used [KB]: 10490
% 0.20/0.50  % (29798)Time elapsed: 0.099 s
% 0.20/0.50  % (29798)------------------------------
% 0.20/0.50  % (29798)------------------------------
% 0.20/0.50  % (29788)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (29788)Refutation not found, incomplete strategy% (29788)------------------------------
% 0.20/0.50  % (29788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29788)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29788)Memory used [KB]: 6012
% 0.20/0.50  % (29788)Time elapsed: 0.097 s
% 0.20/0.50  % (29788)------------------------------
% 0.20/0.50  % (29788)------------------------------
% 0.20/0.50  % (29791)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (29791)Refutation not found, incomplete strategy% (29791)------------------------------
% 0.20/0.50  % (29791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29791)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29791)Memory used [KB]: 1535
% 0.20/0.50  % (29791)Time elapsed: 0.099 s
% 0.20/0.50  % (29791)------------------------------
% 0.20/0.50  % (29791)------------------------------
% 0.20/0.51  % (29789)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (29778)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (29789)Refutation not found, incomplete strategy% (29789)------------------------------
% 0.20/0.51  % (29789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29789)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29789)Memory used [KB]: 10490
% 0.20/0.51  % (29789)Time elapsed: 0.097 s
% 0.20/0.51  % (29789)------------------------------
% 0.20/0.51  % (29789)------------------------------
% 0.20/0.51  % (29778)Refutation not found, incomplete strategy% (29778)------------------------------
% 0.20/0.51  % (29778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29778)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (29778)Memory used [KB]: 6140
% 0.20/0.51  % (29778)Time elapsed: 0.092 s
% 0.20/0.51  % (29778)------------------------------
% 0.20/0.51  % (29778)------------------------------
% 0.20/0.51  % (29795)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.51  % (29795)# SZS output start Saturation.
% 0.20/0.51  cnf(u8,negated_conjecture,
% 0.20/0.51      r3_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u5,negated_conjecture,
% 0.20/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK0,sK1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u6,negated_conjecture,
% 0.20/0.51      ~r3_xboole_0(sK0,sK1) | sK0 != sK1).
% 0.20/0.51  
% 0.20/0.51  cnf(u7,negated_conjecture,
% 0.20/0.51      ~r3_xboole_0(sK0,sK1) | ~r2_xboole_0(sK1,sK0)).
% 0.20/0.51  
% 0.20/0.51  cnf(u11,axiom,
% 0.20/0.51      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u9,axiom,
% 0.20/0.51      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.20/0.51  
% 0.20/0.51  cnf(u12,axiom,
% 0.20/0.51      ~r2_xboole_0(X1,X1)).
% 0.20/0.51  
% 0.20/0.51  % (29795)# SZS output end Saturation.
% 0.20/0.51  % (29795)------------------------------
% 0.20/0.51  % (29795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (29795)Termination reason: Satisfiable
% 0.20/0.51  
% 0.20/0.51  % (29795)Memory used [KB]: 1535
% 0.20/0.51  % (29795)Time elapsed: 0.095 s
% 0.20/0.51  % (29795)------------------------------
% 0.20/0.51  % (29795)------------------------------
% 0.20/0.51  % (29777)Success in time 0.153 s
%------------------------------------------------------------------------------
