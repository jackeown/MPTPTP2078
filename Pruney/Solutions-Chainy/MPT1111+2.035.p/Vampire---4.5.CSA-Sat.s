%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u29,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u28,negated_conjecture,
    ( ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ r2_hidden(X2,k1_xboole_0) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK2(X0),X1)
    | k1_xboole_0 = X0 )).

cnf(u18,axiom,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u19,axiom,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | m1_subset_1(X0,X2) )).

cnf(u16,axiom,
    ( ~ r2_hidden(X2,X0)
    | k1_xboole_0 = X0
    | k4_mcart_1(X2,X3,X4,X5) != sK2(X0) )).

cnf(u17,axiom,
    ( ~ r2_hidden(X3,X0)
    | k1_xboole_0 = X0
    | k4_mcart_1(X2,X3,X4,X5) != sK2(X0) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 != k1_struct_0(sK0) )).

cnf(u24,axiom,
    ( sK2(X0) != k4_mcart_1(X1,sK2(X0),X2,X3)
    | k1_xboole_0 = X0 )).

% (1489)Refutation not found, incomplete strategy% (1489)------------------------------
% (1489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u22,axiom,
    ( sK2(X0) != k4_mcart_1(sK2(X0),X1,X2,X3)
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (1495)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (1497)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (1494)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (1503)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (1506)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (1504)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (1495)Refutation not found, incomplete strategy% (1495)------------------------------
% 0.22/0.50  % (1495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1495)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1495)Memory used [KB]: 10618
% 0.22/0.50  % (1495)Time elapsed: 0.061 s
% 0.22/0.50  % (1495)------------------------------
% 0.22/0.50  % (1495)------------------------------
% 0.22/0.50  % (1503)Refutation not found, incomplete strategy% (1503)------------------------------
% 0.22/0.50  % (1503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1503)Memory used [KB]: 1663
% 0.22/0.50  % (1503)Time elapsed: 0.073 s
% 0.22/0.50  % (1503)------------------------------
% 0.22/0.50  % (1503)------------------------------
% 0.22/0.51  % (1506)Refutation not found, incomplete strategy% (1506)------------------------------
% 0.22/0.51  % (1506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1506)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1506)Memory used [KB]: 10618
% 0.22/0.51  % (1506)Time elapsed: 0.084 s
% 0.22/0.51  % (1506)------------------------------
% 0.22/0.51  % (1506)------------------------------
% 0.22/0.51  % (1504)Refutation not found, incomplete strategy% (1504)------------------------------
% 0.22/0.51  % (1504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1504)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1504)Memory used [KB]: 10618
% 0.22/0.51  % (1504)Time elapsed: 0.084 s
% 0.22/0.51  % (1504)------------------------------
% 0.22/0.51  % (1504)------------------------------
% 0.22/0.53  % (1501)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (1491)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.53  % (1496)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.53  % (1491)Refutation not found, incomplete strategy% (1491)------------------------------
% 0.22/0.53  % (1491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1491)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1491)Memory used [KB]: 10618
% 0.22/0.53  % (1491)Time elapsed: 0.101 s
% 0.22/0.53  % (1491)------------------------------
% 0.22/0.53  % (1491)------------------------------
% 0.22/0.54  % (1493)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.54  % (1492)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (1490)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (1500)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (1492)Refutation not found, incomplete strategy% (1492)------------------------------
% 0.22/0.54  % (1492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1492)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1492)Memory used [KB]: 10618
% 0.22/0.54  % (1492)Time elapsed: 0.102 s
% 0.22/0.54  % (1492)------------------------------
% 0.22/0.54  % (1492)------------------------------
% 0.22/0.54  % (1500)Refutation not found, incomplete strategy% (1500)------------------------------
% 0.22/0.54  % (1500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1500)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1500)Memory used [KB]: 6012
% 0.22/0.54  % (1500)Time elapsed: 0.102 s
% 0.22/0.54  % (1500)------------------------------
% 0.22/0.54  % (1500)------------------------------
% 0.22/0.54  % (1490)Refutation not found, incomplete strategy% (1490)------------------------------
% 0.22/0.54  % (1490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1490)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1490)Memory used [KB]: 10618
% 0.22/0.54  % (1490)Time elapsed: 0.070 s
% 0.22/0.54  % (1490)------------------------------
% 0.22/0.54  % (1490)------------------------------
% 0.22/0.54  % (1505)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (1501)Refutation not found, incomplete strategy% (1501)------------------------------
% 0.22/0.54  % (1501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1505)Refutation not found, incomplete strategy% (1505)------------------------------
% 0.22/0.54  % (1505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1505)Memory used [KB]: 6140
% 0.22/0.54  % (1505)Time elapsed: 0.118 s
% 0.22/0.54  % (1505)------------------------------
% 0.22/0.54  % (1505)------------------------------
% 0.22/0.54  % (1501)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1501)Memory used [KB]: 10490
% 0.22/0.54  % (1501)Time elapsed: 0.119 s
% 0.22/0.54  % (1501)------------------------------
% 0.22/0.54  % (1501)------------------------------
% 0.22/0.54  % (1508)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (1507)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.54  % (1489)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (1508)Refutation not found, incomplete strategy% (1508)------------------------------
% 0.22/0.54  % (1508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1508)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1508)Memory used [KB]: 1663
% 0.22/0.54  % (1508)Time elapsed: 0.112 s
% 0.22/0.54  % (1508)------------------------------
% 0.22/0.54  % (1508)------------------------------
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (1507)# SZS output start Saturation.
% 0.22/0.54  cnf(u29,negated_conjecture,
% 0.22/0.54      m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  cnf(u28,negated_conjecture,
% 0.22/0.54      ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_xboole_0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u20,axiom,
% 0.22/0.54      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | m1_subset_1(sK2(X0),X1) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u18,axiom,
% 0.22/0.54      r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  cnf(u19,axiom,
% 0.22/0.54      ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)).
% 0.22/0.54  
% 0.22/0.54  cnf(u16,axiom,
% 0.22/0.54      ~r2_hidden(X2,X0) | k1_xboole_0 = X0 | k4_mcart_1(X2,X3,X4,X5) != sK2(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u17,axiom,
% 0.22/0.54      ~r2_hidden(X3,X0) | k1_xboole_0 = X0 | k4_mcart_1(X2,X3,X4,X5) != sK2(X0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u27,negated_conjecture,
% 0.22/0.54      k1_xboole_0 = sK1).
% 0.22/0.54  
% 0.22/0.54  cnf(u30,negated_conjecture,
% 0.22/0.54      k1_xboole_0 != k1_struct_0(sK0)).
% 0.22/0.54  
% 0.22/0.54  cnf(u24,axiom,
% 0.22/0.54      sK2(X0) != k4_mcart_1(X1,sK2(X0),X2,X3) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  % (1489)Refutation not found, incomplete strategy% (1489)------------------------------
% 0.22/0.54  % (1489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  cnf(u22,axiom,
% 0.22/0.54      sK2(X0) != k4_mcart_1(sK2(X0),X1,X2,X3) | k1_xboole_0 = X0).
% 0.22/0.54  
% 0.22/0.54  % (1507)# SZS output end Saturation.
% 0.22/0.54  % (1507)------------------------------
% 0.22/0.54  % (1507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1507)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (1507)Memory used [KB]: 1663
% 0.22/0.54  % (1507)Time elapsed: 0.074 s
% 0.22/0.54  % (1507)------------------------------
% 0.22/0.54  % (1507)------------------------------
% 0.22/0.54  % (1489)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1489)Memory used [KB]: 6012
% 0.22/0.54  % (1489)Time elapsed: 0.109 s
% 0.22/0.54  % (1489)------------------------------
% 0.22/0.54  % (1489)------------------------------
% 0.22/0.54  % (1488)Success in time 0.175 s
%------------------------------------------------------------------------------
