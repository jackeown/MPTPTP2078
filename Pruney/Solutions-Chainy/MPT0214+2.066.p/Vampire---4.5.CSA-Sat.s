%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:07 EST 2020

% Result     : CounterSatisfiable 1.66s
% Output     : Saturation 1.66s
% Verified   : 
% Statistics : Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :  146 ( 146 expanded)
%              Number of equality atoms :  127 ( 127 expanded)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u72,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) )).

cnf(u33,axiom,
    ( r1_tarski(k1_xboole_0,k1_tarski(X1)) )).

cnf(u32,axiom,
    ( r1_tarski(k1_tarski(X1),k1_tarski(X1)) )).

cnf(u77,negated_conjecture,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u26,axiom,
    ( ~ r1_tarski(X0,k1_tarski(X1))
    | k1_xboole_0 = X0
    | k1_tarski(X1) = X0 )).

cnf(u70,negated_conjecture,
    ( r2_hidden(sK0,k1_xboole_0) )).

cnf(u24,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = X0
    | k1_tarski(X0) = X1 )).

cnf(u30,axiom,
    ( r2_hidden(X3,k1_tarski(X3)) )).

cnf(u361,negated_conjecture,
    ( ~ r2_hidden(sK2(X9,k1_xboole_0),k1_xboole_0)
    | sK2(X9,k1_xboole_0) != X8
    | k1_xboole_0 = k1_tarski(X8)
    | sK2(X8,k1_xboole_0) = X8
    | k1_xboole_0 = k1_tarski(X9) )).

cnf(u264,axiom,
    ( ~ r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13))
    | sK2(X14,k1_tarski(X13)) != X12
    | k1_tarski(X13) = k1_tarski(X12)
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14) )).

cnf(u25,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) != X0
    | k1_tarski(X0) = X1 )).

cnf(u71,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | sK0 = X1 )).

cnf(u76,negated_conjecture,
    ( ~ r2_hidden(X4,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(X4)
    | sK0 = sK2(X4,k1_xboole_0) )).

cnf(u142,negated_conjecture,
    ( ~ r2_hidden(X4,k1_xboole_0)
    | sK2(X3,k1_xboole_0) = X4
    | sK2(X3,k1_xboole_0) = X3
    | k1_xboole_0 = k1_tarski(X3) )).

cnf(u147,negated_conjecture,
    ( ~ r2_hidden(X12,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(X12)
    | sK2(X11,k1_xboole_0) = sK2(X12,k1_xboole_0)
    | sK2(X11,k1_xboole_0) = X11
    | k1_xboole_0 = k1_tarski(X11) )).

cnf(u31,axiom,
    ( ~ r2_hidden(X3,k1_tarski(X0))
    | X0 = X3 )).

cnf(u60,axiom,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X1 )).

cnf(u128,axiom,
    ( ~ r2_hidden(X7,k1_tarski(X6))
    | sK2(X5,k1_tarski(X6)) = X7
    | sK2(X5,k1_tarski(X6)) = X5
    | k1_tarski(X5) = k1_tarski(X6) )).

cnf(u133,axiom,
    ( ~ r2_hidden(X20,k1_tarski(X19))
    | k1_tarski(X19) = k1_tarski(X20)
    | sK2(X18,k1_tarski(X19)) = sK2(X20,k1_tarski(X19))
    | sK2(X18,k1_tarski(X19)) = X18
    | k1_tarski(X19) = k1_tarski(X18) )).

cnf(u145,negated_conjecture,
    ( sK2(X8,k1_xboole_0) = X8
    | sK2(X7,k1_xboole_0) = sK2(X8,k1_xboole_0)
    | sK2(X7,k1_xboole_0) = X7
    | k1_xboole_0 = k1_tarski(X8)
    | k1_xboole_0 = k1_tarski(X7) )).

cnf(u131,axiom,
    ( sK2(X14,k1_tarski(X13)) = X14
    | sK2(X12,k1_tarski(X13)) = sK2(X14,k1_tarski(X13))
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14)
    | k1_tarski(X13) = k1_tarski(X12) )).

cnf(u81,negated_conjecture,
    ( sK0 = sK2(sK2(X0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_tarski(sK2(X0,k1_xboole_0))
    | sK2(X0,k1_xboole_0) = X0
    | k1_xboole_0 = k1_tarski(X0) )).

cnf(u74,negated_conjecture,
    ( sK2(X2,k1_xboole_0) = X2
    | sK0 = sK2(X2,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(X2) )).

cnf(u21,axiom,
    ( k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u20,axiom,
    ( k1_tarski(X0) = k2_tarski(X0,X0) )).

cnf(u90,axiom,
    ( k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5)))
    | sK2(X4,k1_tarski(X5)) = X4
    | k1_tarski(X4) = k1_tarski(X5) )).

cnf(u122,negated_conjecture,
    ( k1_xboole_0 = k1_tarski(sK2(X2,k1_xboole_0))
    | sK2(X2,k1_xboole_0) = X2
    | k1_xboole_0 = k1_tarski(X2) )).

cnf(u63,negated_conjecture,
    ( k1_xboole_0 = k1_tarski(sK0) )).

cnf(u68,axiom,
    ( sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2)))
    | sK2(X1,k1_tarski(X2)) = X1
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u38,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u74_001,negated_conjecture,
    ( sK2(X2,k1_xboole_0) = X2
    | sK0 = sK2(X2,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(X2) )).

cnf(u145_002,negated_conjecture,
    ( sK2(X8,k1_xboole_0) = X8
    | sK2(X7,k1_xboole_0) = sK2(X8,k1_xboole_0)
    | sK2(X7,k1_xboole_0) = X7
    | k1_xboole_0 = k1_tarski(X8)
    | k1_xboole_0 = k1_tarski(X7) )).

cnf(u145_003,negated_conjecture,
    ( sK2(X8,k1_xboole_0) = X8
    | sK2(X7,k1_xboole_0) = sK2(X8,k1_xboole_0)
    | sK2(X7,k1_xboole_0) = X7
    | k1_xboole_0 = k1_tarski(X8)
    | k1_xboole_0 = k1_tarski(X7) )).

cnf(u38_004,axiom,
    ( sK2(X0,k1_tarski(X1)) = X0
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u131_005,axiom,
    ( sK2(X14,k1_tarski(X13)) = X14
    | sK2(X12,k1_tarski(X13)) = sK2(X14,k1_tarski(X13))
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14)
    | k1_tarski(X13) = k1_tarski(X12) )).

cnf(u131_006,axiom,
    ( sK2(X14,k1_tarski(X13)) = X14
    | sK2(X12,k1_tarski(X13)) = sK2(X14,k1_tarski(X13))
    | sK2(X12,k1_tarski(X13)) = X12
    | k1_tarski(X13) = k1_tarski(X14)
    | k1_tarski(X13) = k1_tarski(X12) )).

cnf(u319,negated_conjecture,
    ( sK2(X1,k1_xboole_0) != X0
    | sK2(X1,k1_xboole_0) = X1
    | sK2(X0,k1_xboole_0) = X0
    | k1_xboole_0 = k1_tarski(X1)
    | k1_xboole_0 = k1_tarski(X0) )).

cnf(u317,negated_conjecture,
    ( sK2(X1,k1_xboole_0) != X0
    | sK2(X0,k1_xboole_0) = sK2(X1,k1_xboole_0)
    | sK2(X1,k1_xboole_0) = X1
    | k1_xboole_0 = k1_tarski(X0)
    | k1_xboole_0 = k1_tarski(X1) )).

cnf(u222,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X2,k1_tarski(X1)) = X2
    | sK2(X0,k1_tarski(X1)) = X0
    | k1_tarski(X1) = k1_tarski(X2)
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u220,axiom,
    ( sK2(X2,k1_tarski(X1)) != X0
    | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1))
    | sK2(X2,k1_tarski(X1)) = X2
    | k1_tarski(X0) = k1_tarski(X1)
    | k1_tarski(X1) = k1_tarski(X2) )).

cnf(u55,axiom,
    ( X0 != X1
    | sK2(X0,k1_tarski(X1)) = X1
    | k1_tarski(X0) = k1_tarski(X1) )).

cnf(u61,axiom,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1)
    | sK2(X0,k1_tarski(X1)) = X0 )).

cnf(u102,negated_conjecture,
    ( sK0 != X0
    | sK0 = sK2(X0,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(X0) )).

cnf(u108,negated_conjecture,
    ( sK0 != X0
    | k1_xboole_0 = k1_tarski(X0)
    | sK2(X0,k1_xboole_0) = X0 )).

cnf(u19,negated_conjecture,
    ( sK0 != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (21749)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (21750)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (21757)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.56  % (21741)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.56  % (21749)Refutation not found, incomplete strategy% (21749)------------------------------
% 1.50/0.56  % (21749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (21742)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.56  % (21741)Refutation not found, incomplete strategy% (21741)------------------------------
% 1.50/0.56  % (21741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (21749)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (21749)Memory used [KB]: 10746
% 1.50/0.56  % (21749)Time elapsed: 0.127 s
% 1.50/0.56  % (21749)------------------------------
% 1.50/0.56  % (21749)------------------------------
% 1.50/0.56  % (21742)Refutation not found, incomplete strategy% (21742)------------------------------
% 1.50/0.56  % (21742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (21741)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (21741)Memory used [KB]: 1791
% 1.50/0.57  % (21741)Time elapsed: 0.130 s
% 1.50/0.57  % (21741)------------------------------
% 1.50/0.57  % (21741)------------------------------
% 1.50/0.57  % (21742)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (21742)Memory used [KB]: 1663
% 1.50/0.57  % (21742)Time elapsed: 0.126 s
% 1.50/0.57  % (21742)------------------------------
% 1.50/0.57  % (21742)------------------------------
% 1.50/0.57  % (21740)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.50/0.57  % (21758)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.50/0.58  % (21758)Refutation not found, incomplete strategy% (21758)------------------------------
% 1.50/0.58  % (21758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (21758)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (21758)Memory used [KB]: 6268
% 1.50/0.58  % (21758)Time elapsed: 0.142 s
% 1.50/0.58  % (21758)------------------------------
% 1.50/0.58  % (21758)------------------------------
% 1.66/0.58  % (21737)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.58  % (21738)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.58  % (21738)Refutation not found, incomplete strategy% (21738)------------------------------
% 1.66/0.58  % (21738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (21738)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (21738)Memory used [KB]: 1663
% 1.66/0.58  % (21738)Time elapsed: 0.151 s
% 1.66/0.58  % (21738)------------------------------
% 1.66/0.58  % (21738)------------------------------
% 1.66/0.58  % (21752)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.59  % (21751)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.59  % (21743)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.59  % (21760)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.59  % (21745)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.59  % (21760)Refutation not found, incomplete strategy% (21760)------------------------------
% 1.66/0.59  % (21760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (21760)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (21760)Memory used [KB]: 10618
% 1.66/0.59  % (21760)Time elapsed: 0.122 s
% 1.66/0.59  % (21760)------------------------------
% 1.66/0.59  % (21760)------------------------------
% 1.66/0.59  % (21762)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.59  % (21748)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.66/0.60  % (21744)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.60  % (21753)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.60  % (21759)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.66/0.60  % (21753)Refutation not found, incomplete strategy% (21753)------------------------------
% 1.66/0.60  % (21753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (21753)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (21753)Memory used [KB]: 10618
% 1.66/0.60  % (21753)Time elapsed: 0.165 s
% 1.66/0.60  % (21753)------------------------------
% 1.66/0.60  % (21753)------------------------------
% 1.66/0.60  % (21759)Refutation not found, incomplete strategy% (21759)------------------------------
% 1.66/0.60  % (21759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (21759)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (21759)Memory used [KB]: 6268
% 1.66/0.60  % (21759)Time elapsed: 0.169 s
% 1.66/0.60  % (21759)------------------------------
% 1.66/0.60  % (21759)------------------------------
% 1.66/0.60  % (21739)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.60  % (21765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.66/0.60  % (21764)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.60  % (21754)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.66/0.60  % (21764)Refutation not found, incomplete strategy% (21764)------------------------------
% 1.66/0.60  % (21764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (21764)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (21761)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.66/0.60  % (21764)Memory used [KB]: 6140
% 1.66/0.60  % (21764)Time elapsed: 0.174 s
% 1.66/0.60  % (21764)------------------------------
% 1.66/0.60  % (21764)------------------------------
% 1.66/0.60  % (21756)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.60  % (21755)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.61  % (21761)Refutation not found, incomplete strategy% (21761)------------------------------
% 1.66/0.61  % (21761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21761)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21761)Memory used [KB]: 10618
% 1.66/0.61  % (21761)Time elapsed: 0.176 s
% 1.66/0.61  % (21761)------------------------------
% 1.66/0.61  % (21761)------------------------------
% 1.66/0.61  % (21755)Refutation not found, incomplete strategy% (21755)------------------------------
% 1.66/0.61  % (21755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21755)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21755)Memory used [KB]: 1663
% 1.66/0.61  % (21755)Time elapsed: 0.178 s
% 1.66/0.61  % (21755)------------------------------
% 1.66/0.61  % (21755)------------------------------
% 1.66/0.61  % (21756)Refutation not found, incomplete strategy% (21756)------------------------------
% 1.66/0.61  % (21756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21756)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21756)Memory used [KB]: 1663
% 1.66/0.61  % (21756)Time elapsed: 0.176 s
% 1.66/0.61  % (21756)------------------------------
% 1.66/0.61  % (21756)------------------------------
% 1.66/0.61  % (21751)Refutation not found, incomplete strategy% (21751)------------------------------
% 1.66/0.61  % (21751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21751)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21751)Memory used [KB]: 1791
% 1.66/0.61  % (21751)Time elapsed: 0.171 s
% 1.66/0.61  % (21751)------------------------------
% 1.66/0.61  % (21751)------------------------------
% 1.66/0.61  % (21747)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.66/0.61  % (21746)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.66/0.61  % (21766)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.61  % (21766)Refutation not found, incomplete strategy% (21766)------------------------------
% 1.66/0.61  % (21766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21766)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21766)Memory used [KB]: 1663
% 1.66/0.61  % (21766)Time elapsed: 0.002 s
% 1.66/0.61  % (21766)------------------------------
% 1.66/0.61  % (21766)------------------------------
% 1.66/0.61  % (21763)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.66/0.61  % (21763)Refutation not found, incomplete strategy% (21763)------------------------------
% 1.66/0.61  % (21763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (21763)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.61  
% 1.66/0.61  % (21763)Memory used [KB]: 6140
% 1.66/0.61  % (21763)Time elapsed: 0.189 s
% 1.66/0.61  % (21763)------------------------------
% 1.66/0.61  % (21763)------------------------------
% 1.66/0.62  % (21762)Refutation not found, incomplete strategy% (21762)------------------------------
% 1.66/0.62  % (21762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (21762)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.62  
% 1.66/0.62  % (21762)Memory used [KB]: 6140
% 1.66/0.62  % (21762)Time elapsed: 0.187 s
% 1.66/0.62  % (21762)------------------------------
% 1.66/0.62  % (21762)------------------------------
% 1.66/0.62  % SZS status CounterSatisfiable for theBenchmark
% 1.66/0.62  % (21744)# SZS output start Saturation.
% 1.66/0.62  cnf(u72,negated_conjecture,
% 1.66/0.62      r1_tarski(k1_xboole_0,k1_xboole_0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u33,axiom,
% 1.66/0.62      r1_tarski(k1_xboole_0,k1_tarski(X1))).
% 1.66/0.62  
% 1.66/0.62  cnf(u32,axiom,
% 1.66/0.62      r1_tarski(k1_tarski(X1),k1_tarski(X1))).
% 1.66/0.62  
% 1.66/0.62  cnf(u77,negated_conjecture,
% 1.66/0.62      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 1.66/0.62  
% 1.66/0.62  cnf(u26,axiom,
% 1.66/0.62      ~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0).
% 1.66/0.62  
% 1.66/0.62  cnf(u70,negated_conjecture,
% 1.66/0.62      r2_hidden(sK0,k1_xboole_0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u24,axiom,
% 1.66/0.62      r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = X0 | k1_tarski(X0) = X1).
% 1.66/0.62  
% 1.66/0.62  cnf(u30,axiom,
% 1.66/0.62      r2_hidden(X3,k1_tarski(X3))).
% 1.66/0.62  
% 1.66/0.62  cnf(u361,negated_conjecture,
% 1.66/0.62      ~r2_hidden(sK2(X9,k1_xboole_0),k1_xboole_0) | sK2(X9,k1_xboole_0) != X8 | k1_xboole_0 = k1_tarski(X8) | sK2(X8,k1_xboole_0) = X8 | k1_xboole_0 = k1_tarski(X9)).
% 1.66/0.62  
% 1.66/0.62  cnf(u264,axiom,
% 1.66/0.62      ~r2_hidden(sK2(X14,k1_tarski(X13)),k1_tarski(X13)) | sK2(X14,k1_tarski(X13)) != X12 | k1_tarski(X13) = k1_tarski(X12) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14)).
% 1.66/0.62  
% 1.66/0.62  cnf(u25,axiom,
% 1.66/0.62      ~r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) != X0 | k1_tarski(X0) = X1).
% 1.66/0.62  
% 1.66/0.62  cnf(u71,negated_conjecture,
% 1.66/0.62      ~r2_hidden(X1,k1_xboole_0) | sK0 = X1).
% 1.66/0.62  
% 1.66/0.62  cnf(u76,negated_conjecture,
% 1.66/0.62      ~r2_hidden(X4,k1_xboole_0) | k1_xboole_0 = k1_tarski(X4) | sK0 = sK2(X4,k1_xboole_0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u142,negated_conjecture,
% 1.66/0.62      ~r2_hidden(X4,k1_xboole_0) | sK2(X3,k1_xboole_0) = X4 | sK2(X3,k1_xboole_0) = X3 | k1_xboole_0 = k1_tarski(X3)).
% 1.66/0.62  
% 1.66/0.62  cnf(u147,negated_conjecture,
% 1.66/0.62      ~r2_hidden(X12,k1_xboole_0) | k1_xboole_0 = k1_tarski(X12) | sK2(X11,k1_xboole_0) = sK2(X12,k1_xboole_0) | sK2(X11,k1_xboole_0) = X11 | k1_xboole_0 = k1_tarski(X11)).
% 1.66/0.62  
% 1.66/0.62  cnf(u31,axiom,
% 1.66/0.62      ~r2_hidden(X3,k1_tarski(X0)) | X0 = X3).
% 1.66/0.62  
% 1.66/0.62  cnf(u60,axiom,
% 1.66/0.62      ~r2_hidden(X0,k1_tarski(X1)) | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X1).
% 1.66/0.62  
% 1.66/0.62  cnf(u128,axiom,
% 1.66/0.62      ~r2_hidden(X7,k1_tarski(X6)) | sK2(X5,k1_tarski(X6)) = X7 | sK2(X5,k1_tarski(X6)) = X5 | k1_tarski(X5) = k1_tarski(X6)).
% 1.66/0.62  
% 1.66/0.62  cnf(u133,axiom,
% 1.66/0.62      ~r2_hidden(X20,k1_tarski(X19)) | k1_tarski(X19) = k1_tarski(X20) | sK2(X18,k1_tarski(X19)) = sK2(X20,k1_tarski(X19)) | sK2(X18,k1_tarski(X19)) = X18 | k1_tarski(X19) = k1_tarski(X18)).
% 1.66/0.62  
% 1.66/0.62  cnf(u145,negated_conjecture,
% 1.66/0.62      sK2(X8,k1_xboole_0) = X8 | sK2(X7,k1_xboole_0) = sK2(X8,k1_xboole_0) | sK2(X7,k1_xboole_0) = X7 | k1_xboole_0 = k1_tarski(X8) | k1_xboole_0 = k1_tarski(X7)).
% 1.66/0.62  
% 1.66/0.62  cnf(u131,axiom,
% 1.66/0.62      sK2(X14,k1_tarski(X13)) = X14 | sK2(X12,k1_tarski(X13)) = sK2(X14,k1_tarski(X13)) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14) | k1_tarski(X13) = k1_tarski(X12)).
% 1.66/0.62  
% 1.66/0.62  cnf(u81,negated_conjecture,
% 1.66/0.62      sK0 = sK2(sK2(X0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_tarski(sK2(X0,k1_xboole_0)) | sK2(X0,k1_xboole_0) = X0 | k1_xboole_0 = k1_tarski(X0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u74,negated_conjecture,
% 1.66/0.62      sK2(X2,k1_xboole_0) = X2 | sK0 = sK2(X2,k1_xboole_0) | k1_xboole_0 = k1_tarski(X2)).
% 1.66/0.62  
% 1.66/0.62  cnf(u21,axiom,
% 1.66/0.62      k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)).
% 1.66/0.62  
% 1.66/0.62  cnf(u20,axiom,
% 1.66/0.62      k1_tarski(X0) = k2_tarski(X0,X0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u90,axiom,
% 1.66/0.62      k1_tarski(X5) = k1_tarski(sK2(X4,k1_tarski(X5))) | sK2(X4,k1_tarski(X5)) = X4 | k1_tarski(X4) = k1_tarski(X5)).
% 1.66/0.62  
% 1.66/0.62  cnf(u122,negated_conjecture,
% 1.66/0.62      k1_xboole_0 = k1_tarski(sK2(X2,k1_xboole_0)) | sK2(X2,k1_xboole_0) = X2 | k1_xboole_0 = k1_tarski(X2)).
% 1.66/0.62  
% 1.66/0.62  cnf(u63,negated_conjecture,
% 1.66/0.62      k1_xboole_0 = k1_tarski(sK0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u68,axiom,
% 1.66/0.62      sK2(sK2(X1,k1_tarski(X2)),k1_tarski(X2)) = X2 | k1_tarski(X2) = k1_tarski(sK2(X1,k1_tarski(X2))) | sK2(X1,k1_tarski(X2)) = X1 | k1_tarski(X1) = k1_tarski(X2)).
% 1.66/0.62  
% 1.66/0.62  cnf(u38,axiom,
% 1.66/0.62      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.66/0.62  
% 1.66/0.62  cnf(u74,negated_conjecture,
% 1.66/0.62      sK2(X2,k1_xboole_0) = X2 | sK0 = sK2(X2,k1_xboole_0) | k1_xboole_0 = k1_tarski(X2)).
% 1.66/0.62  
% 1.66/0.62  cnf(u145,negated_conjecture,
% 1.66/0.62      sK2(X8,k1_xboole_0) = X8 | sK2(X7,k1_xboole_0) = sK2(X8,k1_xboole_0) | sK2(X7,k1_xboole_0) = X7 | k1_xboole_0 = k1_tarski(X8) | k1_xboole_0 = k1_tarski(X7)).
% 1.66/0.62  
% 1.66/0.62  cnf(u145,negated_conjecture,
% 1.66/0.62      sK2(X8,k1_xboole_0) = X8 | sK2(X7,k1_xboole_0) = sK2(X8,k1_xboole_0) | sK2(X7,k1_xboole_0) = X7 | k1_xboole_0 = k1_tarski(X8) | k1_xboole_0 = k1_tarski(X7)).
% 1.66/0.62  
% 1.66/0.62  cnf(u38,axiom,
% 1.66/0.62      sK2(X0,k1_tarski(X1)) = X0 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.66/0.62  
% 1.66/0.62  cnf(u131,axiom,
% 1.66/0.62      sK2(X14,k1_tarski(X13)) = X14 | sK2(X12,k1_tarski(X13)) = sK2(X14,k1_tarski(X13)) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14) | k1_tarski(X13) = k1_tarski(X12)).
% 1.66/0.62  
% 1.66/0.62  cnf(u131,axiom,
% 1.66/0.62      sK2(X14,k1_tarski(X13)) = X14 | sK2(X12,k1_tarski(X13)) = sK2(X14,k1_tarski(X13)) | sK2(X12,k1_tarski(X13)) = X12 | k1_tarski(X13) = k1_tarski(X14) | k1_tarski(X13) = k1_tarski(X12)).
% 1.66/0.62  
% 1.66/0.62  cnf(u319,negated_conjecture,
% 1.66/0.62      sK2(X1,k1_xboole_0) != X0 | sK2(X1,k1_xboole_0) = X1 | sK2(X0,k1_xboole_0) = X0 | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u317,negated_conjecture,
% 1.66/0.62      sK2(X1,k1_xboole_0) != X0 | sK2(X0,k1_xboole_0) = sK2(X1,k1_xboole_0) | sK2(X1,k1_xboole_0) = X1 | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X1)).
% 1.66/0.62  
% 1.66/0.62  cnf(u222,axiom,
% 1.66/0.62      sK2(X2,k1_tarski(X1)) != X0 | sK2(X2,k1_tarski(X1)) = X2 | sK2(X0,k1_tarski(X1)) = X0 | k1_tarski(X1) = k1_tarski(X2) | k1_tarski(X0) = k1_tarski(X1)).
% 1.66/0.62  
% 1.66/0.62  cnf(u220,axiom,
% 1.66/0.62      sK2(X2,k1_tarski(X1)) != X0 | sK2(X0,k1_tarski(X1)) = sK2(X2,k1_tarski(X1)) | sK2(X2,k1_tarski(X1)) = X2 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X1) = k1_tarski(X2)).
% 1.66/0.62  
% 1.66/0.62  cnf(u55,axiom,
% 1.66/0.62      X0 != X1 | sK2(X0,k1_tarski(X1)) = X1 | k1_tarski(X0) = k1_tarski(X1)).
% 1.66/0.62  
% 1.66/0.62  cnf(u61,axiom,
% 1.66/0.62      X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK2(X0,k1_tarski(X1)) = X0).
% 1.66/0.62  
% 1.66/0.62  cnf(u102,negated_conjecture,
% 1.66/0.62      sK0 != X0 | sK0 = sK2(X0,k1_xboole_0) | k1_xboole_0 = k1_tarski(X0)).
% 1.66/0.62  
% 1.66/0.62  cnf(u108,negated_conjecture,
% 1.66/0.62      sK0 != X0 | k1_xboole_0 = k1_tarski(X0) | sK2(X0,k1_xboole_0) = X0).
% 1.66/0.62  
% 1.66/0.62  cnf(u19,negated_conjecture,
% 1.66/0.62      sK0 != sK1).
% 1.66/0.62  
% 1.66/0.62  % (21744)# SZS output end Saturation.
% 1.66/0.62  % (21744)------------------------------
% 1.66/0.62  % (21744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.62  % (21744)Termination reason: Satisfiable
% 1.66/0.62  
% 1.66/0.62  % (21744)Memory used [KB]: 1791
% 1.66/0.62  % (21744)Time elapsed: 0.158 s
% 1.66/0.62  % (21744)------------------------------
% 1.66/0.62  % (21744)------------------------------
% 1.66/0.62  % (21736)Success in time 0.246 s
%------------------------------------------------------------------------------
