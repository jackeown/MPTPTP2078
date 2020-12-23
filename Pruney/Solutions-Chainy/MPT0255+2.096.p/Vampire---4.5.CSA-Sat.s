%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   38 (  38 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u54,axiom,
    ( r1_tarski(X0,X1)
    | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u37,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u64,axiom,
    ( r2_xboole_0(X0,X1)
    | X0 = X1
    | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u55,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X1,X0)) )).

cnf(u86,axiom,
    ( k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) )).

cnf(u83,axiom,
    ( k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) )).

cnf(u53,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) )).

cnf(u130,axiom,
    ( k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) )).

cnf(u159,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k3_tarski(k1_xboole_0) )).

cnf(u30,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u156,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) )).

cnf(u150,negated_conjecture,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) )).

cnf(u158,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) )).

cnf(u161,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_tarski(k1_xboole_0))) )).

cnf(u99,axiom,
    ( k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5)) )).

cnf(u88,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))) )).

cnf(u85,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )).

cnf(u52,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )).

cnf(u56,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u29,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u32,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u123,axiom,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X5,X6))),k3_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X5,X6)))))
    | k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X5,X6))) = X5 )).

cnf(u102,axiom,
    ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))))
    | k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = X2 )).

cnf(u76,axiom,
    ( k1_xboole_0 != k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 )).

cnf(u167,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(k3_tarski(k1_xboole_0),k3_xboole_0(sK0,k3_tarski(k1_xboole_0)))
    | sK0 = k3_tarski(k1_xboole_0) )).

cnf(u75,axiom,
    ( k1_xboole_0 != k5_xboole_0(X5,k1_xboole_0)
    | k1_xboole_0 = X5 )).

cnf(u68,axiom,
    ( k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X2,X1))
    | k1_xboole_0 != k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | X1 = X2 )).

cnf(u65,axiom,
    ( k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X1,X0))
    | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | X0 = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:57:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (21946)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (21969)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (21946)Refutation not found, incomplete strategy% (21946)------------------------------
% 0.21/0.51  % (21946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21969)Refutation not found, incomplete strategy% (21969)------------------------------
% 0.21/0.51  % (21969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21955)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21955)Refutation not found, incomplete strategy% (21955)------------------------------
% 0.21/0.51  % (21955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21969)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21969)Memory used [KB]: 10746
% 0.21/0.51  % (21969)Time elapsed: 0.109 s
% 0.21/0.51  % (21969)------------------------------
% 0.21/0.51  % (21969)------------------------------
% 0.21/0.52  % (21946)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21946)Memory used [KB]: 10874
% 0.21/0.52  % (21946)Time elapsed: 0.100 s
% 0.21/0.52  % (21946)------------------------------
% 0.21/0.52  % (21946)------------------------------
% 0.21/0.52  % (21955)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21955)Memory used [KB]: 6268
% 0.21/0.52  % (21955)Time elapsed: 0.116 s
% 0.21/0.52  % (21955)------------------------------
% 0.21/0.52  % (21955)------------------------------
% 0.21/0.52  % (21963)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (21947)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (21947)Refutation not found, incomplete strategy% (21947)------------------------------
% 0.21/0.52  % (21947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21947)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21947)Memory used [KB]: 6140
% 0.21/0.52  % (21947)Time elapsed: 0.112 s
% 0.21/0.52  % (21947)------------------------------
% 0.21/0.52  % (21947)------------------------------
% 0.21/0.52  % (21950)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (21954)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (21963)Refutation not found, incomplete strategy% (21963)------------------------------
% 0.21/0.53  % (21963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21954)Refutation not found, incomplete strategy% (21954)------------------------------
% 0.21/0.53  % (21954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21954)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21954)Memory used [KB]: 10618
% 0.21/0.53  % (21954)Time elapsed: 0.126 s
% 0.21/0.53  % (21954)------------------------------
% 0.21/0.53  % (21954)------------------------------
% 0.21/0.53  % (21963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21963)Memory used [KB]: 10746
% 0.21/0.53  % (21963)Time elapsed: 0.117 s
% 0.21/0.53  % (21963)------------------------------
% 0.21/0.53  % (21963)------------------------------
% 0.21/0.53  % (21953)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (21953)Refutation not found, incomplete strategy% (21953)------------------------------
% 0.21/0.53  % (21953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21953)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21953)Memory used [KB]: 10618
% 0.21/0.53  % (21953)Time elapsed: 0.116 s
% 0.21/0.53  % (21953)------------------------------
% 0.21/0.53  % (21953)------------------------------
% 0.21/0.53  % (21950)Refutation not found, incomplete strategy% (21950)------------------------------
% 0.21/0.53  % (21950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21945)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21962)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (21966)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21943)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (21950)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21950)Memory used [KB]: 6268
% 0.21/0.54  % (21950)Time elapsed: 0.118 s
% 0.21/0.54  % (21950)------------------------------
% 0.21/0.54  % (21950)------------------------------
% 0.21/0.54  % (21943)Refutation not found, incomplete strategy% (21943)------------------------------
% 0.21/0.54  % (21943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21943)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21943)Memory used [KB]: 1663
% 0.21/0.54  % (21943)Time elapsed: 0.133 s
% 0.21/0.54  % (21943)------------------------------
% 0.21/0.54  % (21943)------------------------------
% 0.21/0.54  % (21952)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (21952)Refutation not found, incomplete strategy% (21952)------------------------------
% 0.21/0.54  % (21952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21952)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21952)Memory used [KB]: 10618
% 0.21/0.54  % (21952)Time elapsed: 0.134 s
% 0.21/0.54  % (21952)------------------------------
% 0.21/0.54  % (21952)------------------------------
% 0.21/0.54  % (21958)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (21958)Refutation not found, incomplete strategy% (21958)------------------------------
% 0.21/0.54  % (21958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21965)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (21966)Refutation not found, incomplete strategy% (21966)------------------------------
% 0.21/0.54  % (21966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21958)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21958)Memory used [KB]: 6140
% 0.21/0.54  % (21958)Time elapsed: 0.003 s
% 0.21/0.54  % (21958)------------------------------
% 0.21/0.54  % (21958)------------------------------
% 0.21/0.54  % (21966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21966)Memory used [KB]: 1663
% 0.21/0.54  % (21966)Time elapsed: 0.126 s
% 0.21/0.54  % (21966)------------------------------
% 0.21/0.54  % (21966)------------------------------
% 0.21/0.55  % (21964)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (21965)Refutation not found, incomplete strategy% (21965)------------------------------
% 0.21/0.55  % (21965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21965)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21965)Memory used [KB]: 10746
% 0.21/0.55  % (21965)Time elapsed: 0.139 s
% 0.21/0.55  % (21965)------------------------------
% 0.21/0.55  % (21965)------------------------------
% 0.21/0.55  % (21968)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21964)Refutation not found, incomplete strategy% (21964)------------------------------
% 0.21/0.55  % (21964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21964)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21964)Memory used [KB]: 1791
% 0.21/0.55  % (21964)Time elapsed: 0.109 s
% 0.21/0.55  % (21964)------------------------------
% 0.21/0.55  % (21964)------------------------------
% 0.21/0.55  % (21960)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (21970)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21956)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (21968)Refutation not found, incomplete strategy% (21968)------------------------------
% 0.21/0.55  % (21968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21968)Memory used [KB]: 6268
% 0.21/0.55  % (21968)Time elapsed: 0.150 s
% 0.21/0.55  % (21968)------------------------------
% 0.21/0.55  % (21968)------------------------------
% 0.21/0.55  % (21951)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21945)Refutation not found, incomplete strategy% (21945)------------------------------
% 0.21/0.55  % (21945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21945)Memory used [KB]: 10746
% 0.21/0.55  % (21945)Time elapsed: 0.144 s
% 0.21/0.55  % (21945)------------------------------
% 0.21/0.55  % (21945)------------------------------
% 0.21/0.55  % (21949)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (21960)Refutation not found, incomplete strategy% (21960)------------------------------
% 0.21/0.55  % (21960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21960)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21960)Memory used [KB]: 10618
% 0.21/0.55  % (21960)Time elapsed: 0.149 s
% 0.21/0.55  % (21960)------------------------------
% 0.21/0.55  % (21960)------------------------------
% 0.21/0.55  % (21957)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (21948)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (21962)Refutation not found, incomplete strategy% (21962)------------------------------
% 0.21/0.56  % (21962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21944)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (21972)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.57  % (21951)Refutation not found, incomplete strategy% (21951)------------------------------
% 0.21/0.57  % (21951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21951)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21951)Memory used [KB]: 10746
% 0.21/0.57  % (21951)Time elapsed: 0.147 s
% 0.21/0.57  % (21951)------------------------------
% 0.21/0.57  % (21951)------------------------------
% 0.21/0.58  % (21961)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (21949)# SZS output start Saturation.
% 0.21/0.58  cnf(u54,axiom,
% 0.21/0.58      r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u37,axiom,
% 0.21/0.58      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u64,axiom,
% 0.21/0.58      r2_xboole_0(X0,X1) | X0 = X1 | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.58  
% 0.21/0.58  cnf(u55,axiom,
% 0.21/0.58      ~r2_xboole_0(X0,X1) | k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X1,X0))).
% 0.21/0.58  
% 0.21/0.58  cnf(u86,axiom,
% 0.21/0.58      k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u83,axiom,
% 0.21/0.58      k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)) = k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u53,axiom,
% 0.21/0.58      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u130,axiom,
% 0.21/0.58      k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u159,negated_conjecture,
% 0.21/0.58      k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k3_tarski(k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u30,axiom,
% 0.21/0.58      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u156,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))).
% 0.21/0.58  
% 0.21/0.58  cnf(u150,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)).
% 0.21/0.58  
% 0.21/0.58  cnf(u158,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)).
% 0.21/0.58  
% 0.21/0.58  cnf(u161,negated_conjecture,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_tarski(k1_xboole_0)))).
% 0.21/0.58  
% 0.21/0.58  cnf(u99,axiom,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(X5,k3_xboole_0(X5,X5))).
% 0.21/0.58  
% 0.21/0.58  cnf(u88,axiom,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))))).
% 0.21/0.58  
% 0.21/0.58  cnf(u85,axiom,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))).
% 0.21/0.58  
% 0.21/0.58  cnf(u52,axiom,
% 0.21/0.58      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))).
% 0.21/0.58  
% 0.21/0.58  cnf(u56,axiom,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u29,axiom,
% 0.21/0.58      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u32,axiom,
% 0.21/0.58      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u123,axiom,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X5,X6))),k3_xboole_0(X5,k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X5,X6))))) | k5_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X5,X6))) = X5).
% 0.21/0.58  
% 0.21/0.58  cnf(u102,axiom,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))),k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))) | k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = X2).
% 0.21/0.58  
% 0.21/0.58  cnf(u76,axiom,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0).
% 0.21/0.58  
% 0.21/0.58  cnf(u167,negated_conjecture,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(k3_tarski(k1_xboole_0),k3_xboole_0(sK0,k3_tarski(k1_xboole_0))) | sK0 = k3_tarski(k1_xboole_0)).
% 0.21/0.58  
% 0.21/0.58  cnf(u75,axiom,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(X5,k1_xboole_0) | k1_xboole_0 = X5).
% 0.21/0.58  
% 0.21/0.58  cnf(u68,axiom,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X2,X1)) | k1_xboole_0 != k5_xboole_0(X2,k3_xboole_0(X2,X1)) | X1 = X2).
% 0.21/0.58  
% 0.21/0.58  cnf(u65,axiom,
% 0.21/0.58      k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X1,X0)) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | X0 = X1).
% 0.21/0.58  
% 0.21/0.58  % (21949)# SZS output end Saturation.
% 0.21/0.58  % (21949)------------------------------
% 0.21/0.58  % (21949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (21949)Termination reason: Satisfiable
% 0.21/0.58  
% 0.21/0.58  % (21949)Memory used [KB]: 6396
% 0.21/0.58  % (21949)Time elapsed: 0.161 s
% 0.21/0.58  % (21949)------------------------------
% 0.21/0.58  % (21949)------------------------------
% 0.21/0.58  % (21962)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (21962)Memory used [KB]: 10874
% 0.21/0.58  % (21962)Time elapsed: 0.147 s
% 0.21/0.58  % (21962)------------------------------
% 0.21/0.58  % (21962)------------------------------
% 0.21/0.58  % (21942)Success in time 0.229 s
%------------------------------------------------------------------------------
