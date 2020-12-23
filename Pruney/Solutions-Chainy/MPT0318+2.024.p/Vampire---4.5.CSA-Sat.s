%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:19 EST 2020

% Result     : CounterSatisfiable 2.83s
% Output     : Saturation 2.83s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u52,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2) )).

cnf(u41,axiom,
    ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X0,X2) )).

cnf(u34,axiom,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u33,axiom,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) )).

cnf(u82,negated_conjecture,
    ( ~ r2_hidden(sK1,X1)
    | ~ r1_xboole_0(k1_xboole_0,X1) )).

cnf(u65,negated_conjecture,
    ( ~ r2_hidden(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) )).

cnf(u55,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u39,axiom,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(X0,X2) )).

cnf(u40,axiom,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    | r2_hidden(X1,X3) )).

cnf(u66,negated_conjecture,
    ( v1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) )).

cnf(u56,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u32,axiom,
    ( ~ v1_xboole_0(X0)
    | ~ r2_hidden(X2,X0) )).

cnf(u78,negated_conjecture,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

cnf(u81,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK0) )).

cnf(u51,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) )).

cnf(u28,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (31336)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (31328)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (31328)Refutation not found, incomplete strategy% (31328)------------------------------
% 0.21/0.52  % (31328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31345)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (31317)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31317)Refutation not found, incomplete strategy% (31317)------------------------------
% 0.21/0.52  % (31317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31317)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31317)Memory used [KB]: 1663
% 0.21/0.52  % (31317)Time elapsed: 0.115 s
% 0.21/0.52  % (31317)------------------------------
% 0.21/0.52  % (31317)------------------------------
% 0.21/0.52  % (31327)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (31328)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31328)Memory used [KB]: 10618
% 0.21/0.52  % (31328)Time elapsed: 0.109 s
% 0.21/0.52  % (31328)------------------------------
% 0.21/0.52  % (31328)------------------------------
% 0.21/0.52  % (31330)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (31327)Refutation not found, incomplete strategy% (31327)------------------------------
% 0.21/0.53  % (31327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31327)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31327)Memory used [KB]: 10618
% 0.21/0.53  % (31327)Time elapsed: 0.117 s
% 0.21/0.53  % (31327)------------------------------
% 0.21/0.53  % (31327)------------------------------
% 0.21/0.53  % (31318)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31343)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (31340)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (31323)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (31335)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (31341)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (31319)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (31322)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31324)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (31321)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (31319)Refutation not found, incomplete strategy% (31319)------------------------------
% 0.21/0.54  % (31319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31319)Memory used [KB]: 10746
% 0.21/0.54  % (31319)Time elapsed: 0.126 s
% 0.21/0.54  % (31319)------------------------------
% 0.21/0.54  % (31319)------------------------------
% 1.42/0.55  % (31333)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.55  % (31332)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (31344)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (31339)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.55  % (31331)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.55  % (31325)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (31325)Refutation not found, incomplete strategy% (31325)------------------------------
% 1.42/0.55  % (31325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (31325)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (31325)Memory used [KB]: 10618
% 1.42/0.55  % (31325)Time elapsed: 0.151 s
% 1.42/0.55  % (31325)------------------------------
% 1.42/0.55  % (31325)------------------------------
% 1.42/0.56  % (31342)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.56  % (31344)Refutation not found, incomplete strategy% (31344)------------------------------
% 1.42/0.56  % (31344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31344)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (31344)Memory used [KB]: 6268
% 1.42/0.56  % (31344)Time elapsed: 0.145 s
% 1.42/0.56  % (31344)------------------------------
% 1.42/0.56  % (31344)------------------------------
% 1.42/0.56  % (31346)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.56  % (31338)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (31346)Refutation not found, incomplete strategy% (31346)------------------------------
% 1.42/0.56  % (31346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (31329)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (31320)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.56  % (31337)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.57  % (31338)Refutation not found, incomplete strategy% (31338)------------------------------
% 1.56/0.57  % (31338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (31338)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (31337)Refutation not found, incomplete strategy% (31337)------------------------------
% 1.56/0.57  % (31337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (31338)Memory used [KB]: 1663
% 1.56/0.57  % (31338)Time elapsed: 0.160 s
% 1.56/0.57  % (31337)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  % (31338)------------------------------
% 1.56/0.57  % (31338)------------------------------
% 1.56/0.57  
% 1.56/0.57  % (31337)Memory used [KB]: 10746
% 1.56/0.57  % (31337)Time elapsed: 0.157 s
% 1.56/0.57  % (31337)------------------------------
% 1.56/0.57  % (31337)------------------------------
% 1.56/0.57  % (31346)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (31346)Memory used [KB]: 1663
% 1.56/0.57  % (31346)Time elapsed: 0.152 s
% 1.56/0.57  % (31346)------------------------------
% 1.56/0.57  % (31346)------------------------------
% 1.56/0.57  % (31339)Refutation not found, incomplete strategy% (31339)------------------------------
% 1.56/0.57  % (31339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (31339)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (31339)Memory used [KB]: 10746
% 1.56/0.57  % (31339)Time elapsed: 0.141 s
% 1.56/0.57  % (31339)------------------------------
% 1.56/0.57  % (31339)------------------------------
% 1.56/0.57  % (31326)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.59  % (31334)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.59  % (31334)Refutation not found, incomplete strategy% (31334)------------------------------
% 1.56/0.59  % (31334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (31334)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (31334)Memory used [KB]: 10618
% 1.56/0.59  % (31334)Time elapsed: 0.153 s
% 1.56/0.59  % (31334)------------------------------
% 1.56/0.59  % (31334)------------------------------
% 1.56/0.59  % (31326)Refutation not found, incomplete strategy% (31326)------------------------------
% 1.56/0.59  % (31326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (31326)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (31326)Memory used [KB]: 10618
% 1.56/0.59  % (31326)Time elapsed: 0.164 s
% 1.56/0.59  % (31326)------------------------------
% 1.56/0.59  % (31326)------------------------------
% 2.15/0.69  % (31350)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.15/0.69  % (31350)Refutation not found, incomplete strategy% (31350)------------------------------
% 2.15/0.69  % (31350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.69  % (31350)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.69  
% 2.15/0.69  % (31350)Memory used [KB]: 6140
% 2.15/0.69  % (31350)Time elapsed: 0.134 s
% 2.15/0.69  % (31350)------------------------------
% 2.15/0.69  % (31350)------------------------------
% 2.15/0.69  % (31358)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.15/0.71  % (31351)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.15/0.72  % (31354)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.15/0.72  % (31352)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.15/0.73  % (31318)Refutation not found, incomplete strategy% (31318)------------------------------
% 2.15/0.73  % (31318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.73  % (31318)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.73  
% 2.15/0.73  % (31318)Memory used [KB]: 6268
% 2.15/0.73  % (31318)Time elapsed: 0.260 s
% 2.15/0.73  % (31318)------------------------------
% 2.15/0.73  % (31318)------------------------------
% 2.52/0.73  % (31355)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.52/0.74  % (31352)Refutation not found, incomplete strategy% (31352)------------------------------
% 2.52/0.74  % (31352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.74  % (31352)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.74  
% 2.52/0.74  % (31352)Memory used [KB]: 6268
% 2.52/0.74  % (31352)Time elapsed: 0.143 s
% 2.52/0.74  % (31352)------------------------------
% 2.52/0.74  % (31352)------------------------------
% 2.52/0.74  % (31354)Refutation not found, incomplete strategy% (31354)------------------------------
% 2.52/0.74  % (31354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.52/0.74  % (31354)Termination reason: Refutation not found, incomplete strategy
% 2.52/0.74  
% 2.52/0.74  % (31354)Memory used [KB]: 10746
% 2.52/0.74  % (31354)Time elapsed: 0.154 s
% 2.52/0.74  % (31354)------------------------------
% 2.52/0.74  % (31354)------------------------------
% 2.52/0.76  % (31368)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.52/0.76  % (31369)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.83/0.77  % (31353)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.83/0.77  % (31377)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.83/0.78  % (31381)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.83/0.79  % SZS status CounterSatisfiable for theBenchmark
% 2.83/0.79  % (31369)# SZS output start Saturation.
% 2.83/0.79  cnf(u30,axiom,
% 2.83/0.79      r1_xboole_0(X0,k1_xboole_0)).
% 2.83/0.79  
% 2.83/0.79  cnf(u52,axiom,
% 2.83/0.79      ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)).
% 2.83/0.79  
% 2.83/0.79  cnf(u41,axiom,
% 2.83/0.79      r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)).
% 2.83/0.79  
% 2.83/0.79  cnf(u34,axiom,
% 2.83/0.79      r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0).
% 2.83/0.79  
% 2.83/0.79  cnf(u33,axiom,
% 2.83/0.79      r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)).
% 2.83/0.79  
% 2.83/0.79  cnf(u82,negated_conjecture,
% 2.83/0.79      ~r2_hidden(sK1,X1) | ~r1_xboole_0(k1_xboole_0,X1)).
% 2.83/0.79  
% 2.83/0.79  cnf(u65,negated_conjecture,
% 2.83/0.79      ~r2_hidden(X1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))).
% 2.83/0.79  
% 2.83/0.79  cnf(u55,axiom,
% 2.83/0.79      ~r2_hidden(X0,k1_xboole_0)).
% 2.83/0.79  
% 2.83/0.79  cnf(u39,axiom,
% 2.83/0.79      ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)).
% 2.83/0.79  
% 2.83/0.79  cnf(u40,axiom,
% 2.83/0.79      ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)).
% 2.83/0.79  
% 2.83/0.79  cnf(u66,negated_conjecture,
% 2.83/0.79      v1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))).
% 2.83/0.79  
% 2.83/0.79  cnf(u56,axiom,
% 2.83/0.79      v1_xboole_0(k1_xboole_0)).
% 2.83/0.79  
% 2.83/0.79  cnf(u32,axiom,
% 2.83/0.79      ~v1_xboole_0(X0) | ~r2_hidden(X2,X0)).
% 2.83/0.79  
% 2.83/0.79  cnf(u78,negated_conjecture,
% 2.83/0.79      k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)).
% 2.83/0.79  
% 2.83/0.79  cnf(u81,negated_conjecture,
% 2.83/0.79      k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK0)).
% 2.83/0.79  
% 2.83/0.79  cnf(u51,negated_conjecture,
% 2.83/0.79      k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))).
% 2.83/0.79  
% 2.83/0.79  cnf(u28,negated_conjecture,
% 2.83/0.79      k1_xboole_0 != sK0).
% 2.83/0.79  
% 2.83/0.79  % (31369)# SZS output end Saturation.
% 2.83/0.79  % (31369)------------------------------
% 2.83/0.79  % (31369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.79  % (31369)Termination reason: Satisfiable
% 2.83/0.79  
% 2.83/0.79  % (31369)Memory used [KB]: 6268
% 2.83/0.79  % (31369)Time elapsed: 0.163 s
% 2.83/0.79  % (31369)------------------------------
% 2.83/0.79  % (31369)------------------------------
% 2.83/0.79  % (31316)Success in time 0.433 s
%------------------------------------------------------------------------------
