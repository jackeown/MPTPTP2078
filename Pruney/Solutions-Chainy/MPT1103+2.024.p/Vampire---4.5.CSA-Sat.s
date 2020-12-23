%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:37 EST 2020

% Result     : CounterSatisfiable 1.65s
% Output     : Saturation 1.65s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u48,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u37,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u49,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u50,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u45,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u52,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u41,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u107,axiom,
    ( k1_setfam_1(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = k7_subset_1(X2,X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u81,axiom,
    ( k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3)) )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u85,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u87,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u54,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u88,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u115,axiom,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1)))) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u112,axiom,
    ( k5_xboole_0(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X6)) = k5_xboole_0(k7_subset_1(k1_xboole_0,k1_xboole_0,X6),k1_setfam_1(k2_tarski(k1_xboole_0,X6))) )).

cnf(u110,axiom,
    ( k5_xboole_0(X2,k7_subset_1(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3),X2)) = k5_xboole_0(k7_subset_1(X2,X2,X3),k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u68,axiom,
    ( k5_xboole_0(X0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) )).

cnf(u59,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u42,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u63,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u26,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u28,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u47,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:23:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6314)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (6306)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (6297)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (6298)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (6306)Refutation not found, incomplete strategy% (6306)------------------------------
% 0.21/0.52  % (6306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6306)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6306)Memory used [KB]: 10746
% 0.21/0.52  % (6306)Time elapsed: 0.059 s
% 0.21/0.52  % (6306)------------------------------
% 0.21/0.52  % (6306)------------------------------
% 0.21/0.52  % (6297)Refutation not found, incomplete strategy% (6297)------------------------------
% 0.21/0.52  % (6297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6297)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6297)Memory used [KB]: 10618
% 0.21/0.52  % (6297)Time elapsed: 0.107 s
% 0.21/0.52  % (6297)------------------------------
% 0.21/0.52  % (6297)------------------------------
% 0.21/0.52  % (6298)Refutation not found, incomplete strategy% (6298)------------------------------
% 0.21/0.52  % (6298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6305)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (6313)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (6286)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (6286)Refutation not found, incomplete strategy% (6286)------------------------------
% 0.21/0.53  % (6286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6286)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6286)Memory used [KB]: 1663
% 0.21/0.53  % (6286)Time elapsed: 0.123 s
% 0.21/0.53  % (6286)------------------------------
% 0.21/0.53  % (6286)------------------------------
% 0.21/0.53  % (6291)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (6289)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (6298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6298)Memory used [KB]: 6268
% 0.21/0.53  % (6298)Time elapsed: 0.075 s
% 0.21/0.53  % (6298)------------------------------
% 0.21/0.53  % (6298)------------------------------
% 0.21/0.54  % (6289)Refutation not found, incomplete strategy% (6289)------------------------------
% 0.21/0.54  % (6289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6289)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6289)Memory used [KB]: 10746
% 0.21/0.54  % (6289)Time elapsed: 0.126 s
% 0.21/0.54  % (6289)------------------------------
% 0.21/0.54  % (6289)------------------------------
% 0.21/0.54  % (6310)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (6290)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (6311)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (6308)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (6308)Refutation not found, incomplete strategy% (6308)------------------------------
% 0.21/0.54  % (6308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (6308)Memory used [KB]: 10746
% 0.21/0.54  % (6308)Time elapsed: 0.134 s
% 0.21/0.54  % (6308)------------------------------
% 0.21/0.54  % (6308)------------------------------
% 0.21/0.55  % (6287)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (6307)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (6303)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (6294)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (6288)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (6303)Refutation not found, incomplete strategy% (6303)------------------------------
% 0.21/0.55  % (6303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6303)Memory used [KB]: 10618
% 0.21/0.55  % (6303)Time elapsed: 0.145 s
% 0.21/0.55  % (6303)------------------------------
% 0.21/0.55  % (6303)------------------------------
% 0.21/0.55  % (6294)Refutation not found, incomplete strategy% (6294)------------------------------
% 0.21/0.55  % (6294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6294)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6294)Memory used [KB]: 10746
% 0.21/0.55  % (6294)Time elapsed: 0.149 s
% 0.21/0.55  % (6294)------------------------------
% 0.21/0.55  % (6294)------------------------------
% 0.21/0.55  % (6293)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (6292)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (6295)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (6295)Refutation not found, incomplete strategy% (6295)------------------------------
% 0.21/0.55  % (6295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6295)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (6295)Memory used [KB]: 10618
% 0.21/0.55  % (6295)Time elapsed: 0.147 s
% 0.21/0.55  % (6295)------------------------------
% 0.21/0.55  % (6295)------------------------------
% 0.21/0.56  % (6301)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (6300)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (6301)Refutation not found, incomplete strategy% (6301)------------------------------
% 0.21/0.56  % (6301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (6301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (6301)Memory used [KB]: 6140
% 0.21/0.56  % (6301)Time elapsed: 0.001 s
% 0.21/0.56  % (6301)------------------------------
% 0.21/0.56  % (6301)------------------------------
% 0.21/0.56  % (6309)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.65/0.56  % (6290)Refutation not found, incomplete strategy% (6290)------------------------------
% 1.65/0.56  % (6290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.56  % (6290)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.56  
% 1.65/0.56  % (6290)Memory used [KB]: 6268
% 1.65/0.56  % (6290)Time elapsed: 0.135 s
% 1.65/0.56  % (6290)------------------------------
% 1.65/0.56  % (6290)------------------------------
% 1.65/0.56  % (6309)Refutation not found, incomplete strategy% (6309)------------------------------
% 1.65/0.56  % (6309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.56  % (6309)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.56  
% 1.65/0.56  % (6309)Memory used [KB]: 1791
% 1.65/0.56  % (6309)Time elapsed: 0.154 s
% 1.65/0.56  % (6309)------------------------------
% 1.65/0.56  % (6309)------------------------------
% 1.65/0.56  % (6299)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.65/0.57  % (6302)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.65/0.57  % (6307)Refutation not found, incomplete strategy% (6307)------------------------------
% 1.65/0.57  % (6307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.57  % (6307)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.57  
% 1.65/0.57  % (6307)Memory used [KB]: 1791
% 1.65/0.57  % (6307)Time elapsed: 0.134 s
% 1.65/0.57  % (6307)------------------------------
% 1.65/0.57  % (6307)------------------------------
% 1.65/0.57  % (6312)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.57  % SZS status CounterSatisfiable for theBenchmark
% 1.65/0.57  % (6292)# SZS output start Saturation.
% 1.65/0.57  cnf(u48,axiom,
% 1.65/0.57      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u25,negated_conjecture,
% 1.65/0.57      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.65/0.57  
% 1.65/0.57  cnf(u37,axiom,
% 1.65/0.57      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u55,axiom,
% 1.65/0.57      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.65/0.57  
% 1.65/0.57  cnf(u49,negated_conjecture,
% 1.65/0.57      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u50,axiom,
% 1.65/0.57      r1_tarski(X0,X0)).
% 1.65/0.57  
% 1.65/0.57  cnf(u45,axiom,
% 1.65/0.57      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 1.65/0.57  
% 1.65/0.57  cnf(u52,negated_conjecture,
% 1.65/0.57      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.65/0.57  
% 1.65/0.57  cnf(u41,axiom,
% 1.65/0.57      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u107,axiom,
% 1.65/0.57      k1_setfam_1(k2_tarski(X2,k7_subset_1(X2,X2,X3))) = k7_subset_1(X2,X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.65/0.57  
% 1.65/0.57  cnf(u81,axiom,
% 1.65/0.57      k7_subset_1(X2,X2,k7_subset_1(X2,X2,X3)) = k1_setfam_1(k2_tarski(X2,X3))).
% 1.65/0.57  
% 1.65/0.57  cnf(u58,negated_conjecture,
% 1.65/0.57      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.65/0.57  
% 1.65/0.57  cnf(u85,axiom,
% 1.65/0.57      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 1.65/0.57  
% 1.65/0.57  cnf(u87,negated_conjecture,
% 1.65/0.57      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 1.65/0.57  
% 1.65/0.57  cnf(u23,negated_conjecture,
% 1.65/0.57      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.65/0.57  
% 1.65/0.57  cnf(u54,axiom,
% 1.65/0.57      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.65/0.57  
% 1.65/0.57  cnf(u88,negated_conjecture,
% 1.65/0.57      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 1.65/0.57  
% 1.65/0.57  cnf(u115,axiom,
% 1.65/0.57      k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,k1_setfam_1(k2_tarski(X0,X1))))).
% 1.65/0.57  
% 1.65/0.57  cnf(u84,axiom,
% 1.65/0.57      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.65/0.57  
% 1.65/0.57  cnf(u112,axiom,
% 1.65/0.57      k5_xboole_0(k1_xboole_0,k7_subset_1(k1_xboole_0,k1_xboole_0,X6)) = k5_xboole_0(k7_subset_1(k1_xboole_0,k1_xboole_0,X6),k1_setfam_1(k2_tarski(k1_xboole_0,X6)))).
% 1.65/0.57  
% 1.65/0.57  cnf(u110,axiom,
% 1.65/0.57      k5_xboole_0(X2,k7_subset_1(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3),X2)) = k5_xboole_0(k7_subset_1(X2,X2,X3),k1_setfam_1(k2_tarski(X2,X3)))).
% 1.65/0.57  
% 1.65/0.57  cnf(u68,axiom,
% 1.65/0.57      k5_xboole_0(X0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0)).
% 1.65/0.57  
% 1.65/0.57  cnf(u59,axiom,
% 1.65/0.57      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 1.65/0.57  
% 1.65/0.57  cnf(u42,axiom,
% 1.65/0.57      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.65/0.57  
% 1.65/0.57  cnf(u63,axiom,
% 1.65/0.57      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.65/0.57  
% 1.65/0.57  cnf(u26,axiom,
% 1.65/0.57      k2_subset_1(X0) = X0).
% 1.65/0.57  
% 1.65/0.57  cnf(u28,axiom,
% 1.65/0.57      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.65/0.57  
% 1.65/0.57  cnf(u47,negated_conjecture,
% 1.65/0.57      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.65/0.57  
% 1.65/0.57  % (6292)# SZS output end Saturation.
% 1.65/0.57  % (6292)------------------------------
% 1.65/0.57  % (6292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.57  % (6292)Termination reason: Satisfiable
% 1.65/0.57  
% 1.65/0.57  % (6292)Memory used [KB]: 6268
% 1.65/0.57  % (6292)Time elapsed: 0.141 s
% 1.65/0.57  % (6292)------------------------------
% 1.65/0.57  % (6292)------------------------------
% 1.65/0.57  % (6285)Success in time 0.208 s
%------------------------------------------------------------------------------
