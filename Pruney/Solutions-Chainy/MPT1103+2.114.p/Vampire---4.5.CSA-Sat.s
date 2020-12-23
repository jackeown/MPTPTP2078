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
% DateTime   : Thu Dec  3 13:08:49 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) )).

cnf(u42,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u32,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u44,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

cnf(u40,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) )).

cnf(u39,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) )).

cnf(u34,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u37,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u38,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

% (32455)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
cnf(u45,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u21,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u31,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u30,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:57:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (32452)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.48  % (32452)Refutation not found, incomplete strategy% (32452)------------------------------
% 0.21/0.48  % (32452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32468)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.49  % (32469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (32452)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32452)Memory used [KB]: 6268
% 0.21/0.49  % (32452)Time elapsed: 0.095 s
% 0.21/0.49  % (32452)------------------------------
% 0.21/0.49  % (32452)------------------------------
% 0.21/0.50  % (32468)Refutation not found, incomplete strategy% (32468)------------------------------
% 0.21/0.50  % (32468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32460)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (32468)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32468)Memory used [KB]: 1663
% 0.21/0.50  % (32468)Time elapsed: 0.114 s
% 0.21/0.50  % (32468)------------------------------
% 0.21/0.50  % (32468)------------------------------
% 0.21/0.50  % (32469)Refutation not found, incomplete strategy% (32469)------------------------------
% 0.21/0.50  % (32469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32469)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32469)Memory used [KB]: 10618
% 0.21/0.50  % (32469)Time elapsed: 0.083 s
% 0.21/0.50  % (32469)------------------------------
% 0.21/0.50  % (32469)------------------------------
% 0.21/0.52  % (32449)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (32451)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32451)Refutation not found, incomplete strategy% (32451)------------------------------
% 0.21/0.52  % (32451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32451)Memory used [KB]: 6140
% 0.21/0.52  % (32451)Time elapsed: 0.116 s
% 0.21/0.52  % (32451)------------------------------
% 0.21/0.52  % (32451)------------------------------
% 0.21/0.52  % (32476)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (32461)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (32448)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (32458)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (32476)Refutation not found, incomplete strategy% (32476)------------------------------
% 0.21/0.53  % (32476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32476)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32476)Memory used [KB]: 1791
% 0.21/0.53  % (32476)Time elapsed: 0.133 s
% 0.21/0.53  % (32476)------------------------------
% 0.21/0.53  % (32476)------------------------------
% 0.21/0.53  % (32449)Refutation not found, incomplete strategy% (32449)------------------------------
% 0.21/0.53  % (32449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32465)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (32449)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32449)Memory used [KB]: 10618
% 0.21/0.53  % (32449)Time elapsed: 0.113 s
% 0.21/0.53  % (32449)------------------------------
% 0.21/0.53  % (32449)------------------------------
% 0.21/0.53  % (32471)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (32466)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (32458)Refutation not found, incomplete strategy% (32458)------------------------------
% 0.21/0.53  % (32458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32450)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32458)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32458)Memory used [KB]: 10618
% 0.21/0.53  % (32458)Time elapsed: 0.131 s
% 0.21/0.53  % (32458)------------------------------
% 0.21/0.53  % (32458)------------------------------
% 0.21/0.53  % (32447)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (32447)Refutation not found, incomplete strategy% (32447)------------------------------
% 0.21/0.53  % (32447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (32447)Memory used [KB]: 1663
% 0.21/0.53  % (32447)Time elapsed: 0.121 s
% 0.21/0.53  % (32447)------------------------------
% 0.21/0.53  % (32447)------------------------------
% 0.21/0.53  % (32470)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (32467)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (32450)Refutation not found, incomplete strategy% (32450)------------------------------
% 0.21/0.54  % (32450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32456)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (32459)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (32467)Refutation not found, incomplete strategy% (32467)------------------------------
% 0.21/0.54  % (32467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32450)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32450)Memory used [KB]: 10746
% 0.21/0.54  % (32450)Time elapsed: 0.126 s
% 0.21/0.54  % (32450)------------------------------
% 0.21/0.54  % (32450)------------------------------
% 0.21/0.54  % (32459)Refutation not found, incomplete strategy% (32459)------------------------------
% 0.21/0.54  % (32459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32467)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32467)Memory used [KB]: 10746
% 0.21/0.54  % (32467)Time elapsed: 0.125 s
% 0.21/0.54  % (32467)------------------------------
% 0.21/0.54  % (32467)------------------------------
% 0.21/0.54  % (32459)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32459)Memory used [KB]: 6268
% 0.21/0.54  % (32459)Time elapsed: 0.138 s
% 0.21/0.54  % (32459)------------------------------
% 0.21/0.54  % (32459)------------------------------
% 0.21/0.54  % (32464)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (32470)Refutation not found, incomplete strategy% (32470)------------------------------
% 0.21/0.54  % (32470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32470)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  % (32463)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (32462)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (32454)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (32473)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (32475)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (32462)Refutation not found, incomplete strategy% (32462)------------------------------
% 0.21/0.55  % (32462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32454)Refutation not found, incomplete strategy% (32454)------------------------------
% 0.21/0.55  % (32454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32462)Memory used [KB]: 6140
% 0.21/0.55  % (32462)Time elapsed: 0.003 s
% 0.21/0.55  % (32462)------------------------------
% 0.21/0.55  % (32462)------------------------------
% 0.21/0.55  % (32473)Refutation not found, incomplete strategy% (32473)------------------------------
% 0.21/0.55  % (32473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32473)Memory used [KB]: 10746
% 0.21/0.55  % (32473)Time elapsed: 0.137 s
% 0.21/0.55  % (32473)------------------------------
% 0.21/0.55  % (32473)------------------------------
% 0.21/0.55  % (32454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32454)Memory used [KB]: 6140
% 0.21/0.55  % (32454)Time elapsed: 0.140 s
% 0.21/0.55  % (32454)------------------------------
% 0.21/0.55  % (32454)------------------------------
% 0.21/0.55  
% 0.21/0.55  % (32470)Memory used [KB]: 1663
% 0.21/0.55  % (32470)Time elapsed: 0.115 s
% 0.21/0.55  % (32470)------------------------------
% 0.21/0.55  % (32470)------------------------------
% 0.21/0.55  % (32457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32466)Refutation not found, incomplete strategy% (32466)------------------------------
% 0.21/0.55  % (32466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32466)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32466)Memory used [KB]: 10746
% 0.21/0.55  % (32466)Time elapsed: 0.140 s
% 0.21/0.55  % (32466)------------------------------
% 0.21/0.55  % (32466)------------------------------
% 0.21/0.55  % (32453)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (32457)Refutation not found, incomplete strategy% (32457)------------------------------
% 0.21/0.55  % (32457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32457)Memory used [KB]: 10618
% 0.21/0.55  % (32457)Time elapsed: 0.151 s
% 0.21/0.55  % (32457)------------------------------
% 0.21/0.55  % (32457)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (32453)# SZS output start Saturation.
% 0.21/0.55  cnf(u20,axiom,
% 0.21/0.55      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u19,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u25,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.21/0.55  
% 0.21/0.55  cnf(u28,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u29,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))).
% 0.21/0.55  
% 0.21/0.55  cnf(u42,negated_conjecture,
% 0.21/0.55      sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u32,negated_conjecture,
% 0.21/0.55      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u44,axiom,
% 0.21/0.55      k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u40,axiom,
% 0.21/0.55      k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))).
% 0.21/0.55  
% 0.21/0.55  cnf(u39,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u34,negated_conjecture,
% 0.21/0.55      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k3_xboole_0(u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u37,axiom,
% 0.21/0.55      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u38,axiom,
% 0.21/0.55      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  % (32455)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  cnf(u45,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u17,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u21,axiom,
% 0.21/0.55      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u31,axiom,
% 0.21/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u30,negated_conjecture,
% 0.21/0.55      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  % (32453)# SZS output end Saturation.
% 0.21/0.55  % (32453)------------------------------
% 0.21/0.55  % (32453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32453)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (32453)Memory used [KB]: 6268
% 0.21/0.55  % (32453)Time elapsed: 0.114 s
% 0.21/0.55  % (32453)------------------------------
% 0.21/0.55  % (32453)------------------------------
% 0.21/0.55  % (32446)Success in time 0.184 s
%------------------------------------------------------------------------------
