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
% DateTime   : Thu Dec  3 13:08:57 EST 2020

% Result     : CounterSatisfiable 1.38s
% Output     : Saturation 1.38s
% Verified   : 
% Statistics : Number of clauses        :   46 (  46 expanded)
%              Number of leaves         :   46 (  46 expanded)
%              Depth                    :    0
%              Number of atoms          :   54 (  54 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u43,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u76,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2)) )).

cnf(u77,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1)) )).

cnf(u58,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u42,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) )).

cnf(u78,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3) )).

% (31341)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
cnf(u45,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u24,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u34,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u49,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 )).

cnf(u95,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u88,negated_conjecture,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) )).

cnf(u83,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u92,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u89,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) )).

cnf(u84,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u82,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

cnf(u100,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u23,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u109,axiom,
    ( k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))) = X2 )).

cnf(u47,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 )).

cnf(u39,axiom,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 )).

cnf(u112,axiom,
    ( k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),X0) )).

cnf(u70,axiom,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) )).

cnf(u66,axiom,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) )).

cnf(u64,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) )).

cnf(u60,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1) )).

cnf(u59,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) )).

cnf(u106,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u105,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u101,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u85,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

cnf(u27,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u103,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u102,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u104,axiom,
    ( k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u29,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u86,negated_conjecture,
    ( k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

cnf(u87,negated_conjecture,
    ( k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u71,axiom,
    ( k7_subset_1(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X3,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X3,X2)),X2) )).

cnf(u107,axiom,
    ( k5_xboole_0(X0,X0) = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0)) )).

cnf(u67,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) = k5_xboole_0(X2,X2) )).

cnf(u57,axiom,
    ( k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3))) )).

cnf(u25,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:14:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (31347)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.49  % (31330)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (31330)Refutation not found, incomplete strategy% (31330)------------------------------
% 0.21/0.50  % (31330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31330)Memory used [KB]: 10746
% 0.21/0.50  % (31330)Time elapsed: 0.085 s
% 0.21/0.50  % (31330)------------------------------
% 0.21/0.50  % (31330)------------------------------
% 0.21/0.50  % (31347)Refutation not found, incomplete strategy% (31347)------------------------------
% 0.21/0.50  % (31347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31347)Memory used [KB]: 10746
% 0.21/0.50  % (31347)Time elapsed: 0.087 s
% 0.21/0.50  % (31347)------------------------------
% 0.21/0.50  % (31347)------------------------------
% 0.21/0.51  % (31324)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31339)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (31343)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31325)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31325)Refutation not found, incomplete strategy% (31325)------------------------------
% 0.21/0.52  % (31325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31325)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31325)Memory used [KB]: 6268
% 0.21/0.52  % (31325)Time elapsed: 0.110 s
% 0.21/0.52  % (31325)------------------------------
% 0.21/0.52  % (31325)------------------------------
% 0.21/0.52  % (31321)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31321)Refutation not found, incomplete strategy% (31321)------------------------------
% 0.21/0.52  % (31321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31321)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31321)Memory used [KB]: 1791
% 0.21/0.52  % (31321)Time elapsed: 0.116 s
% 0.21/0.52  % (31321)------------------------------
% 0.21/0.52  % (31321)------------------------------
% 0.21/0.53  % (31323)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (31337)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (31333)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31323)Refutation not found, incomplete strategy% (31323)------------------------------
% 0.21/0.53  % (31323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31323)Memory used [KB]: 10746
% 0.21/0.53  % (31323)Time elapsed: 0.117 s
% 0.21/0.53  % (31323)------------------------------
% 0.21/0.53  % (31323)------------------------------
% 0.21/0.53  % (31350)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (31322)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31332)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (31344)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (31340)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (31345)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (31344)Refutation not found, incomplete strategy% (31344)------------------------------
% 0.21/0.53  % (31344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31344)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31344)Memory used [KB]: 1791
% 0.21/0.53  % (31344)Time elapsed: 0.127 s
% 0.21/0.53  % (31344)------------------------------
% 0.21/0.53  % (31344)------------------------------
% 0.21/0.54  % (31343)Refutation not found, incomplete strategy% (31343)------------------------------
% 0.21/0.54  % (31343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31343)Memory used [KB]: 10746
% 0.21/0.54  % (31343)Time elapsed: 0.097 s
% 0.21/0.54  % (31343)------------------------------
% 0.21/0.54  % (31343)------------------------------
% 0.21/0.54  % (31324)Refutation not found, incomplete strategy% (31324)------------------------------
% 0.21/0.54  % (31324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31324)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31324)Memory used [KB]: 10874
% 0.21/0.54  % (31324)Time elapsed: 0.109 s
% 0.21/0.54  % (31324)------------------------------
% 0.21/0.54  % (31324)------------------------------
% 0.21/0.54  % (31335)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (31326)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31342)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (31334)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.54  % (31326)Refutation not found, incomplete strategy% (31326)------------------------------
% 1.38/0.54  % (31326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (31348)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (31327)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.54  % (31331)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.55  % (31331)Refutation not found, incomplete strategy% (31331)------------------------------
% 1.38/0.55  % (31331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (31329)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.55  % (31338)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (31342)Refutation not found, incomplete strategy% (31342)------------------------------
% 1.38/0.55  % (31342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.38/0.55  % (31342)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (31342)Memory used [KB]: 1791
% 1.38/0.55  % (31342)Time elapsed: 0.138 s
% 1.38/0.55  % (31342)------------------------------
% 1.38/0.55  % (31342)------------------------------
% 1.38/0.55  % (31327)# SZS output start Saturation.
% 1.38/0.55  cnf(u43,axiom,
% 1.38/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.38/0.55  
% 1.38/0.55  cnf(u26,negated_conjecture,
% 1.38/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u22,negated_conjecture,
% 1.38/0.55      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u76,negated_conjecture,
% 1.38/0.55      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k3_tarski(k2_tarski(X0,sK2))).
% 1.38/0.55  
% 1.38/0.55  cnf(u77,negated_conjecture,
% 1.38/0.55      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k3_tarski(k2_tarski(X1,sK1))).
% 1.38/0.55  
% 1.38/0.55  cnf(u58,axiom,
% 1.38/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u42,axiom,
% 1.38/0.55      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))).
% 1.38/0.55  
% 1.38/0.55  cnf(u78,axiom,
% 1.38/0.55      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k3_tarski(k2_tarski(X2,X3)) = k4_subset_1(X3,X2,X3)).
% 1.38/0.55  
% 1.38/0.55  % (31341)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  cnf(u45,negated_conjecture,
% 1.38/0.55      r1_xboole_0(sK2,sK1)).
% 1.38/0.55  
% 1.38/0.55  cnf(u24,negated_conjecture,
% 1.38/0.55      r1_xboole_0(sK1,sK2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u34,axiom,
% 1.38/0.55      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u49,axiom,
% 1.38/0.55      ~r1_xboole_0(X0,X1) | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0).
% 1.38/0.55  
% 1.38/0.55  cnf(u95,negated_conjecture,
% 1.38/0.55      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.38/0.55  
% 1.38/0.55  cnf(u88,negated_conjecture,
% 1.38/0.55      sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u83,negated_conjecture,
% 1.38/0.55      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 1.38/0.55  
% 1.38/0.55  cnf(u92,negated_conjecture,
% 1.38/0.55      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u89,negated_conjecture,
% 1.38/0.55      sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u84,negated_conjecture,
% 1.38/0.55      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u82,negated_conjecture,
% 1.38/0.55      k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))).
% 1.38/0.55  
% 1.38/0.55  cnf(u100,negated_conjecture,
% 1.38/0.55      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 1.38/0.55  
% 1.38/0.55  cnf(u23,negated_conjecture,
% 1.38/0.55      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u109,axiom,
% 1.38/0.55      k1_setfam_1(k2_tarski(X2,k4_subset_1(X2,X2,X2))) = X2).
% 1.38/0.55  
% 1.38/0.55  cnf(u47,axiom,
% 1.38/0.55      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0).
% 1.38/0.55  
% 1.38/0.55  cnf(u39,axiom,
% 1.38/0.55      k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0).
% 1.38/0.55  
% 1.38/0.55  cnf(u112,axiom,
% 1.38/0.55      k7_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u70,axiom,
% 1.38/0.55      k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u66,axiom,
% 1.38/0.55      k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u64,axiom,
% 1.38/0.55      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u60,negated_conjecture,
% 1.38/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k7_subset_1(sK1,sK1,X1)).
% 1.38/0.55  
% 1.38/0.55  cnf(u59,negated_conjecture,
% 1.38/0.55      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u106,negated_conjecture,
% 1.38/0.55      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 1.38/0.55  
% 1.38/0.55  cnf(u105,negated_conjecture,
% 1.38/0.55      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u101,negated_conjecture,
% 1.38/0.55      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u85,negated_conjecture,
% 1.38/0.55      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u27,axiom,
% 1.38/0.55      k2_subset_1(X0) = X0).
% 1.38/0.55  
% 1.38/0.55  cnf(u103,negated_conjecture,
% 1.38/0.55      k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.38/0.55  
% 1.38/0.55  cnf(u102,negated_conjecture,
% 1.38/0.55      k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 1.38/0.55  
% 1.38/0.55  cnf(u104,axiom,
% 1.38/0.55      k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u29,axiom,
% 1.38/0.55      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 1.38/0.55  
% 1.38/0.55  cnf(u86,negated_conjecture,
% 1.38/0.55      k5_xboole_0(sK2,sK2) = k7_subset_1(sK2,sK2,k2_struct_0(sK0))).
% 1.38/0.55  
% 1.38/0.55  cnf(u87,negated_conjecture,
% 1.38/0.55      k5_xboole_0(sK1,sK1) = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 1.38/0.55  
% 1.38/0.55  cnf(u71,axiom,
% 1.38/0.55      k7_subset_1(k3_tarski(k2_tarski(X3,X2)),k3_tarski(k2_tarski(X3,X2)),X2) = k5_xboole_0(k3_tarski(k2_tarski(X3,X2)),X2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u107,axiom,
% 1.38/0.55      k5_xboole_0(X0,X0) = k7_subset_1(X0,X0,k4_subset_1(X0,X0,X0))).
% 1.38/0.55  
% 1.38/0.55  cnf(u67,axiom,
% 1.38/0.55      k7_subset_1(X2,X2,k3_tarski(k2_tarski(X3,X2))) = k5_xboole_0(X2,X2)).
% 1.38/0.55  
% 1.38/0.55  cnf(u57,axiom,
% 1.38/0.55      k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X3)))).
% 1.38/0.55  
% 1.38/0.55  cnf(u25,negated_conjecture,
% 1.38/0.55      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 1.38/0.55  
% 1.38/0.55  % (31327)# SZS output end Saturation.
% 1.38/0.55  % (31327)------------------------------
% 1.38/0.55  % (31327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (31327)Termination reason: Satisfiable
% 1.38/0.55  
% 1.38/0.55  % (31327)Memory used [KB]: 6268
% 1.38/0.55  % (31327)Time elapsed: 0.114 s
% 1.38/0.55  % (31327)------------------------------
% 1.38/0.55  % (31327)------------------------------
% 1.38/0.55  % (31338)Refutation not found, incomplete strategy% (31338)------------------------------
% 1.38/0.55  % (31338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (31320)Success in time 0.181 s
%------------------------------------------------------------------------------
