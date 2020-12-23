%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:46 EST 2020

% Result     : CounterSatisfiable 1.40s
% Output     : Saturation 1.40s
% Verified   : 
% Statistics : Number of clauses        :   38 (  38 expanded)
%              Number of leaves         :   38 (  38 expanded)
%              Depth                    :    0
%              Number of atoms          :   54 (  54 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u40,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) )).

cnf(u52,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u28,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u85,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u53,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u54,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u29,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u39,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u48,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u89,axiom,
    ( ~ r1_tarski(X4,X3)
    | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5) )).

cnf(u58,negated_conjecture,
    ( r2_xboole_0(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) )).

cnf(u56,axiom,
    ( r2_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = X0 )).

cnf(u140,axiom,
    ( ~ r2_xboole_0(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X2) )).

cnf(u104,axiom,
    ( ~ r2_xboole_0(X0,k1_xboole_0) )).

cnf(u101,axiom,
    ( ~ r2_xboole_0(X0,X0) )).

cnf(u99,negated_conjecture,
    ( ~ r2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u59,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u61,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u83,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u88,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u96,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u26,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u97,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

cnf(u114,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X1) )).

cnf(u123,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u95,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u87,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u73,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u46,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u31,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u30,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u94,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | sK1 = u1_struct_0(sK0) )).

cnf(u93,axiom,
    ( k1_xboole_0 != k7_subset_1(X0,X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u86,axiom,
    ( k1_xboole_0 != k7_subset_1(X1,X1,X0)
    | ~ r2_xboole_0(X0,X1) )).

cnf(u62,axiom,
    ( k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 )).

cnf(u63,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | sK1 = u1_struct_0(sK0) )).

cnf(u51,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (30804)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.48  % (30796)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (30788)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (30804)Refutation not found, incomplete strategy% (30804)------------------------------
% 0.21/0.50  % (30804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30780)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (30780)Refutation not found, incomplete strategy% (30780)------------------------------
% 0.21/0.50  % (30780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30780)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30780)Memory used [KB]: 1663
% 0.21/0.50  % (30780)Time elapsed: 0.093 s
% 0.21/0.50  % (30780)------------------------------
% 0.21/0.50  % (30780)------------------------------
% 0.21/0.51  % (30782)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (30804)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30804)Memory used [KB]: 6524
% 0.21/0.51  % (30804)Time elapsed: 0.098 s
% 0.21/0.51  % (30804)------------------------------
% 0.21/0.51  % (30804)------------------------------
% 1.26/0.51  % (30785)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.51  % (30787)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.51  % (30792)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.51  % (30787)Refutation not found, incomplete strategy% (30787)------------------------------
% 1.26/0.51  % (30787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.51  % (30787)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.51  
% 1.26/0.51  % (30787)Memory used [KB]: 6268
% 1.26/0.51  % (30787)Time elapsed: 0.109 s
% 1.26/0.51  % (30787)------------------------------
% 1.26/0.51  % (30787)------------------------------
% 1.26/0.52  % (30788)Refutation not found, incomplete strategy% (30788)------------------------------
% 1.26/0.52  % (30788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (30788)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.52  
% 1.26/0.52  % (30788)Memory used [KB]: 10746
% 1.26/0.52  % (30788)Time elapsed: 0.117 s
% 1.26/0.52  % (30788)------------------------------
% 1.26/0.52  % (30788)------------------------------
% 1.26/0.52  % (30808)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.26/0.52  % (30802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.26/0.53  % (30800)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.26/0.53  % (30786)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.53  % (30784)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.53  % (30809)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.53  % (30782)Refutation not found, incomplete strategy% (30782)------------------------------
% 1.40/0.53  % (30782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (30782)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (30782)Memory used [KB]: 10746
% 1.40/0.53  % (30782)Time elapsed: 0.127 s
% 1.40/0.53  % (30782)------------------------------
% 1.40/0.53  % (30782)------------------------------
% 1.40/0.53  % (30791)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.53  % (30794)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.40/0.53  % (30791)Refutation not found, incomplete strategy% (30791)------------------------------
% 1.40/0.53  % (30791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (30791)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (30791)Memory used [KB]: 10618
% 1.40/0.53  % (30791)Time elapsed: 0.124 s
% 1.40/0.53  % (30791)------------------------------
% 1.40/0.53  % (30791)------------------------------
% 1.40/0.53  % (30806)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.53  % (30781)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.40/0.53  % (30784)Refutation not found, incomplete strategy% (30784)------------------------------
% 1.40/0.53  % (30784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (30784)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (30784)Memory used [KB]: 6268
% 1.40/0.53  % (30784)Time elapsed: 0.131 s
% 1.40/0.53  % (30784)------------------------------
% 1.40/0.53  % (30784)------------------------------
% 1.40/0.53  % (30785)Refutation not found, incomplete strategy% (30785)------------------------------
% 1.40/0.53  % (30785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (30785)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (30785)Memory used [KB]: 6268
% 1.40/0.53  % (30785)Time elapsed: 0.109 s
% 1.40/0.53  % (30785)------------------------------
% 1.40/0.53  % (30785)------------------------------
% 1.40/0.54  % (30801)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.40/0.54  % (30792)Refutation not found, incomplete strategy% (30792)------------------------------
% 1.40/0.54  % (30792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (30792)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (30792)Memory used [KB]: 6268
% 1.40/0.54  % (30792)Time elapsed: 0.139 s
% 1.40/0.54  % (30792)------------------------------
% 1.40/0.54  % (30792)------------------------------
% 1.40/0.54  % (30801)Refutation not found, incomplete strategy% (30801)------------------------------
% 1.40/0.54  % (30801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (30801)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (30801)Memory used [KB]: 1791
% 1.40/0.54  % (30801)Time elapsed: 0.141 s
% 1.40/0.54  % (30801)------------------------------
% 1.40/0.54  % (30801)------------------------------
% 1.40/0.54  % (30798)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.54  % (30793)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.40/0.54  % (30802)Refutation not found, incomplete strategy% (30802)------------------------------
% 1.40/0.54  % (30802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (30802)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (30802)Memory used [KB]: 10746
% 1.40/0.54  % (30802)Time elapsed: 0.104 s
% 1.40/0.54  % (30802)------------------------------
% 1.40/0.54  % (30802)------------------------------
% 1.40/0.54  % (30803)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.54  % (30795)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.40/0.54  % (30797)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (30790)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (30803)Refutation not found, incomplete strategy% (30803)------------------------------
% 1.40/0.55  % (30803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (30803)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (30803)Memory used [KB]: 1663
% 1.40/0.55  % (30803)Time elapsed: 0.146 s
% 1.40/0.55  % (30803)------------------------------
% 1.40/0.55  % (30803)------------------------------
% 1.40/0.55  % (30795)Refutation not found, incomplete strategy% (30795)------------------------------
% 1.40/0.55  % (30795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (30795)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (30795)Memory used [KB]: 6140
% 1.40/0.55  % (30795)Time elapsed: 0.120 s
% 1.40/0.55  % (30795)------------------------------
% 1.40/0.55  % (30795)------------------------------
% 1.40/0.55  % (30797)Refutation not found, incomplete strategy% (30797)------------------------------
% 1.40/0.55  % (30797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (30797)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (30797)Memory used [KB]: 10618
% 1.40/0.55  % (30797)Time elapsed: 0.148 s
% 1.40/0.55  % (30797)------------------------------
% 1.40/0.55  % (30797)------------------------------
% 1.40/0.55  % (30800)Refutation not found, incomplete strategy% (30800)------------------------------
% 1.40/0.55  % (30800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (30800)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (30800)Memory used [KB]: 10746
% 1.40/0.55  % (30800)Time elapsed: 0.153 s
% 1.40/0.55  % (30800)------------------------------
% 1.40/0.55  % (30800)------------------------------
% 1.40/0.55  % (30790)Refutation not found, incomplete strategy% (30790)------------------------------
% 1.40/0.55  % (30790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (30790)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (30790)Memory used [KB]: 10618
% 1.40/0.55  % (30790)Time elapsed: 0.149 s
% 1.40/0.55  % (30790)------------------------------
% 1.40/0.55  % (30790)------------------------------
% 1.40/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.40/0.55  % (30786)# SZS output start Saturation.
% 1.40/0.55  cnf(u40,axiom,
% 1.40/0.55      m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u52,axiom,
% 1.40/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.40/0.55  
% 1.40/0.55  cnf(u28,negated_conjecture,
% 1.40/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.40/0.55  
% 1.40/0.55  cnf(u41,axiom,
% 1.40/0.55      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u85,axiom,
% 1.40/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.40/0.55  
% 1.40/0.55  cnf(u53,negated_conjecture,
% 1.40/0.55      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.40/0.55  
% 1.40/0.55  cnf(u54,axiom,
% 1.40/0.55      r1_tarski(X0,X0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u29,axiom,
% 1.40/0.55      r1_tarski(k1_xboole_0,X0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u39,axiom,
% 1.40/0.55      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u48,axiom,
% 1.40/0.55      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u89,axiom,
% 1.40/0.55      ~r1_tarski(X4,X3) | k7_subset_1(X3,X4,X5) = k7_subset_1(X4,X4,X5)).
% 1.40/0.55  
% 1.40/0.55  cnf(u58,negated_conjecture,
% 1.40/0.55      r2_xboole_0(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u56,axiom,
% 1.40/0.55      r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u140,axiom,
% 1.40/0.55      ~r2_xboole_0(k5_xboole_0(X2,k7_subset_1(X3,X3,X2)),X2)).
% 1.40/0.55  
% 1.40/0.55  cnf(u104,axiom,
% 1.40/0.55      ~r2_xboole_0(X0,k1_xboole_0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u101,axiom,
% 1.40/0.55      ~r2_xboole_0(X0,X0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u99,negated_conjecture,
% 1.40/0.55      ~r2_xboole_0(u1_struct_0(sK0),sK1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u59,axiom,
% 1.40/0.55      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 1.40/0.55  
% 1.40/0.55  cnf(u61,negated_conjecture,
% 1.40/0.55      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 1.40/0.55  
% 1.40/0.55  cnf(u83,axiom,
% 1.40/0.55      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.40/0.55  
% 1.40/0.55  cnf(u88,negated_conjecture,
% 1.40/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u96,negated_conjecture,
% 1.40/0.55      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 1.40/0.55  
% 1.40/0.55  cnf(u26,negated_conjecture,
% 1.40/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u97,axiom,
% 1.40/0.55      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u114,axiom,
% 1.40/0.55      k1_xboole_0 = k7_subset_1(X0,k1_xboole_0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u123,axiom,
% 1.40/0.55      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 1.40/0.55  
% 1.40/0.55  cnf(u95,axiom,
% 1.40/0.55      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u87,axiom,
% 1.40/0.55      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 1.40/0.55  
% 1.40/0.55  cnf(u73,axiom,
% 1.40/0.55      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u46,axiom,
% 1.40/0.55      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u31,axiom,
% 1.40/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u30,axiom,
% 1.40/0.55      k2_subset_1(X0) = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u94,negated_conjecture,
% 1.40/0.55      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) | sK1 = u1_struct_0(sK0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u93,axiom,
% 1.40/0.55      k1_xboole_0 != k7_subset_1(X0,X0,k1_xboole_0) | k1_xboole_0 = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u86,axiom,
% 1.40/0.55      k1_xboole_0 != k7_subset_1(X1,X1,X0) | ~r2_xboole_0(X0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u62,axiom,
% 1.40/0.55      k1_xboole_0 != k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) | k1_xboole_0 = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u63,negated_conjecture,
% 1.40/0.55      k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) | sK1 = u1_struct_0(sK0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u51,negated_conjecture,
% 1.40/0.55      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.40/0.55  
% 1.40/0.55  % (30786)# SZS output end Saturation.
% 1.40/0.55  % (30786)------------------------------
% 1.40/0.55  % (30786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (30786)Termination reason: Satisfiable
% 1.40/0.55  
% 1.40/0.55  % (30786)Memory used [KB]: 6268
% 1.40/0.55  % (30786)Time elapsed: 0.104 s
% 1.40/0.55  % (30786)------------------------------
% 1.40/0.55  % (30786)------------------------------
% 1.40/0.55  % (30779)Success in time 0.187 s
%------------------------------------------------------------------------------
