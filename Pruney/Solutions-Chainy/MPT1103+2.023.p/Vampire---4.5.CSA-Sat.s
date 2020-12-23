%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:37 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u49,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u38,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u69,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u51,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u52,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u46,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 )).

cnf(u55,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) )).

cnf(u68,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u72,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u101,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) )).

cnf(u82,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u76,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u77,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u24,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u105,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) )).

cnf(u106,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),X1)) )).

cnf(u127,axiom,
    ( k5_xboole_0(X2,k7_subset_1(X1,X1,X2)) = k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k7_subset_1(X1,X1,X2)),k5_xboole_0(X2,k7_subset_1(X1,X1,X2)),X1)) )).

cnf(u73,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) )).

cnf(u102,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k5_xboole_0(X3,k7_subset_1(X2,X2,X3))))) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u60,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u42,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u28,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u27,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u48,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (7054)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (7073)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (7058)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (7061)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (7054)Refutation not found, incomplete strategy% (7054)------------------------------
% 0.21/0.52  % (7054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7054)Memory used [KB]: 1663
% 0.21/0.52  % (7054)Time elapsed: 0.110 s
% 0.21/0.52  % (7054)------------------------------
% 0.21/0.52  % (7054)------------------------------
% 0.21/0.52  % (7081)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (7065)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (7077)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (7076)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (7065)Refutation not found, incomplete strategy% (7065)------------------------------
% 0.21/0.52  % (7065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7065)Memory used [KB]: 10618
% 0.21/0.52  % (7065)Time elapsed: 0.113 s
% 0.21/0.52  % (7065)------------------------------
% 0.21/0.52  % (7065)------------------------------
% 0.21/0.52  % (7077)Refutation not found, incomplete strategy% (7077)------------------------------
% 0.21/0.52  % (7077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7077)Memory used [KB]: 1663
% 0.21/0.52  % (7077)Time elapsed: 0.113 s
% 0.21/0.52  % (7077)------------------------------
% 0.21/0.52  % (7077)------------------------------
% 0.21/0.52  % (7076)Refutation not found, incomplete strategy% (7076)------------------------------
% 0.21/0.52  % (7076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7061)Refutation not found, incomplete strategy% (7061)------------------------------
% 0.21/0.52  % (7061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7061)Memory used [KB]: 6268
% 0.21/0.52  % (7061)Time elapsed: 0.118 s
% 0.21/0.52  % (7061)------------------------------
% 0.21/0.52  % (7061)------------------------------
% 0.21/0.52  % (7073)Refutation not found, incomplete strategy% (7073)------------------------------
% 0.21/0.52  % (7073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7073)Memory used [KB]: 10874
% 0.21/0.53  % (7073)Time elapsed: 0.110 s
% 0.21/0.53  % (7073)------------------------------
% 0.21/0.53  % (7073)------------------------------
% 0.21/0.53  % (7068)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (7082)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (7060)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (7056)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (7083)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (7057)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (7063)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (7059)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (7062)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (7058)Refutation not found, incomplete strategy% (7058)------------------------------
% 0.21/0.54  % (7058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7058)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7058)Memory used [KB]: 6396
% 0.21/0.54  % (7058)Time elapsed: 0.122 s
% 0.21/0.54  % (7058)------------------------------
% 0.21/0.54  % (7058)------------------------------
% 0.21/0.54  % (7063)Refutation not found, incomplete strategy% (7063)------------------------------
% 0.21/0.54  % (7063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7063)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7063)Memory used [KB]: 10618
% 0.21/0.54  % (7063)Time elapsed: 0.134 s
% 0.21/0.54  % (7063)------------------------------
% 0.21/0.54  % (7063)------------------------------
% 0.21/0.54  % (7064)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (7074)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (7064)Refutation not found, incomplete strategy% (7064)------------------------------
% 0.21/0.54  % (7064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7064)Memory used [KB]: 10618
% 0.21/0.54  % (7064)Time elapsed: 0.131 s
% 0.21/0.54  % (7064)------------------------------
% 0.21/0.54  % (7064)------------------------------
% 0.21/0.54  % (7059)Refutation not found, incomplete strategy% (7059)------------------------------
% 0.21/0.54  % (7059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7059)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7059)Memory used [KB]: 6268
% 0.21/0.54  % (7059)Time elapsed: 0.134 s
% 0.21/0.54  % (7059)------------------------------
% 0.21/0.54  % (7059)------------------------------
% 0.21/0.54  % (7062)Refutation not found, incomplete strategy% (7062)------------------------------
% 0.21/0.54  % (7062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7062)Memory used [KB]: 10746
% 0.21/0.54  % (7062)Time elapsed: 0.133 s
% 0.21/0.54  % (7062)------------------------------
% 0.21/0.54  % (7062)------------------------------
% 0.21/0.54  % (7074)Refutation not found, incomplete strategy% (7074)------------------------------
% 0.21/0.54  % (7074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7074)Memory used [KB]: 10746
% 0.21/0.54  % (7074)Time elapsed: 0.142 s
% 0.21/0.54  % (7074)------------------------------
% 0.21/0.54  % (7074)------------------------------
% 0.21/0.54  % (7076)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7076)Memory used [KB]: 10746
% 0.21/0.54  % (7076)Time elapsed: 0.086 s
% 0.21/0.54  % (7076)------------------------------
% 0.21/0.54  % (7076)------------------------------
% 0.21/0.54  % (7066)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (7079)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (7075)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (7080)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (7078)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (7066)Refutation not found, incomplete strategy% (7066)------------------------------
% 0.21/0.55  % (7066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7066)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7066)Memory used [KB]: 6396
% 0.21/0.55  % (7066)Time elapsed: 0.156 s
% 0.21/0.55  % (7066)------------------------------
% 0.21/0.55  % (7066)------------------------------
% 0.21/0.55  % (7071)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (7071)Refutation not found, incomplete strategy% (7071)------------------------------
% 0.21/0.55  % (7071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7071)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7071)Memory used [KB]: 10618
% 0.21/0.55  % (7071)Time elapsed: 0.147 s
% 0.21/0.55  % (7071)------------------------------
% 0.21/0.55  % (7071)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (7060)# SZS output start Saturation.
% 0.21/0.55  cnf(u49,axiom,
% 0.21/0.55      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u26,negated_conjecture,
% 0.21/0.55      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u38,axiom,
% 0.21/0.55      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 0.21/0.55  
% 0.21/0.55  cnf(u69,axiom,
% 0.21/0.55      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u51,negated_conjecture,
% 0.21/0.55      r1_tarski(sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u52,axiom,
% 0.21/0.55      r1_tarski(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u46,axiom,
% 0.21/0.55      ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u55,negated_conjecture,
% 0.21/0.55      sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u68,axiom,
% 0.21/0.55      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.55  
% 0.21/0.55  cnf(u72,negated_conjecture,
% 0.21/0.55      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u101,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u82,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 0.21/0.55  
% 0.21/0.55  cnf(u76,axiom,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u77,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 0.21/0.55  
% 0.21/0.55  cnf(u24,negated_conjecture,
% 0.21/0.55      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u105,negated_conjecture,
% 0.21/0.55      u1_struct_0(sK0) = k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u106,axiom,
% 0.21/0.55      k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u127,axiom,
% 0.21/0.55      k5_xboole_0(X2,k7_subset_1(X1,X1,X2)) = k5_xboole_0(X1,k7_subset_1(k5_xboole_0(X2,k7_subset_1(X1,X1,X2)),k5_xboole_0(X2,k7_subset_1(X1,X1,X2)),X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u73,axiom,
% 0.21/0.55      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1))).
% 0.21/0.55  
% 0.21/0.55  cnf(u102,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k5_xboole_0(X3,k7_subset_1(X2,X2,X3)))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u70,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 0.21/0.55  
% 0.21/0.55  cnf(u60,axiom,
% 0.21/0.55      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.55  
% 0.21/0.55  cnf(u42,axiom,
% 0.21/0.55      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u28,axiom,
% 0.21/0.55      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u27,axiom,
% 0.21/0.55      k2_subset_1(X0) = X0).
% 0.21/0.55  
% 0.21/0.55  cnf(u48,negated_conjecture,
% 0.21/0.55      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.55  
% 0.21/0.55  % (7060)# SZS output end Saturation.
% 0.21/0.55  % (7060)------------------------------
% 0.21/0.55  % (7060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7060)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (7060)Memory used [KB]: 6268
% 0.21/0.55  % (7060)Time elapsed: 0.106 s
% 0.21/0.55  % (7060)------------------------------
% 0.21/0.55  % (7060)------------------------------
% 0.21/0.55  % (7072)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (7067)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (7053)Success in time 0.191 s
%------------------------------------------------------------------------------
