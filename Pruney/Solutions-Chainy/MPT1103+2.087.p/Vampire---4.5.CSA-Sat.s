%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u102,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u101,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u100,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u99,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u98,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u97,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u96,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

tff(u95,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) )).

tff(u94,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u93,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u92,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u91,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

tff(u90,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u89,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u88,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) )).

tff(u87,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u86,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (14068)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (14083)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % (14068)Refutation not found, incomplete strategy% (14068)------------------------------
% 0.21/0.49  % (14068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (14068)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (14068)Memory used [KB]: 10618
% 0.21/0.49  % (14068)Time elapsed: 0.084 s
% 0.21/0.49  % (14068)------------------------------
% 0.21/0.49  % (14068)------------------------------
% 0.21/0.50  % (14083)Refutation not found, incomplete strategy% (14083)------------------------------
% 0.21/0.50  % (14083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14083)Memory used [KB]: 10618
% 0.21/0.50  % (14083)Time elapsed: 0.096 s
% 0.21/0.50  % (14083)------------------------------
% 0.21/0.50  % (14083)------------------------------
% 0.21/0.52  % (14074)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14069)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (14078)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (14070)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14070)Refutation not found, incomplete strategy% (14070)------------------------------
% 0.21/0.52  % (14070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14070)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14070)Memory used [KB]: 6140
% 0.21/0.52  % (14070)Time elapsed: 0.120 s
% 0.21/0.52  % (14070)------------------------------
% 0.21/0.52  % (14070)------------------------------
% 0.21/0.52  % (14067)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (14088)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (14073)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (14080)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (14071)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (14090)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (14066)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (14092)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (14066)Refutation not found, incomplete strategy% (14066)------------------------------
% 0.21/0.53  % (14066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14066)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14066)Memory used [KB]: 1663
% 0.21/0.53  % (14066)Time elapsed: 0.127 s
% 0.21/0.53  % (14066)------------------------------
% 0.21/0.53  % (14066)------------------------------
% 0.21/0.54  % (14081)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (14092)Refutation not found, incomplete strategy% (14092)------------------------------
% 0.21/0.54  % (14092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14092)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14092)Memory used [KB]: 10618
% 0.21/0.54  % (14092)Time elapsed: 0.139 s
% 0.21/0.54  % (14092)------------------------------
% 0.21/0.54  % (14092)------------------------------
% 0.21/0.54  % (14075)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (14078)Refutation not found, incomplete strategy% (14078)------------------------------
% 0.21/0.54  % (14078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14078)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14078)Memory used [KB]: 6268
% 0.21/0.54  % (14078)Time elapsed: 0.126 s
% 0.21/0.54  % (14078)------------------------------
% 0.21/0.54  % (14078)------------------------------
% 0.21/0.54  % (14074)Refutation not found, incomplete strategy% (14074)------------------------------
% 0.21/0.54  % (14074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14074)Memory used [KB]: 10618
% 0.21/0.54  % (14074)Time elapsed: 0.137 s
% 0.21/0.54  % (14074)------------------------------
% 0.21/0.54  % (14074)------------------------------
% 0.21/0.54  % (14093)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (14090)Refutation not found, incomplete strategy% (14090)------------------------------
% 0.21/0.54  % (14090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14069)Refutation not found, incomplete strategy% (14069)------------------------------
% 0.21/0.54  % (14069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14069)Memory used [KB]: 10746
% 0.21/0.54  % (14069)Time elapsed: 0.118 s
% 0.21/0.54  % (14069)------------------------------
% 0.21/0.54  % (14069)------------------------------
% 0.21/0.54  % (14090)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14090)Memory used [KB]: 6268
% 0.21/0.54  % (14090)Time elapsed: 0.130 s
% 0.21/0.54  % (14090)------------------------------
% 0.21/0.54  % (14090)------------------------------
% 0.21/0.54  % (14088)Refutation not found, incomplete strategy% (14088)------------------------------
% 0.21/0.54  % (14088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14081)Refutation not found, incomplete strategy% (14081)------------------------------
% 0.21/0.54  % (14081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14081)Memory used [KB]: 6140
% 0.21/0.54  % (14081)Time elapsed: 0.005 s
% 0.21/0.54  % (14081)------------------------------
% 0.21/0.54  % (14081)------------------------------
% 0.21/0.54  % (14093)Refutation not found, incomplete strategy% (14093)------------------------------
% 0.21/0.54  % (14093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14093)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14093)Memory used [KB]: 6268
% 0.21/0.54  % (14093)Time elapsed: 0.143 s
% 0.21/0.54  % (14093)------------------------------
% 0.21/0.54  % (14093)------------------------------
% 0.21/0.54  % (14075)Refutation not found, incomplete strategy% (14075)------------------------------
% 0.21/0.54  % (14075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14088)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14088)Memory used [KB]: 10618
% 0.21/0.54  % (14088)Time elapsed: 0.129 s
% 0.21/0.54  % (14088)------------------------------
% 0.21/0.54  % (14088)------------------------------
% 0.21/0.54  % (14089)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (14089)Refutation not found, incomplete strategy% (14089)------------------------------
% 0.21/0.54  % (14089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14089)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14089)Memory used [KB]: 1663
% 0.21/0.54  % (14089)Time elapsed: 0.140 s
% 0.21/0.54  % (14089)------------------------------
% 0.21/0.54  % (14089)------------------------------
% 0.21/0.54  % (14085)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (14082)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (14095)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (14075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14075)Memory used [KB]: 10618
% 0.21/0.55  % (14075)Time elapsed: 0.128 s
% 0.21/0.55  % (14075)------------------------------
% 0.21/0.55  % (14075)------------------------------
% 0.21/0.55  % (14085)Refutation not found, incomplete strategy% (14085)------------------------------
% 0.21/0.55  % (14085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14085)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14085)Memory used [KB]: 10746
% 0.21/0.55  % (14085)Time elapsed: 0.149 s
% 0.21/0.55  % (14085)------------------------------
% 0.21/0.55  % (14085)------------------------------
% 0.21/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.55  % (14082)# SZS output start Saturation.
% 0.21/0.55  tff(u102,negated_conjecture,
% 0.21/0.55      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u101,axiom,
% 0.21/0.55      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u100,axiom,
% 0.21/0.55      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u99,negated_conjecture,
% 0.21/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u98,negated_conjecture,
% 0.21/0.55      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u97,axiom,
% 0.21/0.55      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u96,axiom,
% 0.21/0.55      (![X1, X2] : ((k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.55  
% 0.21/0.55  tff(u95,negated_conjecture,
% 0.21/0.55      ((~(k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1))) | (k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)))).
% 0.21/0.55  
% 0.21/0.55  tff(u94,axiom,
% 0.21/0.55      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u93,axiom,
% 0.21/0.55      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.21/0.55  
% 0.21/0.55  tff(u92,negated_conjecture,
% 0.21/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u91,negated_conjecture,
% 0.21/0.55      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u90,axiom,
% 0.21/0.55      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u89,axiom,
% 0.21/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.55  
% 0.21/0.55  tff(u88,axiom,
% 0.21/0.55      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)))))).
% 0.21/0.55  
% 0.21/0.55  tff(u87,negated_conjecture,
% 0.21/0.55      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.55  
% 0.21/0.55  tff(u86,axiom,
% 0.21/0.55      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.55  
% 0.21/0.55  % (14082)# SZS output end Saturation.
% 0.21/0.55  % (14082)------------------------------
% 0.21/0.55  % (14082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14082)Termination reason: Satisfiable
% 0.21/0.55  
% 0.21/0.55  % (14082)Memory used [KB]: 10746
% 0.21/0.55  % (14082)Time elapsed: 0.152 s
% 0.21/0.55  % (14082)------------------------------
% 0.21/0.55  % (14082)------------------------------
% 0.21/0.55  % (14065)Success in time 0.184 s
%------------------------------------------------------------------------------
