%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 1.63s
% Output     : Saturation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   29 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u209,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u208,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u207,axiom,(
    ! [X3,X4] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) )).

tff(u206,axiom,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )).

tff(u205,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

tff(u204,axiom,(
    ! [X3] : k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,k1_xboole_0) )).

tff(u203,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u202,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u201,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u200,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) )).

tff(u199,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u198,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u197,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u196,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))) )).

tff(u195,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))) )).

tff(u194,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u193,axiom,(
    ! [X1,X0] : k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

tff(u192,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u191,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(sK1,sK1,X2) )).

tff(u190,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u189,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u188,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) )).

tff(u187,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u186,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

tff(u185,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u184,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (15872)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (15894)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (15871)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (15872)Refutation not found, incomplete strategy% (15872)------------------------------
% 0.21/0.51  % (15872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15871)Refutation not found, incomplete strategy% (15871)------------------------------
% 0.21/0.51  % (15871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15894)Refutation not found, incomplete strategy% (15894)------------------------------
% 0.21/0.52  % (15894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15872)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15872)Memory used [KB]: 10618
% 0.21/0.52  % (15872)Time elapsed: 0.092 s
% 0.21/0.52  % (15872)------------------------------
% 0.21/0.52  % (15872)------------------------------
% 0.21/0.52  % (15871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15871)Memory used [KB]: 6268
% 0.21/0.52  % (15871)Time elapsed: 0.098 s
% 0.21/0.52  % (15871)------------------------------
% 0.21/0.52  % (15871)------------------------------
% 0.21/0.52  % (15894)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15894)Memory used [KB]: 1791
% 0.21/0.52  % (15894)Time elapsed: 0.098 s
% 0.21/0.52  % (15894)------------------------------
% 0.21/0.52  % (15894)------------------------------
% 0.21/0.54  % (15865)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (15877)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (15886)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (15873)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (15866)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15873)Refutation not found, incomplete strategy% (15873)------------------------------
% 0.21/0.54  % (15873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15873)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15873)Memory used [KB]: 10618
% 0.21/0.54  % (15873)Time elapsed: 0.121 s
% 0.21/0.54  % (15873)------------------------------
% 0.21/0.54  % (15873)------------------------------
% 0.21/0.54  % (15866)Refutation not found, incomplete strategy% (15866)------------------------------
% 0.21/0.54  % (15866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15866)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15866)Memory used [KB]: 10618
% 0.21/0.54  % (15866)Time elapsed: 0.123 s
% 0.21/0.54  % (15866)------------------------------
% 0.21/0.54  % (15866)------------------------------
% 0.21/0.54  % (15867)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15886)Refutation not found, incomplete strategy% (15886)------------------------------
% 0.21/0.54  % (15886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15869)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15886)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15886)Memory used [KB]: 10618
% 0.21/0.54  % (15886)Time elapsed: 0.050 s
% 0.21/0.54  % (15886)------------------------------
% 0.21/0.54  % (15886)------------------------------
% 0.21/0.54  % (15868)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (15878)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (15874)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (15885)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (15868)Refutation not found, incomplete strategy% (15868)------------------------------
% 0.21/0.55  % (15868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15874)Refutation not found, incomplete strategy% (15874)------------------------------
% 0.21/0.55  % (15874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15874)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15874)Memory used [KB]: 10618
% 0.21/0.55  % (15874)Time elapsed: 0.133 s
% 0.21/0.55  % (15874)------------------------------
% 0.21/0.55  % (15874)------------------------------
% 0.21/0.55  % (15885)Refutation not found, incomplete strategy% (15885)------------------------------
% 0.21/0.55  % (15885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15885)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15885)Memory used [KB]: 1791
% 0.21/0.55  % (15885)Time elapsed: 0.138 s
% 0.21/0.55  % (15885)------------------------------
% 0.21/0.55  % (15885)------------------------------
% 0.21/0.55  % (15868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15868)Memory used [KB]: 6140
% 0.21/0.55  % (15868)Time elapsed: 0.134 s
% 0.21/0.55  % (15868)------------------------------
% 0.21/0.55  % (15868)------------------------------
% 0.21/0.55  % (15890)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (15864)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (15893)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (15869)Refutation not found, incomplete strategy% (15869)------------------------------
% 0.21/0.55  % (15869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15869)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15869)Memory used [KB]: 6268
% 0.21/0.55  % (15869)Time elapsed: 0.126 s
% 0.21/0.55  % (15869)------------------------------
% 0.21/0.55  % (15869)------------------------------
% 0.21/0.55  % (15864)Refutation not found, incomplete strategy% (15864)------------------------------
% 0.21/0.55  % (15864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15879)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (15882)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (15879)Refutation not found, incomplete strategy% (15879)------------------------------
% 0.21/0.56  % (15879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15879)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15879)Memory used [KB]: 6140
% 0.21/0.56  % (15879)Time elapsed: 0.001 s
% 0.21/0.56  % (15879)------------------------------
% 0.21/0.56  % (15879)------------------------------
% 0.21/0.56  % (15888)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (15864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15864)Memory used [KB]: 1663
% 0.21/0.56  % (15864)Time elapsed: 0.128 s
% 0.21/0.56  % (15864)------------------------------
% 0.21/0.56  % (15864)------------------------------
% 0.21/0.56  % (15881)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (15883)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (15891)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (15881)Refutation not found, incomplete strategy% (15881)------------------------------
% 0.21/0.56  % (15881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15881)Memory used [KB]: 10618
% 0.21/0.56  % (15881)Time elapsed: 0.148 s
% 0.21/0.56  % (15881)------------------------------
% 0.21/0.56  % (15881)------------------------------
% 0.21/0.56  % (15876)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (15890)Refutation not found, incomplete strategy% (15890)------------------------------
% 0.21/0.56  % (15890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15890)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15890)Memory used [KB]: 6268
% 0.21/0.56  % (15890)Time elapsed: 0.147 s
% 0.21/0.56  % (15890)------------------------------
% 0.21/0.56  % (15890)------------------------------
% 0.21/0.56  % (15876)Refutation not found, incomplete strategy% (15876)------------------------------
% 0.21/0.56  % (15876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (15867)Refutation not found, incomplete strategy% (15867)------------------------------
% 1.63/0.57  % (15867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (15867)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (15867)Memory used [KB]: 10746
% 1.63/0.57  % (15867)Time elapsed: 0.126 s
% 1.63/0.57  % (15867)------------------------------
% 1.63/0.57  % (15867)------------------------------
% 1.63/0.57  % (15888)Refutation not found, incomplete strategy% (15888)------------------------------
% 1.63/0.57  % (15888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (15892)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.63/0.57  % (15887)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.63/0.57  % (15891)Refutation not found, incomplete strategy% (15891)------------------------------
% 1.63/0.57  % (15891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (15891)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (15891)Memory used [KB]: 10746
% 1.63/0.57  % (15891)Time elapsed: 0.158 s
% 1.63/0.57  % (15891)------------------------------
% 1.63/0.57  % (15891)------------------------------
% 1.63/0.57  % (15887)Refutation not found, incomplete strategy% (15887)------------------------------
% 1.63/0.57  % (15887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (15887)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (15887)Memory used [KB]: 1791
% 1.63/0.57  % (15887)Time elapsed: 0.156 s
% 1.63/0.57  % (15887)------------------------------
% 1.63/0.57  % (15887)------------------------------
% 1.63/0.57  % (15880)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.63/0.57  % (15883)Refutation not found, incomplete strategy% (15883)------------------------------
% 1.63/0.57  % (15883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (15883)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (15883)Memory used [KB]: 10746
% 1.63/0.57  % (15883)Time elapsed: 0.160 s
% 1.63/0.57  % (15883)------------------------------
% 1.63/0.57  % (15883)------------------------------
% 1.63/0.57  % (15876)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (15876)Memory used [KB]: 6268
% 1.63/0.57  % (15876)Time elapsed: 0.150 s
% 1.63/0.57  % (15876)------------------------------
% 1.63/0.57  % (15876)------------------------------
% 1.63/0.57  % (15884)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.63/0.58  % (15875)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.63/0.58  % (15870)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.63/0.58  % (15875)Refutation not found, incomplete strategy% (15875)------------------------------
% 1.63/0.58  % (15875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.63/0.58  % (15880)# SZS output start Saturation.
% 1.63/0.58  tff(u209,negated_conjecture,
% 1.63/0.58      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u208,axiom,
% 1.63/0.58      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u207,axiom,
% 1.63/0.58      (![X3, X4] : ((k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))))))).
% 1.63/0.58  
% 1.63/0.58  tff(u206,axiom,
% 1.63/0.58      (![X1] : ((k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))))).
% 1.63/0.58  
% 1.63/0.58  tff(u205,axiom,
% 1.63/0.58      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u204,axiom,
% 1.63/0.58      (![X3] : ((k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,k1_xboole_0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u203,axiom,
% 1.63/0.58      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 1.63/0.58  
% 1.63/0.58  tff(u202,negated_conjecture,
% 1.63/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.63/0.58  
% 1.63/0.58  tff(u201,negated_conjecture,
% 1.63/0.58      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.63/0.58  
% 1.63/0.58  tff(u200,axiom,
% 1.63/0.58      (![X0] : ((k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u199,axiom,
% 1.63/0.58      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u198,axiom,
% 1.63/0.58      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u197,negated_conjecture,
% 1.63/0.58      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))).
% 1.63/0.58  
% 1.63/0.58  tff(u196,negated_conjecture,
% 1.63/0.58      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1))))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),sK1)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u195,axiom,
% 1.63/0.58      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))))))).
% 1.63/0.58  
% 1.63/0.58  tff(u194,axiom,
% 1.63/0.58      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 1.63/0.58  
% 1.63/0.58  tff(u193,axiom,
% 1.63/0.58      (![X1, X0] : ((k7_subset_1(X0,k1_xboole_0,X1) = k7_subset_1(k1_xboole_0,k1_xboole_0,X1))))).
% 1.63/0.58  
% 1.63/0.58  tff(u192,axiom,
% 1.63/0.58      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u191,negated_conjecture,
% 1.63/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X2] : ((k7_subset_1(u1_struct_0(sK0),sK1,X2) = k7_subset_1(sK1,sK1,X2)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u190,negated_conjecture,
% 1.63/0.58      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 1.63/0.58  
% 1.63/0.58  tff(u189,axiom,
% 1.63/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u188,axiom,
% 1.63/0.58      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)))))).
% 1.63/0.58  
% 1.63/0.58  tff(u187,axiom,
% 1.63/0.58      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 1.63/0.58  
% 1.63/0.58  tff(u186,axiom,
% 1.63/0.58      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u185,negated_conjecture,
% 1.63/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.63/0.58  
% 1.63/0.58  tff(u184,axiom,
% 1.63/0.58      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.63/0.58  
% 1.63/0.58  % (15880)# SZS output end Saturation.
% 1.63/0.58  % (15880)------------------------------
% 1.63/0.58  % (15880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (15880)Termination reason: Satisfiable
% 1.63/0.58  
% 1.63/0.58  % (15880)Memory used [KB]: 10746
% 1.63/0.58  % (15880)Time elapsed: 0.163 s
% 1.63/0.58  % (15880)------------------------------
% 1.63/0.58  % (15880)------------------------------
% 1.63/0.58  % (15884)Refutation not found, incomplete strategy% (15884)------------------------------
% 1.63/0.58  % (15884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (15863)Success in time 0.21 s
%------------------------------------------------------------------------------
