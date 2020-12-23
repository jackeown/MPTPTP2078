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
% DateTime   : Thu Dec  3 13:09:00 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   38 (  38 expanded)
%              Depth                    :    0
%              Number of atoms          :   68 (  68 expanded)
%              Number of equality atoms :   48 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u214,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u213,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u212,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 )).

tff(u211,axiom,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

tff(u210,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) )).

tff(u209,axiom,(
    ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k3_tarski(k2_tarski(X2,X1))) )).

tff(u208,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u207,axiom,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) )).

tff(u206,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) )).

tff(u205,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) )).

tff(u204,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | ! [X0] : k3_tarski(k2_tarski(sK2,k4_xboole_0(X0,sK1))) = k4_xboole_0(k3_tarski(k2_tarski(sK2,X0)),sK1) )).

tff(u203,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u202,negated_conjecture,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | sK2 = k4_xboole_0(sK2,sK1) )).

tff(u201,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u200,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | ! [X0] : k4_xboole_0(k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k4_xboole_0(X0,sK1))) )).

tff(u199,axiom,(
    ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) )).

tff(u198,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k3_tarski(k2_tarski(sK1,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) )).

tff(u197,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u196,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k3_tarski(k2_tarski(sK2,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) )).

tff(u195,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

tff(u194,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

tff(u193,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u192,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u191,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0) )).

tff(u190,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u189,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u188,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3) )).

tff(u187,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

tff(u186,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_tarski(k2_tarski(k4_xboole_0(X2,X0),X1)) = k4_xboole_0(k3_tarski(k2_tarski(X2,X1)),X0) ) )).

tff(u185,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u184,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X3,X2) = k3_tarski(k2_tarski(X3,X2)) ) )).

tff(u183,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) )).

tff(u182,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u181,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)) ) )).

tff(u180,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) )).

tff(u179,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u178,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u177,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (12940)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (12948)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (12932)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (12932)Refutation not found, incomplete strategy% (12932)------------------------------
% 0.20/0.52  % (12932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12932)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12932)Memory used [KB]: 6268
% 0.20/0.52  % (12932)Time elapsed: 0.068 s
% 0.20/0.52  % (12932)------------------------------
% 0.20/0.52  % (12932)------------------------------
% 0.20/0.52  % (12938)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (12940)Refutation not found, incomplete strategy% (12940)------------------------------
% 0.20/0.52  % (12940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12940)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (12940)Memory used [KB]: 6140
% 0.20/0.52  % (12940)Time elapsed: 0.003 s
% 0.20/0.52  % (12940)------------------------------
% 0.20/0.52  % (12940)------------------------------
% 0.20/0.53  % (12926)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (12946)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (12928)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (12951)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (12930)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (12925)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (12930)Refutation not found, incomplete strategy% (12930)------------------------------
% 0.20/0.54  % (12930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12930)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12930)Memory used [KB]: 6268
% 0.20/0.54  % (12930)Time elapsed: 0.140 s
% 0.20/0.54  % (12930)------------------------------
% 0.20/0.54  % (12930)------------------------------
% 0.20/0.54  % (12927)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (12937)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (12929)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (12931)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (12944)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (12954)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (12941)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (12944)Refutation not found, incomplete strategy% (12944)------------------------------
% 0.20/0.55  % (12944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (12944)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (12944)Memory used [KB]: 10746
% 0.20/0.55  % (12944)Time elapsed: 0.140 s
% 0.20/0.55  % (12944)------------------------------
% 0.20/0.55  % (12944)------------------------------
% 0.20/0.55  % (12943)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (12952)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (12945)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (12933)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (12935)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (12953)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (12936)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (12949)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (12939)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  % (12950)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (12947)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (12942)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (12942)Refutation not found, incomplete strategy% (12942)------------------------------
% 0.20/0.57  % (12942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12942)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (12942)Memory used [KB]: 10618
% 0.20/0.57  % (12942)Time elapsed: 0.167 s
% 0.20/0.57  % (12942)------------------------------
% 0.20/0.57  % (12942)------------------------------
% 0.20/0.57  % (12934)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.57  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.57  % (12941)# SZS output start Saturation.
% 0.20/0.57  tff(u214,negated_conjecture,
% 0.20/0.57      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.57  
% 0.20/0.57  tff(u213,axiom,
% 0.20/0.57      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.57  
% 0.20/0.57  tff(u212,axiom,
% 0.20/0.57      (![X0] : ((k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0)))).
% 0.20/0.57  
% 0.20/0.57  tff(u211,axiom,
% 0.20/0.57      (![X0] : ((k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0)))).
% 0.20/0.57  
% 0.20/0.57  tff(u210,axiom,
% 0.20/0.57      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u209,axiom,
% 0.20/0.57      (![X1, X2] : ((k1_xboole_0 = k4_xboole_0(X1,k3_tarski(k2_tarski(X2,X1))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u208,axiom,
% 0.20/0.57      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u207,axiom,
% 0.20/0.57      (![X2] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2))))).
% 0.20/0.57  
% 0.20/0.57  tff(u206,negated_conjecture,
% 0.20/0.57      ((~(k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u205,negated_conjecture,
% 0.20/0.57      ((~(k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u204,negated_conjecture,
% 0.20/0.57      ((~r1_xboole_0(sK1,sK2)) | (![X0] : ((k3_tarski(k2_tarski(sK2,k4_xboole_0(X0,sK1))) = k4_xboole_0(k3_tarski(k2_tarski(sK2,X0)),sK1)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u203,negated_conjecture,
% 0.20/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u202,negated_conjecture,
% 0.20/0.57      ((~(sK2 = k4_xboole_0(sK2,sK1))) | (sK2 = k4_xboole_0(sK2,sK1)))).
% 0.20/0.57  
% 0.20/0.57  tff(u201,negated_conjecture,
% 0.20/0.57      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 0.20/0.57  
% 0.20/0.57  tff(u200,negated_conjecture,
% 0.20/0.57      ((~r1_xboole_0(sK1,sK2)) | (![X0] : ((k4_xboole_0(k3_tarski(k2_tarski(X0,sK2)),sK1) = k3_tarski(k2_tarski(sK2,k4_xboole_0(X0,sK1)))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u199,axiom,
% 0.20/0.57      (![X1, X0] : ((k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u198,negated_conjecture,
% 0.20/0.57      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))))).
% 0.20/0.57  
% 0.20/0.57  tff(u197,negated_conjecture,
% 0.20/0.57      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u196,negated_conjecture,
% 0.20/0.57      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2))))).
% 0.20/0.57  
% 0.20/0.57  tff(u195,negated_conjecture,
% 0.20/0.57      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u194,negated_conjecture,
% 0.20/0.57      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))))).
% 0.20/0.57  
% 0.20/0.57  tff(u193,negated_conjecture,
% 0.20/0.57      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 0.20/0.57  
% 0.20/0.57  tff(u192,negated_conjecture,
% 0.20/0.57      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 0.20/0.57  
% 0.20/0.57  tff(u191,axiom,
% 0.20/0.57      (![X0] : ((k3_tarski(k2_tarski(X0,X0)) = k4_subset_1(X0,X0,X0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u190,negated_conjecture,
% 0.20/0.57      ((~(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u189,negated_conjecture,
% 0.20/0.57      ((~(k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u188,axiom,
% 0.20/0.57      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3))))).
% 0.20/0.57  
% 0.20/0.57  tff(u187,negated_conjecture,
% 0.20/0.57      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u186,axiom,
% 0.20/0.57      (![X1, X0, X2] : ((~r1_xboole_0(X0,X1) | (k3_tarski(k2_tarski(k4_xboole_0(X2,X0),X1)) = k4_xboole_0(k3_tarski(k2_tarski(X2,X1)),X0)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u185,negated_conjecture,
% 0.20/0.57      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 0.20/0.57  
% 0.20/0.57  tff(u184,axiom,
% 0.20/0.57      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k4_subset_1(X3,X3,X2) = k3_tarski(k2_tarski(X3,X2))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u183,axiom,
% 0.20/0.57      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u182,axiom,
% 0.20/0.57      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.20/0.57  
% 0.20/0.57  tff(u181,negated_conjecture,
% 0.20/0.57      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u180,negated_conjecture,
% 0.20/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))))))).
% 0.20/0.57  
% 0.20/0.57  tff(u179,negated_conjecture,
% 0.20/0.57      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u178,negated_conjecture,
% 0.20/0.57      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.57  
% 0.20/0.57  tff(u177,axiom,
% 0.20/0.57      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.57  
% 0.20/0.57  % (12941)# SZS output end Saturation.
% 0.20/0.57  % (12941)------------------------------
% 0.20/0.57  % (12941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12941)Termination reason: Satisfiable
% 0.20/0.57  
% 0.20/0.57  % (12941)Memory used [KB]: 10874
% 0.20/0.57  % (12941)Time elapsed: 0.151 s
% 0.20/0.57  % (12941)------------------------------
% 0.20/0.57  % (12941)------------------------------
% 0.20/0.58  % (12924)Success in time 0.213 s
%------------------------------------------------------------------------------
