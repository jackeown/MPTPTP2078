%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:57 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   58 (  58 expanded)
%              Number of equality atoms :   36 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u187,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u186,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3) )).

tff(u185,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

tff(u184,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) )).

tff(u183,negated_conjecture,
    ( k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u182,negated_conjecture,
    ( k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u181,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u180,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = k3_tarski(k1_enumset1(X0,X0,X0)) )).

tff(u179,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) )).

tff(u178,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) )).

tff(u177,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k4_subset_1(sK1,sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

tff(u176,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k4_subset_1(sK2,sK2,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

tff(u175,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u174,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u173,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u172,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k1_enumset1(sK1,sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK2)) )).

tff(u171,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u170,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u169,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X1) = X0 ) )).

% (26511)Refutation not found, incomplete strategy% (26511)------------------------------
% (26511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u168,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

% (26511)Termination reason: Refutation not found, incomplete strategy

% (26511)Memory used [KB]: 1791
% (26511)Time elapsed: 0.118 s
% (26511)------------------------------
% (26511)------------------------------
tff(u167,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u166,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1) )).

tff(u165,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X3,X2) = k3_tarski(k1_enumset1(X3,X3,X2)) ) )).

tff(u164,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) ) )).

tff(u163,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u162,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k1_enumset1(sK2,sK2,X1)) ) )).

tff(u161,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)) ) )).

tff(u160,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u159,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u158,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:17:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (26497)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (26489)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (26496)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (26497)Refutation not found, incomplete strategy% (26497)------------------------------
% 0.22/0.53  % (26497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26497)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26497)Memory used [KB]: 10746
% 0.22/0.53  % (26497)Time elapsed: 0.114 s
% 0.22/0.53  % (26497)------------------------------
% 0.22/0.53  % (26497)------------------------------
% 0.22/0.54  % (26496)Refutation not found, incomplete strategy% (26496)------------------------------
% 0.22/0.54  % (26496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26496)Memory used [KB]: 10746
% 0.22/0.54  % (26496)Time elapsed: 0.091 s
% 0.22/0.54  % (26496)------------------------------
% 0.22/0.54  % (26496)------------------------------
% 0.22/0.54  % (26494)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (26488)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (26490)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (26505)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (26493)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (26491)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (26492)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (26514)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (26505)Refutation not found, incomplete strategy% (26505)------------------------------
% 0.22/0.54  % (26505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26495)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (26505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26505)Memory used [KB]: 10618
% 0.22/0.54  % (26505)Time elapsed: 0.129 s
% 0.22/0.54  % (26505)------------------------------
% 0.22/0.54  % (26505)------------------------------
% 0.22/0.54  % (26492)Refutation not found, incomplete strategy% (26492)------------------------------
% 0.22/0.54  % (26492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26492)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26492)Memory used [KB]: 6268
% 0.22/0.54  % (26492)Time elapsed: 0.125 s
% 0.22/0.54  % (26492)------------------------------
% 0.22/0.54  % (26492)------------------------------
% 0.22/0.54  % (26493)Refutation not found, incomplete strategy% (26493)------------------------------
% 0.22/0.54  % (26493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26493)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26493)Memory used [KB]: 6268
% 0.22/0.54  % (26493)Time elapsed: 0.125 s
% 0.22/0.54  % (26493)------------------------------
% 0.22/0.54  % (26493)------------------------------
% 0.22/0.54  % (26514)Refutation not found, incomplete strategy% (26514)------------------------------
% 0.22/0.54  % (26514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26490)Refutation not found, incomplete strategy% (26490)------------------------------
% 0.22/0.54  % (26490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26491)Refutation not found, incomplete strategy% (26491)------------------------------
% 0.22/0.54  % (26491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26495)Refutation not found, incomplete strategy% (26495)------------------------------
% 0.22/0.54  % (26495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26506)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (26498)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (26517)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (26511)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (26515)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (26516)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (26509)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (26512)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (26510)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (26510)Refutation not found, incomplete strategy% (26510)------------------------------
% 0.22/0.55  % (26510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26510)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26510)Memory used [KB]: 10746
% 0.22/0.55  % (26510)Time elapsed: 0.100 s
% 0.22/0.55  % (26510)------------------------------
% 0.22/0.55  % (26510)------------------------------
% 0.22/0.55  % (26509)Refutation not found, incomplete strategy% (26509)------------------------------
% 0.22/0.55  % (26509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26501)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (26509)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26509)Memory used [KB]: 1663
% 0.22/0.55  % (26509)Time elapsed: 0.141 s
% 0.22/0.55  % (26509)------------------------------
% 0.22/0.55  % (26509)------------------------------
% 0.22/0.55  % (26504)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (26507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (26498)Refutation not found, incomplete strategy% (26498)------------------------------
% 0.22/0.55  % (26498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26514)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26514)Memory used [KB]: 10746
% 0.22/0.55  % (26514)Time elapsed: 0.129 s
% 0.22/0.55  % (26514)------------------------------
% 0.22/0.55  % (26514)------------------------------
% 0.22/0.55  % (26508)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (26498)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26498)Memory used [KB]: 10618
% 0.22/0.55  % (26498)Time elapsed: 0.140 s
% 0.22/0.55  % (26498)------------------------------
% 0.22/0.55  % (26498)------------------------------
% 0.22/0.55  % (26502)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (26499)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (26513)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (26490)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26490)Memory used [KB]: 10746
% 0.22/0.56  % (26490)Time elapsed: 0.123 s
% 0.22/0.56  % (26490)------------------------------
% 0.22/0.56  % (26490)------------------------------
% 0.22/0.56  % (26499)Refutation not found, incomplete strategy% (26499)------------------------------
% 0.22/0.56  % (26499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26500)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (26508)Refutation not found, incomplete strategy% (26508)------------------------------
% 0.22/0.56  % (26508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26507)Refutation not found, incomplete strategy% (26507)------------------------------
% 0.22/0.56  % (26507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26491)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26491)Memory used [KB]: 10746
% 0.22/0.56  % (26491)Time elapsed: 0.127 s
% 0.22/0.56  % (26491)------------------------------
% 0.22/0.56  % (26491)------------------------------
% 0.22/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.56  % (26507)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  % (26499)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26507)Memory used [KB]: 10746
% 0.22/0.56  
% 0.22/0.56  % (26499)Memory used [KB]: 10746
% 0.22/0.56  % (26507)Time elapsed: 0.142 s
% 0.22/0.56  % (26507)------------------------------
% 0.22/0.56  % (26507)------------------------------
% 0.22/0.56  % (26499)Time elapsed: 0.142 s
% 0.22/0.56  % (26499)------------------------------
% 0.22/0.56  % (26499)------------------------------
% 0.22/0.56  % (26513)Refutation not found, incomplete strategy% (26513)------------------------------
% 0.22/0.56  % (26513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26513)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26517)Refutation not found, incomplete strategy% (26517)------------------------------
% 0.22/0.56  % (26517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26513)Memory used [KB]: 6396
% 0.22/0.56  % (26513)Time elapsed: 0.149 s
% 0.22/0.56  % (26517)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  % (26513)------------------------------
% 0.22/0.56  % (26513)------------------------------
% 0.22/0.56  
% 0.22/0.56  % (26517)Memory used [KB]: 1791
% 0.22/0.56  % (26517)Time elapsed: 0.144 s
% 0.22/0.56  % (26517)------------------------------
% 0.22/0.56  % (26517)------------------------------
% 0.22/0.56  % (26504)# SZS output start Saturation.
% 0.22/0.56  tff(u187,negated_conjecture,
% 0.22/0.56      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.22/0.56  
% 0.22/0.56  tff(u186,axiom,
% 0.22/0.56      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3))))).
% 0.22/0.56  
% 0.22/0.56  tff(u185,negated_conjecture,
% 0.22/0.56      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)))))).
% 0.22/0.56  
% 0.22/0.56  tff(u184,axiom,
% 0.22/0.56      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0))))).
% 0.22/0.56  
% 0.22/0.56  tff(u183,negated_conjecture,
% 0.22/0.56      ((~(k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  tff(u182,negated_conjecture,
% 0.22/0.56      ((~(k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  tff(u181,axiom,
% 0.22/0.56      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.22/0.56  
% 0.22/0.56  tff(u180,axiom,
% 0.22/0.56      (![X0] : ((k4_subset_1(X0,X0,X0) = k3_tarski(k1_enumset1(X0,X0,X0)))))).
% 0.22/0.56  
% 0.22/0.56  tff(u179,negated_conjecture,
% 0.22/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k1_enumset1(sK1,sK1,u1_struct_0(sK0)))))).
% 0.22/0.56  
% 0.22/0.56  tff(u178,negated_conjecture,
% 0.22/0.56      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k1_enumset1(sK2,sK2,u1_struct_0(sK0)))))).
% 0.22/0.56  
% 0.22/0.56  tff(u177,negated_conjecture,
% 0.22/0.56      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)))).
% 0.22/0.56  
% 0.22/0.56  tff(u176,negated_conjecture,
% 0.22/0.56      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)))).
% 0.22/0.56  
% 0.22/0.56  tff(u175,negated_conjecture,
% 0.22/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 0.22/0.56  
% 0.22/0.56  tff(u174,negated_conjecture,
% 0.22/0.56      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 0.22/0.56  
% 0.22/0.56  tff(u173,negated_conjecture,
% 0.22/0.56      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 0.22/0.56  
% 0.22/0.56  tff(u172,negated_conjecture,
% 0.22/0.56      ((~(k2_struct_0(sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK2))))).
% 0.22/0.56  
% 0.22/0.56  tff(u171,negated_conjecture,
% 0.22/0.56      ((~(sK1 = k4_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)))).
% 0.22/0.56  
% 0.22/0.56  tff(u170,negated_conjecture,
% 0.22/0.56      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 0.22/0.56  
% 0.22/0.56  tff(u169,axiom,
% 0.22/0.56      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(k3_tarski(k1_enumset1(X0,X0,X1)),X1) = X0))))).
% 0.22/0.56  
% 0.22/0.56  % (26511)Refutation not found, incomplete strategy% (26511)------------------------------
% 0.22/0.56  % (26511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  tff(u168,axiom,
% 0.22/0.56      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 0.22/0.56  
% 0.22/0.56  % (26511)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26511)Memory used [KB]: 1791
% 0.22/0.56  % (26511)Time elapsed: 0.118 s
% 0.22/0.56  % (26511)------------------------------
% 0.22/0.56  % (26511)------------------------------
% 0.22/0.56  tff(u167,negated_conjecture,
% 0.22/0.56      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 0.22/0.56  
% 0.22/0.56  tff(u166,negated_conjecture,
% 0.22/0.56      ((~r1_xboole_0(sK2,sK1)) | r1_xboole_0(sK2,sK1))).
% 0.22/0.56  
% 0.22/0.56  tff(u165,axiom,
% 0.22/0.56      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k4_subset_1(X3,X3,X2) = k3_tarski(k1_enumset1(X3,X3,X2))))))).
% 0.22/0.56  
% 0.22/0.56  tff(u164,axiom,
% 0.22/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))))))).
% 0.22/0.56  
% 0.22/0.56  tff(u163,axiom,
% 0.22/0.56      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 0.22/0.56  
% 0.22/0.56  tff(u162,negated_conjecture,
% 0.22/0.56      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k1_enumset1(sK2,sK2,X1)))))))).
% 0.22/0.56  
% 0.22/0.56  tff(u161,negated_conjecture,
% 0.22/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k1_enumset1(sK1,sK1,X0)))))))).
% 0.22/0.56  
% 0.22/0.56  tff(u160,negated_conjecture,
% 0.22/0.56      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  tff(u159,negated_conjecture,
% 0.22/0.56      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.56  
% 0.22/0.56  tff(u158,axiom,
% 0.22/0.56      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.22/0.56  
% 0.22/0.56  % (26504)# SZS output end Saturation.
% 0.22/0.56  % (26504)------------------------------
% 0.22/0.56  % (26504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26504)Termination reason: Satisfiable
% 0.22/0.56  
% 0.22/0.56  % (26504)Memory used [KB]: 10746
% 0.22/0.56  % (26504)Time elapsed: 0.118 s
% 0.22/0.56  % (26504)------------------------------
% 0.22/0.56  % (26504)------------------------------
% 0.22/0.56  % (26515)Refutation not found, incomplete strategy% (26515)------------------------------
% 0.22/0.56  % (26515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26515)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26515)Memory used [KB]: 6268
% 0.22/0.56  % (26515)Time elapsed: 0.135 s
% 0.22/0.56  % (26515)------------------------------
% 0.22/0.56  % (26515)------------------------------
% 0.22/0.57  % (26487)Success in time 0.188 s
%------------------------------------------------------------------------------
