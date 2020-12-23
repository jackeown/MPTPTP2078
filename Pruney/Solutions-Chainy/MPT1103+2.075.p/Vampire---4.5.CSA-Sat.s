%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u193,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u192,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1 )).

tff(u191,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

tff(u190,axiom,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) )).

tff(u189,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) )).

tff(u188,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

tff(u187,axiom,(
    ! [X5] : k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,k1_xboole_0) )).

tff(u186,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u185,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u184,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u183,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u182,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) )).

tff(u181,axiom,(
    ! [X1] : k7_subset_1(X1,X1,k1_xboole_0) = X1 )).

tff(u180,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u179,axiom,(
    ! [X3,X4] : k7_subset_1(X3,k1_xboole_0,X4) = k7_subset_1(k1_xboole_0,k1_xboole_0,X4) )).

tff(u178,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

tff(u177,axiom,(
    ! [X3,X4] : k7_subset_1(X3,k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X4))) )).

tff(u176,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u175,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u174,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u173,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u172,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) )).

tff(u171,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u170,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u169,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u168,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (22688)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.48  % (22688)Refutation not found, incomplete strategy% (22688)------------------------------
% 0.22/0.48  % (22688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (22704)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.49  % (22688)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (22688)Memory used [KB]: 6268
% 0.22/0.49  % (22688)Time elapsed: 0.087 s
% 0.22/0.49  % (22688)------------------------------
% 0.22/0.49  % (22688)------------------------------
% 0.22/0.49  % (22712)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.50  % (22704)Refutation not found, incomplete strategy% (22704)------------------------------
% 0.22/0.50  % (22704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (22704)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22704)Memory used [KB]: 1663
% 0.22/0.50  % (22704)Time elapsed: 0.107 s
% 0.22/0.50  % (22704)------------------------------
% 0.22/0.50  % (22704)------------------------------
% 0.22/0.50  % (22712)Refutation not found, incomplete strategy% (22712)------------------------------
% 0.22/0.50  % (22712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (22712)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (22712)Memory used [KB]: 1791
% 0.22/0.50  % (22712)Time elapsed: 0.108 s
% 0.22/0.50  % (22712)------------------------------
% 0.22/0.50  % (22712)------------------------------
% 0.22/0.51  % (22684)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (22683)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (22683)Refutation not found, incomplete strategy% (22683)------------------------------
% 0.22/0.52  % (22683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22683)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22683)Memory used [KB]: 1663
% 0.22/0.52  % (22683)Time elapsed: 0.103 s
% 0.22/0.52  % (22683)------------------------------
% 0.22/0.52  % (22683)------------------------------
% 0.22/0.52  % (22686)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (22706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (22685)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (22706)Refutation not found, incomplete strategy% (22706)------------------------------
% 0.22/0.52  % (22706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22706)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22706)Memory used [KB]: 1663
% 0.22/0.52  % (22706)Time elapsed: 0.082 s
% 0.22/0.52  % (22706)------------------------------
% 0.22/0.52  % (22706)------------------------------
% 0.22/0.52  % (22699)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (22698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (22698)Refutation not found, incomplete strategy% (22698)------------------------------
% 0.22/0.52  % (22698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (22698)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (22698)Memory used [KB]: 6140
% 0.22/0.52  % (22698)Time elapsed: 0.002 s
% 0.22/0.52  % (22698)------------------------------
% 0.22/0.52  % (22698)------------------------------
% 0.22/0.52  % (22691)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (22691)Refutation not found, incomplete strategy% (22691)------------------------------
% 0.22/0.53  % (22691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (22691)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (22691)Memory used [KB]: 10618
% 0.22/0.53  % (22691)Time elapsed: 0.119 s
% 0.22/0.53  % (22691)------------------------------
% 0.22/0.53  % (22691)------------------------------
% 0.22/0.53  % (22707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (22697)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (22690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (22690)Refutation not found, incomplete strategy% (22690)------------------------------
% 0.22/0.54  % (22690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22690)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22690)Memory used [KB]: 6268
% 0.22/0.54  % (22690)Time elapsed: 0.108 s
% 0.22/0.54  % (22690)------------------------------
% 0.22/0.54  % (22690)------------------------------
% 0.22/0.54  % (22685)Refutation not found, incomplete strategy% (22685)------------------------------
% 0.22/0.54  % (22685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22685)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22685)Memory used [KB]: 10618
% 0.22/0.54  % (22685)Time elapsed: 0.128 s
% 0.22/0.54  % (22685)------------------------------
% 0.22/0.54  % (22685)------------------------------
% 0.22/0.54  % (22686)Refutation not found, incomplete strategy% (22686)------------------------------
% 0.22/0.54  % (22686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22686)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (22686)Memory used [KB]: 10746
% 0.22/0.54  % (22686)Time elapsed: 0.111 s
% 0.22/0.54  % (22686)------------------------------
% 0.22/0.54  % (22686)------------------------------
% 0.22/0.54  % (22705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (22710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.54  % (22699)# SZS output start Saturation.
% 0.22/0.54  tff(u193,negated_conjecture,
% 0.22/0.54      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u192,axiom,
% 0.22/0.54      (![X1] : ((k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_xboole_0))) = X1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u191,axiom,
% 0.22/0.54      (![X1, X2] : ((k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2))))).
% 0.22/0.54  
% 0.22/0.54  tff(u190,axiom,
% 0.22/0.54      (![X1] : ((k1_xboole_0 = k3_subset_1(X1,X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u189,axiom,
% 0.22/0.54      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u188,axiom,
% 0.22/0.54      (![X1] : ((k1_xboole_0 = k7_subset_1(X1,X1,X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u187,axiom,
% 0.22/0.54      (![X5] : ((k1_xboole_0 = k7_subset_1(X5,k1_xboole_0,k1_xboole_0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u186,negated_conjecture,
% 0.22/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u185,negated_conjecture,
% 0.22/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u184,axiom,
% 0.22/0.54      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u183,negated_conjecture,
% 0.22/0.54      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u182,negated_conjecture,
% 0.22/0.54      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u181,axiom,
% 0.22/0.54      (![X1] : ((k7_subset_1(X1,X1,k1_xboole_0) = X1)))).
% 0.22/0.54  
% 0.22/0.54  tff(u180,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u179,axiom,
% 0.22/0.54      (![X3, X4] : ((k7_subset_1(X3,k1_xboole_0,X4) = k7_subset_1(k1_xboole_0,k1_xboole_0,X4))))).
% 0.22/0.54  
% 0.22/0.54  tff(u178,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u177,axiom,
% 0.22/0.54      (![X3, X4] : ((k7_subset_1(X3,k1_xboole_0,X4) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X4))))))).
% 0.22/0.54  
% 0.22/0.54  tff(u176,negated_conjecture,
% 0.22/0.54      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u175,axiom,
% 0.22/0.54      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u174,axiom,
% 0.22/0.54      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.22/0.54  
% 0.22/0.54  tff(u173,axiom,
% 0.22/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u172,axiom,
% 0.22/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)))))).
% 0.22/0.54  
% 0.22/0.54  tff(u171,axiom,
% 0.22/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.22/0.54  
% 0.22/0.54  tff(u170,negated_conjecture,
% 0.22/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u169,axiom,
% 0.22/0.54      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.22/0.54  
% 0.22/0.54  tff(u168,axiom,
% 0.22/0.54      (![X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))))).
% 0.22/0.54  
% 0.22/0.54  % (22699)# SZS output end Saturation.
% 0.22/0.54  % (22699)------------------------------
% 0.22/0.54  % (22699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (22699)Termination reason: Satisfiable
% 0.22/0.54  
% 0.22/0.54  % (22699)Memory used [KB]: 10746
% 0.22/0.54  % (22699)Time elapsed: 0.110 s
% 0.22/0.54  % (22699)------------------------------
% 0.22/0.54  % (22699)------------------------------
% 0.22/0.54  % (22689)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (22709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (22682)Success in time 0.174 s
%------------------------------------------------------------------------------
