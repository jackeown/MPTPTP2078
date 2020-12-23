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
% DateTime   : Thu Dec  3 13:08:43 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   42 (  42 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u209,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u208,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u207,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

tff(u206,axiom,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) )).

tff(u205,axiom,(
    ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

tff(u204,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))
    | k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) )).

tff(u203,axiom,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) )).

% (11528)Termination reason: Refutation not found, incomplete strategy
tff(u202,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

% (11545)Refutation not found, incomplete strategy% (11545)------------------------------
% (11545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u201,axiom,(
    ! [X1] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1) )).

tff(u200,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u199,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u198,axiom,(
    ! [X3,X2] : k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

tff(u197,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))
    | k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) )).

tff(u196,axiom,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

tff(u195,axiom,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 )).

tff(u194,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u193,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) )).

tff(u192,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u191,axiom,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

tff(u190,negated_conjecture,
    ( sK1 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

tff(u189,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u188,axiom,(
    ! [X1,X0] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) )).

tff(u187,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u186,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u185,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) )).

tff(u184,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) )).

tff(u183,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u182,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (11532)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (11548)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.50  % (11540)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (11532)Refutation not found, incomplete strategy% (11532)------------------------------
% 0.21/0.50  % (11532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11532)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11532)Memory used [KB]: 6268
% 0.21/0.50  % (11532)Time elapsed: 0.097 s
% 0.21/0.50  % (11532)------------------------------
% 0.21/0.50  % (11532)------------------------------
% 0.21/0.51  % (11524)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11525)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11534)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (11524)Refutation not found, incomplete strategy% (11524)------------------------------
% 0.21/0.51  % (11524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11524)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11524)Memory used [KB]: 6268
% 0.21/0.51  % (11524)Time elapsed: 0.110 s
% 0.21/0.51  % (11524)------------------------------
% 0.21/0.51  % (11524)------------------------------
% 0.21/0.51  % (11522)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11530)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (11522)Refutation not found, incomplete strategy% (11522)------------------------------
% 0.21/0.51  % (11522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11522)Memory used [KB]: 10746
% 0.21/0.51  % (11522)Time elapsed: 0.106 s
% 0.21/0.51  % (11522)------------------------------
% 0.21/0.51  % (11522)------------------------------
% 0.21/0.51  % (11540)Refutation not found, incomplete strategy% (11540)------------------------------
% 0.21/0.51  % (11540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11540)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11540)Memory used [KB]: 10746
% 0.21/0.51  % (11540)Time elapsed: 0.104 s
% 0.21/0.51  % (11540)------------------------------
% 0.21/0.51  % (11540)------------------------------
% 0.21/0.51  % (11530)Refutation not found, incomplete strategy% (11530)------------------------------
% 0.21/0.51  % (11530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11530)Memory used [KB]: 10618
% 0.21/0.52  % (11530)Time elapsed: 0.108 s
% 0.21/0.52  % (11530)------------------------------
% 0.21/0.52  % (11530)------------------------------
% 0.21/0.52  % (11520)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (11535)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (11535)Refutation not found, incomplete strategy% (11535)------------------------------
% 0.21/0.52  % (11535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11535)Memory used [KB]: 6140
% 0.21/0.52  % (11535)Time elapsed: 0.001 s
% 0.21/0.52  % (11535)------------------------------
% 0.21/0.52  % (11535)------------------------------
% 0.21/0.52  % (11542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (11544)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (11520)Refutation not found, incomplete strategy% (11520)------------------------------
% 0.21/0.52  % (11520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11520)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11520)Memory used [KB]: 1663
% 0.21/0.52  % (11520)Time elapsed: 0.116 s
% 0.21/0.52  % (11520)------------------------------
% 0.21/0.52  % (11520)------------------------------
% 0.21/0.53  % (11528)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (11543)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (11521)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (11523)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11542)Refutation not found, incomplete strategy% (11542)------------------------------
% 0.21/0.53  % (11542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11542)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11542)Memory used [KB]: 10618
% 0.21/0.53  % (11542)Time elapsed: 0.098 s
% 0.21/0.53  % (11542)------------------------------
% 0.21/0.53  % (11542)------------------------------
% 0.21/0.53  % (11527)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (11546)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (11536)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (11525)Refutation not found, incomplete strategy% (11525)------------------------------
% 0.21/0.53  % (11525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11547)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (11523)Refutation not found, incomplete strategy% (11523)------------------------------
% 0.21/0.53  % (11523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11539)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (11525)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11525)Memory used [KB]: 6268
% 0.21/0.53  % (11525)Time elapsed: 0.128 s
% 0.21/0.53  % (11525)------------------------------
% 0.21/0.53  % (11525)------------------------------
% 0.21/0.54  % (11545)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (11531)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (11537)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (11549)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (11543)Refutation not found, incomplete strategy% (11543)------------------------------
% 0.21/0.54  % (11543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11538)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (11526)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (11529)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (11541)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (11527)Refutation not found, incomplete strategy% (11527)------------------------------
% 0.21/0.54  % (11527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11543)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11543)Memory used [KB]: 1663
% 0.21/0.54  % (11543)Time elapsed: 0.137 s
% 0.21/0.54  % (11543)------------------------------
% 0.21/0.54  % (11543)------------------------------
% 0.21/0.54  % (11537)Refutation not found, incomplete strategy% (11537)------------------------------
% 0.21/0.54  % (11537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.54  % (11527)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11527)Memory used [KB]: 6268
% 0.21/0.54  % (11527)Time elapsed: 0.141 s
% 0.21/0.54  % (11527)------------------------------
% 0.21/0.54  % (11527)------------------------------
% 0.21/0.54  % (11533)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (11541)Refutation not found, incomplete strategy% (11541)------------------------------
% 0.21/0.54  % (11541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11528)Refutation not found, incomplete strategy% (11528)------------------------------
% 0.21/0.54  % (11528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11536)# SZS output start Saturation.
% 0.21/0.54  tff(u209,negated_conjecture,
% 0.21/0.54      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u208,axiom,
% 0.21/0.54      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u207,axiom,
% 0.21/0.54      (![X1, X2] : ((k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2))))).
% 0.21/0.54  
% 0.21/0.54  tff(u206,axiom,
% 0.21/0.54      (![X1] : ((k1_xboole_0 = k5_xboole_0(X1,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u205,axiom,
% 0.21/0.54      (![X1, X0] : ((k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u204,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))))) | (k1_xboole_0 = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u203,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = k3_subset_1(X0,X0))))).
% 0.21/0.54  
% 0.21/0.54  % (11528)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  tff(u202,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 0.21/0.54  
% 0.21/0.54  
% 0.21/0.54  % (11545)Refutation not found, incomplete strategy% (11545)------------------------------
% 0.21/0.54  % (11545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  tff(u201,axiom,
% 0.21/0.54      (![X1] : ((k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u200,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u199,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u198,axiom,
% 0.21/0.54      (![X3, X2] : ((k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))))))).
% 0.21/0.54  
% 0.21/0.54  tff(u197,negated_conjecture,
% 0.21/0.54      ((~(k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))))) | (k1_xboole_0 = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u196,axiom,
% 0.21/0.54      (![X0] : ((k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u195,axiom,
% 0.21/0.54      (![X0] : ((k3_subset_1(X0,k1_xboole_0) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u194,negated_conjecture,
% 0.21/0.54      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))).
% 0.21/0.54  
% 0.21/0.54  tff(u193,negated_conjecture,
% 0.21/0.54      ((~(k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))))) | (k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u192,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u191,axiom,
% 0.21/0.54      (![X0] : ((k1_setfam_1(k2_tarski(X0,X0)) = X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u190,negated_conjecture,
% 0.21/0.54      ((~(sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | (sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u189,axiom,
% 0.21/0.54      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u188,axiom,
% 0.21/0.54      (![X1, X0] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u187,axiom,
% 0.21/0.54      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.54  
% 0.21/0.54  tff(u186,axiom,
% 0.21/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u185,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)))))).
% 0.21/0.54  
% 0.21/0.54  tff(u184,axiom,
% 0.21/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1))))).
% 0.21/0.54  
% 0.21/0.54  tff(u183,negated_conjecture,
% 0.21/0.54      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.54  
% 0.21/0.54  tff(u182,axiom,
% 0.21/0.54      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.21/0.54  
% 0.21/0.54  % (11536)# SZS output end Saturation.
% 0.21/0.54  % (11536)------------------------------
% 0.21/0.54  % (11536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11536)Termination reason: Satisfiable
% 0.21/0.54  
% 0.21/0.54  % (11536)Memory used [KB]: 10746
% 0.21/0.54  % (11536)Time elapsed: 0.144 s
% 0.21/0.54  % (11536)------------------------------
% 0.21/0.54  % (11536)------------------------------
% 0.21/0.54  % (11528)Memory used [KB]: 10746
% 0.21/0.54  % (11528)Time elapsed: 0.142 s
% 0.21/0.54  % (11528)------------------------------
% 0.21/0.54  % (11528)------------------------------
% 0.21/0.54  % (11519)Success in time 0.182 s
%------------------------------------------------------------------------------
