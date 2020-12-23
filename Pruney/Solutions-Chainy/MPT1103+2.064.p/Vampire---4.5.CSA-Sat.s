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
% DateTime   : Thu Dec  3 13:08:42 EST 2020

% Result     : CounterSatisfiable 1.28s
% Output     : Saturation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :   49 (  49 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u179,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u178,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u177,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) )).

tff(u176,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u175,axiom,(
    ! [X1,X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) )).

tff(u174,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) )).

tff(u173,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u172,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u171,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,X1)) )).

tff(u170,axiom,(
    ! [X2] : k1_xboole_0 = k7_subset_1(X2,X2,X2) )).

tff(u169,axiom,(
    ! [X1,X0] : k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1)) )).

tff(u168,negated_conjecture,(
    ! [X1] : k1_xboole_0 = k7_subset_1(sK1,sK1,k2_xboole_0(sK1,X1)) )).

tff(u167,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u166,axiom,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

tff(u165,negated_conjecture,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u164,negated_conjecture,(
    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u163,negated_conjecture,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u162,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u161,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(X2,X1)
      | k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3) ) )).

tff(u160,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u159,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u158,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ r1_tarski(u1_struct_0(sK0),sK1) )).

tff(u157,negated_conjecture,
    ( ~ ~ r1_tarski(k2_struct_0(sK0),sK1)
    | ~ r1_tarski(k2_struct_0(sK0),sK1) )).

tff(u156,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u155,negated_conjecture,(
    r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u154,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

% (24716)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
tff(u153,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u152,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u151,negated_conjecture,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) )).

tff(u149,axiom,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) ) )).

tff(u148,negated_conjecture,(
    l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (24717)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.49  % (24734)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.49  % (24734)Refutation not found, incomplete strategy% (24734)------------------------------
% 0.21/0.49  % (24734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (24734)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (24734)Memory used [KB]: 1663
% 0.21/0.49  % (24734)Time elapsed: 0.096 s
% 0.21/0.49  % (24734)------------------------------
% 0.21/0.49  % (24734)------------------------------
% 0.21/0.50  % (24724)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.50  % (24717)Refutation not found, incomplete strategy% (24717)------------------------------
% 0.21/0.50  % (24717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24717)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24717)Memory used [KB]: 1663
% 0.21/0.50  % (24717)Time elapsed: 0.083 s
% 0.21/0.50  % (24717)------------------------------
% 0.21/0.50  % (24717)------------------------------
% 0.21/0.50  % (24726)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (24726)Refutation not found, incomplete strategy% (24726)------------------------------
% 0.21/0.50  % (24726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24726)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24726)Memory used [KB]: 10746
% 0.21/0.50  % (24726)Time elapsed: 0.102 s
% 0.21/0.50  % (24726)------------------------------
% 0.21/0.50  % (24726)------------------------------
% 0.21/0.51  % (24718)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24738)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (24742)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (24742)Refutation not found, incomplete strategy% (24742)------------------------------
% 0.21/0.52  % (24742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24742)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24742)Memory used [KB]: 6268
% 0.21/0.52  % (24742)Time elapsed: 0.112 s
% 0.21/0.52  % (24742)------------------------------
% 0.21/0.52  % (24742)------------------------------
% 0.21/0.52  % (24720)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (24730)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (24725)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (24727)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (24732)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (24732)Refutation not found, incomplete strategy% (24732)------------------------------
% 0.21/0.52  % (24732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24732)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24732)Memory used [KB]: 10618
% 0.21/0.52  % (24732)Time elapsed: 0.115 s
% 0.21/0.52  % (24732)------------------------------
% 0.21/0.52  % (24732)------------------------------
% 0.21/0.52  % (24725)Refutation not found, incomplete strategy% (24725)------------------------------
% 0.21/0.52  % (24725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24719)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.53  % (24730)Refutation not found, incomplete strategy% (24730)------------------------------
% 1.28/0.53  % (24730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (24736)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.28/0.53  % (24722)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (24741)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.53  % (24728)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.28/0.53  % (24743)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.53  % (24730)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (24730)Memory used [KB]: 1663
% 1.28/0.53  % (24730)Time elapsed: 0.089 s
% 1.28/0.53  % (24730)------------------------------
% 1.28/0.53  % (24730)------------------------------
% 1.28/0.53  % (24738)Refutation not found, incomplete strategy% (24738)------------------------------
% 1.28/0.53  % (24738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (24738)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (24738)Memory used [KB]: 6268
% 1.28/0.53  % (24728)Refutation not found, incomplete strategy% (24728)------------------------------
% 1.28/0.53  % (24728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (24728)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (24728)Memory used [KB]: 10618
% 1.28/0.53  % (24728)Time elapsed: 0.131 s
% 1.28/0.53  % (24728)------------------------------
% 1.28/0.53  % (24728)------------------------------
% 1.28/0.53  % (24738)Time elapsed: 0.096 s
% 1.28/0.53  % (24738)------------------------------
% 1.28/0.53  % (24738)------------------------------
% 1.28/0.54  % (24721)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.54  % SZS status CounterSatisfiable for theBenchmark
% 1.28/0.54  % (24722)# SZS output start Saturation.
% 1.28/0.54  tff(u179,negated_conjecture,
% 1.28/0.54      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 1.28/0.54  
% 1.28/0.54  tff(u178,axiom,
% 1.28/0.54      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.28/0.54  
% 1.28/0.54  tff(u177,axiom,
% 1.28/0.54      (![X1, X0] : ((k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1))))).
% 1.28/0.54  
% 1.28/0.54  tff(u176,axiom,
% 1.28/0.54      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 1.28/0.54  
% 1.28/0.54  tff(u175,axiom,
% 1.28/0.54      (![X1, X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))))))).
% 1.28/0.54  
% 1.28/0.54  tff(u174,axiom,
% 1.28/0.54      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)))))).
% 1.28/0.54  
% 1.28/0.54  tff(u173,negated_conjecture,
% 1.28/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.28/0.54  
% 1.28/0.54  tff(u172,negated_conjecture,
% 1.28/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.28/0.54  
% 1.28/0.54  tff(u171,negated_conjecture,
% 1.28/0.54      (![X1] : ((k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,k2_xboole_0(sK1,X1)))))).
% 1.28/0.54  
% 1.28/0.54  tff(u170,axiom,
% 1.28/0.54      (![X2] : ((k1_xboole_0 = k7_subset_1(X2,X2,X2))))).
% 1.28/0.54  
% 1.28/0.54  tff(u169,axiom,
% 1.28/0.54      (![X1, X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,k2_xboole_0(X0,X1)))))).
% 1.28/0.54  
% 1.28/0.54  tff(u168,negated_conjecture,
% 1.28/0.54      (![X1] : ((k1_xboole_0 = k7_subset_1(sK1,sK1,k2_xboole_0(sK1,X1)))))).
% 1.28/0.54  
% 1.28/0.54  tff(u167,axiom,
% 1.28/0.54      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.28/0.54  
% 1.28/0.54  tff(u166,axiom,
% 1.28/0.54      (![X0] : ((k7_subset_1(X0,X0,k1_xboole_0) = X0)))).
% 1.28/0.54  
% 1.28/0.54  tff(u165,negated_conjecture,
% 1.28/0.54      (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0))))).
% 1.28/0.54  
% 1.28/0.54  tff(u164,negated_conjecture,
% 1.28/0.54      (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))).
% 1.28/0.54  
% 1.28/0.54  tff(u163,negated_conjecture,
% 1.28/0.54      (sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))).
% 1.28/0.54  
% 1.28/0.54  tff(u162,negated_conjecture,
% 1.28/0.54      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 1.28/0.54  
% 1.28/0.54  tff(u161,axiom,
% 1.28/0.54      (![X1, X3, X2] : ((~r1_tarski(X2,X1) | (k7_subset_1(X1,X2,X3) = k7_subset_1(X2,X2,X3)))))).
% 1.28/0.54  
% 1.28/0.54  tff(u160,axiom,
% 1.28/0.54      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 1.28/0.54  
% 1.28/0.54  tff(u159,axiom,
% 1.28/0.54      (![X1, X0] : ((~r1_tarski(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 1.28/0.54  
% 1.28/0.54  tff(u158,negated_conjecture,
% 1.28/0.54      ((~~r1_tarski(u1_struct_0(sK0),sK1)) | ~r1_tarski(u1_struct_0(sK0),sK1))).
% 1.28/0.54  
% 1.28/0.54  tff(u157,negated_conjecture,
% 1.28/0.54      ((~~r1_tarski(k2_struct_0(sK0),sK1)) | ~r1_tarski(k2_struct_0(sK0),sK1))).
% 1.28/0.54  
% 1.28/0.54  tff(u156,axiom,
% 1.28/0.54      (![X1] : (r1_tarski(X1,X1)))).
% 1.28/0.54  
% 1.28/0.54  tff(u155,negated_conjecture,
% 1.28/0.54      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.28/0.54  
% 1.28/0.54  tff(u154,axiom,
% 1.28/0.54      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.28/0.54  
% 1.28/0.54  % (24716)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.54  tff(u153,axiom,
% 1.28/0.54      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 1.28/0.54  
% 1.28/0.54  tff(u152,axiom,
% 1.28/0.54      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 1.28/0.54  
% 1.28/0.54  tff(u151,negated_conjecture,
% 1.28/0.54      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.28/0.54  
% 1.28/0.54  tff(u150,axiom,
% 1.28/0.54      (![X1, X0] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))))).
% 1.28/0.54  
% 1.28/0.54  tff(u149,axiom,
% 1.28/0.54      (![X0] : ((~l1_struct_0(X0) | (u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))))))).
% 1.28/0.54  
% 1.28/0.54  tff(u148,negated_conjecture,
% 1.28/0.54      l1_struct_0(sK0)).
% 1.28/0.54  
% 1.28/0.54  % (24722)# SZS output end Saturation.
% 1.28/0.54  % (24722)------------------------------
% 1.28/0.54  % (24722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24722)Termination reason: Satisfiable
% 1.28/0.54  
% 1.28/0.54  % (24722)Memory used [KB]: 10746
% 1.28/0.54  % (24722)Time elapsed: 0.104 s
% 1.28/0.54  % (24722)------------------------------
% 1.28/0.54  % (24722)------------------------------
% 1.28/0.54  % (24733)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.28/0.54  % (24743)Refutation not found, incomplete strategy% (24743)------------------------------
% 1.28/0.54  % (24743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (24715)Success in time 0.167 s
%------------------------------------------------------------------------------
