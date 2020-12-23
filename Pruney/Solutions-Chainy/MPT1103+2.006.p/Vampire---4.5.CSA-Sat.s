%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:34 EST 2020

% Result     : CounterSatisfiable 1.69s
% Output     : Saturation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u180,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k7_subset_1(X0,X0,X1)
      | r1_tarski(X0,X1) ) )).

tff(u179,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )
    | sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

tff(u178,negated_conjecture,
    ( ~ ( sK1 != k7_subset_1(sK1,sK1,k1_xboole_0) )
    | sK1 != k7_subset_1(sK1,sK1,k1_xboole_0) )).

tff(u177,negated_conjecture,
    ( ~ ( k2_struct_0(sK0) != sK1 )
    | k2_struct_0(sK0) != sK1 )).

tff(u176,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u175,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u174,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u173,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) )).

tff(u172,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) )).

tff(u171,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) )).

tff(u170,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u169,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u168,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u167,negated_conjecture,
    ( u1_struct_0(sK0) != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

tff(u166,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) )).

tff(u165,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k7_subset_1(X0,X0,X1) ) )).

tff(u164,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u163,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u162,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u161,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ) )).

tff(u160,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u159,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u158,axiom,(
    ! [X1,X0] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) )).

tff(u157,negated_conjecture,
    ( ~ l1_struct_0(sK0)
    | l1_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:44:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (1059)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (1075)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (1067)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (1061)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (1061)Refutation not found, incomplete strategy% (1061)------------------------------
% 0.21/0.55  % (1061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1061)Memory used [KB]: 10746
% 0.21/0.55  % (1061)Time elapsed: 0.131 s
% 0.21/0.55  % (1061)------------------------------
% 0.21/0.55  % (1061)------------------------------
% 0.21/0.55  % (1052)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (1052)Refutation not found, incomplete strategy% (1052)------------------------------
% 0.21/0.56  % (1052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1052)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1052)Memory used [KB]: 1663
% 0.21/0.56  % (1052)Time elapsed: 0.140 s
% 0.21/0.56  % (1052)------------------------------
% 0.21/0.56  % (1052)------------------------------
% 0.21/0.56  % (1067)Refutation not found, incomplete strategy% (1067)------------------------------
% 0.21/0.56  % (1067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1075)Refutation not found, incomplete strategy% (1075)------------------------------
% 0.21/0.56  % (1075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1067)Memory used [KB]: 10618
% 0.21/0.56  % (1067)Time elapsed: 0.135 s
% 0.21/0.56  % (1067)------------------------------
% 0.21/0.56  % (1067)------------------------------
% 0.21/0.56  % (1077)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (1075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1075)Memory used [KB]: 10618
% 0.21/0.56  % (1075)Time elapsed: 0.145 s
% 0.21/0.56  % (1075)------------------------------
% 0.21/0.56  % (1075)------------------------------
% 0.21/0.56  % (1077)Refutation not found, incomplete strategy% (1077)------------------------------
% 0.21/0.56  % (1077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1077)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (1077)Memory used [KB]: 6268
% 0.21/0.56  % (1077)Time elapsed: 0.155 s
% 0.21/0.56  % (1077)------------------------------
% 0.21/0.56  % (1077)------------------------------
% 0.21/0.56  % (1073)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (1073)Refutation not found, incomplete strategy% (1073)------------------------------
% 0.21/0.57  % (1073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (1057)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.58  % (1056)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.69/0.58  % (1069)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.69/0.58  % (1069)Refutation not found, incomplete strategy% (1069)------------------------------
% 1.69/0.58  % (1069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (1069)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.58  
% 1.69/0.58  % (1069)Memory used [KB]: 1663
% 1.69/0.58  % (1069)Time elapsed: 0.176 s
% 1.69/0.58  % (1069)------------------------------
% 1.69/0.58  % (1069)------------------------------
% 1.69/0.58  % (1071)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.69/0.59  % SZS status CounterSatisfiable for theBenchmark
% 1.69/0.59  % (1073)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (1073)Memory used [KB]: 6268
% 1.69/0.59  % (1073)Time elapsed: 0.076 s
% 1.69/0.59  % (1073)------------------------------
% 1.69/0.59  % (1073)------------------------------
% 1.69/0.59  % (1051)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.69/0.59  % (1071)# SZS output start Saturation.
% 1.69/0.59  tff(u180,axiom,
% 1.69/0.59      (![X1, X0] : (((k1_xboole_0 != k7_subset_1(X0,X0,X1)) | r1_tarski(X0,X1))))).
% 1.69/0.59  
% 1.69/0.59  tff(u179,negated_conjecture,
% 1.69/0.59      ((~(sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0))) | (sK1 != k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)))).
% 1.69/0.59  
% 1.69/0.59  tff(u178,negated_conjecture,
% 1.69/0.59      ((~(sK1 != k7_subset_1(sK1,sK1,k1_xboole_0))) | (sK1 != k7_subset_1(sK1,sK1,k1_xboole_0)))).
% 1.69/0.59  
% 1.69/0.59  tff(u177,negated_conjecture,
% 1.69/0.59      ((~(k2_struct_0(sK0) != sK1)) | (k2_struct_0(sK0) != sK1))).
% 1.69/0.59  
% 1.69/0.59  tff(u176,axiom,
% 1.69/0.59      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 1.69/0.59  
% 1.69/0.59  tff(u175,negated_conjecture,
% 1.69/0.59      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.69/0.59  
% 1.69/0.59  tff(u174,negated_conjecture,
% 1.69/0.59      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.69/0.59  
% 1.69/0.59  tff(u173,axiom,
% 1.69/0.59      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))))))).
% 1.69/0.59  
% 1.69/0.59  tff(u172,axiom,
% 1.69/0.59      (![X1, X0] : ((k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1))))).
% 1.69/0.59  
% 1.69/0.59  tff(u171,axiom,
% 1.69/0.59      (![X1, X0] : ((k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1))))).
% 1.69/0.59  
% 1.69/0.59  tff(u170,axiom,
% 1.69/0.59      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 1.69/0.59  
% 1.69/0.59  tff(u169,axiom,
% 1.69/0.59      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.69/0.59  
% 1.69/0.59  tff(u168,negated_conjecture,
% 1.69/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 1.69/0.59  
% 1.69/0.59  tff(u167,negated_conjecture,
% 1.69/0.59      ((~(u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))))) | (u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))))).
% 1.69/0.59  
% 1.69/0.59  tff(u166,negated_conjecture,
% 1.69/0.59      ((~(sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0))) | (sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)))).
% 1.69/0.59  
% 1.69/0.59  tff(u165,axiom,
% 1.69/0.59      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_xboole_0 = k7_subset_1(X0,X0,X1)))))).
% 1.69/0.59  
% 1.69/0.59  tff(u164,axiom,
% 1.69/0.59      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 1.69/0.59  
% 1.69/0.59  tff(u163,axiom,
% 1.69/0.59      (![X1] : (r1_tarski(X1,X1)))).
% 1.69/0.59  
% 1.69/0.59  tff(u162,axiom,
% 1.69/0.59      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.69/0.59  
% 1.69/0.59  tff(u161,negated_conjecture,
% 1.69/0.59      ((~l1_struct_0(sK0)) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0)))))).
% 1.69/0.59  
% 1.69/0.59  tff(u160,negated_conjecture,
% 1.69/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.69/0.59  
% 1.69/0.59  tff(u159,axiom,
% 1.69/0.59      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.69/0.59  
% 1.69/0.59  tff(u158,axiom,
% 1.69/0.59      (![X1, X0] : ((~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))))).
% 1.69/0.59  
% 1.69/0.59  tff(u157,negated_conjecture,
% 1.69/0.59      ((~l1_struct_0(sK0)) | l1_struct_0(sK0))).
% 1.69/0.59  
% 1.69/0.59  % (1071)# SZS output end Saturation.
% 1.69/0.59  % (1071)------------------------------
% 1.69/0.59  % (1071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (1071)Termination reason: Satisfiable
% 1.69/0.59  
% 1.69/0.59  % (1071)Memory used [KB]: 10746
% 1.69/0.59  % (1071)Time elapsed: 0.094 s
% 1.69/0.59  % (1071)------------------------------
% 1.69/0.59  % (1071)------------------------------
% 1.69/0.59  % (1050)Success in time 0.231 s
%------------------------------------------------------------------------------
