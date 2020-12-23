%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:00 EST 2020

% Result     : CounterSatisfiable 1.56s
% Output     : Saturation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    0
%              Number of atoms          :   60 (  60 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u189,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) )).

tff(u188,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != k3_tarski(k2_tarski(X0,X1))
      | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ) )).

tff(u187,axiom,(
    ! [X1,X2] :
      ( k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1)
      | r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1) ) )).

tff(u186,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u185,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u184,negated_conjecture,
    ( ~ ( sK2 != k2_struct_0(sK0) )
    | sK2 != k2_struct_0(sK0) )).

tff(u183,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) )).

tff(u182,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) )).

tff(u181,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

tff(u180,axiom,(
    ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) )).

tff(u179,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k3_tarski(k2_tarski(sK1,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) )).

tff(u178,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k3_tarski(k2_tarski(sK2,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) )).

tff(u177,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u176,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

% (6113)Refutation not found, incomplete strategy% (6113)------------------------------
% (6113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6113)Termination reason: Refutation not found, incomplete strategy

% (6113)Memory used [KB]: 6268
% (6113)Time elapsed: 0.109 s
% (6113)------------------------------
% (6113)------------------------------
% (6114)Refutation not found, incomplete strategy% (6114)------------------------------
% (6114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
tff(u175,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u174,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

tff(u173,negated_conjecture,
    ( sK1 != k4_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK1,sK2) )).

tff(u172,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u171,negated_conjecture,
    ( sK2 != k4_xboole_0(sK2,sK1)
    | sK2 = k4_xboole_0(sK2,sK1) )).

tff(u170,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u169,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u168,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u167,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u166,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1) )).

tff(u165,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) )).

tff(u164,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u163,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)) ) )).

tff(u162,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) )).

tff(u161,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u160,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (6106)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (6106)Refutation not found, incomplete strategy% (6106)------------------------------
% 0.22/0.55  % (6106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6128)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (6106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6106)Memory used [KB]: 1791
% 0.22/0.56  % (6106)Time elapsed: 0.120 s
% 0.22/0.56  % (6106)------------------------------
% 0.22/0.56  % (6106)------------------------------
% 0.22/0.56  % (6130)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (6121)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (6107)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.57  % (6122)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.57  % (6111)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.57  % (6113)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.57  % (6120)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.57  % (6128)Refutation not found, incomplete strategy% (6128)------------------------------
% 1.56/0.57  % (6128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (6128)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (6128)Memory used [KB]: 10746
% 1.56/0.57  % (6128)Time elapsed: 0.139 s
% 1.56/0.57  % (6128)------------------------------
% 1.56/0.57  % (6128)------------------------------
% 1.56/0.58  % (6121)Refutation not found, incomplete strategy% (6121)------------------------------
% 1.56/0.58  % (6121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (6121)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (6121)Memory used [KB]: 6140
% 1.56/0.58  % (6121)Time elapsed: 0.004 s
% 1.56/0.58  % (6121)------------------------------
% 1.56/0.58  % (6121)------------------------------
% 1.56/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.56/0.58  % (6114)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.58  % (6122)# SZS output start Saturation.
% 1.56/0.58  tff(u189,axiom,
% 1.56/0.58      (![X1, X0] : (((k4_xboole_0(X0,X1) != X0) | r1_xboole_0(X0,X1))))).
% 1.56/0.58  
% 1.56/0.58  tff(u188,axiom,
% 1.56/0.58      (![X1, X0] : (((k4_xboole_0(X0,X1) != k3_tarski(k2_tarski(X0,X1))) | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))))).
% 1.56/0.58  
% 1.56/0.58  tff(u187,axiom,
% 1.56/0.58      (![X1, X2] : (((k3_tarski(k2_tarski(X1,X2)) != k4_xboole_0(X2,X1)) | r1_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1))))).
% 1.56/0.58  
% 1.56/0.58  tff(u186,negated_conjecture,
% 1.56/0.58      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 1.56/0.58  
% 1.56/0.58  tff(u185,negated_conjecture,
% 1.56/0.58      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.56/0.58  
% 1.56/0.58  tff(u184,negated_conjecture,
% 1.56/0.58      ((~(sK2 != k2_struct_0(sK0))) | (sK2 != k2_struct_0(sK0)))).
% 1.56/0.58  
% 1.56/0.58  tff(u183,axiom,
% 1.56/0.58      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))))).
% 1.56/0.58  
% 1.56/0.58  tff(u182,axiom,
% 1.56/0.58      (![X1, X0] : ((k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))))).
% 1.56/0.58  
% 1.56/0.58  tff(u181,negated_conjecture,
% 1.56/0.58      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)))))).
% 1.56/0.58  
% 1.56/0.58  tff(u180,axiom,
% 1.56/0.58      (![X1, X0] : ((k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)))))).
% 1.56/0.58  
% 1.78/0.58  tff(u179,negated_conjecture,
% 1.78/0.58      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1))))).
% 1.78/0.58  
% 1.78/0.58  tff(u178,negated_conjecture,
% 1.78/0.58      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2))))).
% 1.78/0.58  
% 1.78/0.58  tff(u177,negated_conjecture,
% 1.78/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 1.78/0.58  
% 1.78/0.58  tff(u176,negated_conjecture,
% 1.78/0.58      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 1.78/0.58  
% 1.78/0.59  % (6113)Refutation not found, incomplete strategy% (6113)------------------------------
% 1.78/0.59  % (6113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (6113)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.59  
% 1.78/0.59  % (6113)Memory used [KB]: 6268
% 1.78/0.59  % (6113)Time elapsed: 0.109 s
% 1.78/0.59  % (6113)------------------------------
% 1.78/0.59  % (6113)------------------------------
% 1.78/0.59  % (6114)Refutation not found, incomplete strategy% (6114)------------------------------
% 1.78/0.59  % (6114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  tff(u175,negated_conjecture,
% 1.78/0.59      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 1.78/0.59  
% 1.78/0.59  tff(u174,negated_conjecture,
% 1.78/0.59      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))))).
% 1.78/0.59  
% 1.78/0.59  tff(u173,negated_conjecture,
% 1.78/0.59      ((~(sK1 = k4_xboole_0(sK1,sK2))) | (sK1 = k4_xboole_0(sK1,sK2)))).
% 1.78/0.59  
% 1.78/0.59  tff(u172,negated_conjecture,
% 1.78/0.59      ((~(sK1 = k4_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)))).
% 1.78/0.59  
% 1.78/0.59  tff(u171,negated_conjecture,
% 1.78/0.59      ((~(sK2 = k4_xboole_0(sK2,sK1))) | (sK2 = k4_xboole_0(sK2,sK1)))).
% 1.78/0.59  
% 1.78/0.59  tff(u170,negated_conjecture,
% 1.78/0.59      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 1.78/0.59  
% 1.78/0.59  tff(u169,axiom,
% 1.78/0.59      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 1.78/0.59  
% 1.78/0.59  tff(u168,axiom,
% 1.78/0.59      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 1.78/0.59  
% 1.78/0.59  tff(u167,negated_conjecture,
% 1.78/0.59      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 1.78/0.59  
% 1.78/0.59  tff(u166,negated_conjecture,
% 1.78/0.59      ((~r1_xboole_0(sK2,sK1)) | r1_xboole_0(sK2,sK1))).
% 1.78/0.59  
% 1.78/0.59  tff(u165,axiom,
% 1.78/0.59      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))))))).
% 1.78/0.59  
% 1.78/0.59  tff(u164,axiom,
% 1.78/0.59      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 1.78/0.59  
% 1.78/0.59  tff(u163,negated_conjecture,
% 1.78/0.59      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)))))))).
% 1.78/0.59  
% 1.78/0.59  tff(u162,negated_conjecture,
% 1.78/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))))))).
% 1.78/0.59  
% 1.78/0.59  tff(u161,negated_conjecture,
% 1.78/0.59      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.78/0.59  
% 1.78/0.59  tff(u160,negated_conjecture,
% 1.78/0.59      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.78/0.59  
% 1.78/0.59  % (6122)# SZS output end Saturation.
% 1.78/0.59  % (6122)------------------------------
% 1.78/0.59  % (6122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (6122)Termination reason: Satisfiable
% 1.78/0.59  
% 1.78/0.59  % (6122)Memory used [KB]: 10746
% 1.78/0.59  % (6122)Time elapsed: 0.152 s
% 1.78/0.59  % (6122)------------------------------
% 1.78/0.59  % (6122)------------------------------
% 1.78/0.59  % (6105)Success in time 0.225 s
%------------------------------------------------------------------------------
