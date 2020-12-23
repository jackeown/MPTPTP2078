%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:39 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u169,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k7_subset_1(X0,X0,X1)
      | r1_tarski(X0,X1) ) )).

tff(u168,negated_conjecture,
    ( ~ ( k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1) )
    | k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1) )).

tff(u167,negated_conjecture,
    ( ~ ( sK1 != k2_struct_0(sK0) )
    | sK1 != k2_struct_0(sK0) )).

tff(u166,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u165,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u164,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = k5_xboole_0(sK1,sK1) )).

tff(u163,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u162,axiom,(
    ! [X4] : k1_xboole_0 = k7_subset_1(X4,X4,X4) )).

tff(u161,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(sK1,sK1,u1_struct_0(sK0))
    | k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

tff(u160,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u159,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u158,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

tff(u157,axiom,(
    ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) )).

tff(u156,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) != k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)
    | k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

tff(u155,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u154,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u153,negated_conjecture,
    ( sK1 != k3_xboole_0(sK1,u1_struct_0(sK0))
    | sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u152,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k7_subset_1(X0,X0,X1) ) )).

tff(u151,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u150,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) )).

tff(u149,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u148,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

tff(u147,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u146,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u145,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u144,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:36:49 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.47  % (24054)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (24069)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.50  % (24073)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (24065)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (24065)Refutation not found, incomplete strategy% (24065)------------------------------
% 0.20/0.50  % (24065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24065)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24065)Memory used [KB]: 6268
% 0.20/0.50  % (24065)Time elapsed: 0.086 s
% 0.20/0.50  % (24065)------------------------------
% 0.20/0.50  % (24065)------------------------------
% 0.20/0.51  % (24061)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (24073)Refutation not found, incomplete strategy% (24073)------------------------------
% 0.20/0.51  % (24073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24073)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24073)Memory used [KB]: 10746
% 0.20/0.51  % (24073)Time elapsed: 0.085 s
% 0.20/0.51  % (24073)------------------------------
% 0.20/0.51  % (24073)------------------------------
% 0.20/0.51  % (24077)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (24067)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (24056)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (24055)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24055)Refutation not found, incomplete strategy% (24055)------------------------------
% 0.20/0.51  % (24055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24055)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24055)Memory used [KB]: 10618
% 0.20/0.51  % (24055)Time elapsed: 0.108 s
% 0.20/0.51  % (24055)------------------------------
% 0.20/0.51  % (24055)------------------------------
% 0.20/0.51  % (24053)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (24064)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (24053)Refutation not found, incomplete strategy% (24053)------------------------------
% 0.20/0.52  % (24053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24053)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24053)Memory used [KB]: 1663
% 0.20/0.52  % (24053)Time elapsed: 0.108 s
% 0.20/0.52  % (24053)------------------------------
% 0.20/0.52  % (24053)------------------------------
% 0.20/0.52  % (24059)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (24063)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (24069)# SZS output start Saturation.
% 0.20/0.52  tff(u169,axiom,
% 0.20/0.52      (![X1, X0] : (((k1_xboole_0 != k7_subset_1(X0,X0,X1)) | r1_tarski(X0,X1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u168,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1))) | (k1_xboole_0 != k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u167,negated_conjecture,
% 0.20/0.52      ((~(sK1 != k2_struct_0(sK0))) | (sK1 != k2_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u166,axiom,
% 0.20/0.52      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u165,axiom,
% 0.20/0.52      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u164,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 = k5_xboole_0(sK1,sK1))) | (k1_xboole_0 = k5_xboole_0(sK1,sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u163,axiom,
% 0.20/0.52      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u162,axiom,
% 0.20/0.52      (![X4] : ((k1_xboole_0 = k7_subset_1(X4,X4,X4))))).
% 0.20/0.52  
% 0.20/0.52  tff(u161,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)))) | (k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u160,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u159,negated_conjecture,
% 0.20/0.52      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u158,axiom,
% 0.20/0.52      (![X1, X2] : ((k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2))))).
% 0.20/0.52  
% 0.20/0.52  tff(u157,axiom,
% 0.20/0.52      (![X1, X0] : ((k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u156,negated_conjecture,
% 0.20/0.52      ((~(k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1))) | (k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)))).
% 0.20/0.52  
% 0.20/0.52  tff(u155,axiom,
% 0.20/0.52      (![X0] : ((k2_subset_1(X0) = X0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u154,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u153,negated_conjecture,
% 0.20/0.52      ((~(sK1 = k3_xboole_0(sK1,u1_struct_0(sK0)))) | (sK1 = k3_xboole_0(sK1,u1_struct_0(sK0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u152,axiom,
% 0.20/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | (k1_xboole_0 = k7_subset_1(X0,X0,X1)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u151,axiom,
% 0.20/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u150,axiom,
% 0.20/0.52      (![X1, X0] : ((~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u149,axiom,
% 0.20/0.52      (![X0] : (r1_tarski(X0,X0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u148,negated_conjecture,
% 0.20/0.52      ((~r1_tarski(sK1,u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  tff(u147,axiom,
% 0.20/0.52      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 0.20/0.52  
% 0.20/0.52  tff(u146,axiom,
% 0.20/0.52      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 0.20/0.52  
% 0.20/0.52  tff(u145,negated_conjecture,
% 0.20/0.52      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.20/0.52  
% 0.20/0.52  tff(u144,axiom,
% 0.20/0.52      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 0.20/0.52  
% 0.20/0.52  % (24069)# SZS output end Saturation.
% 0.20/0.52  % (24069)------------------------------
% 0.20/0.52  % (24069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24069)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (24069)Memory used [KB]: 10746
% 0.20/0.52  % (24069)Time elapsed: 0.123 s
% 0.20/0.52  % (24069)------------------------------
% 0.20/0.52  % (24069)------------------------------
% 0.20/0.52  % (24064)Refutation not found, incomplete strategy% (24064)------------------------------
% 0.20/0.52  % (24064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24064)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24064)Memory used [KB]: 10618
% 0.20/0.52  % (24064)Time elapsed: 0.109 s
% 0.20/0.52  % (24064)------------------------------
% 0.20/0.52  % (24064)------------------------------
% 0.20/0.52  % (24049)Success in time 0.156 s
%------------------------------------------------------------------------------
