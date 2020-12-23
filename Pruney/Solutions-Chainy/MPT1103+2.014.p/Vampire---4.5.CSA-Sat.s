%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:36 EST 2020

% Result     : CounterSatisfiable 5.63s
% Output     : Saturation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   71 (  71 expanded)
%              Number of leaves         :   71 (  71 expanded)
%              Depth                    :    0
%              Number of atoms          :   90 (  90 expanded)
%              Number of equality atoms :   75 (  75 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u961,negated_conjecture,
    ( ~ ( sK2 != k2_struct_0(sK1) )
    | sK2 != k2_struct_0(sK1) )).

tff(u960,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u959,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 )).

tff(u958,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

tff(u957,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) )).

tff(u956,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) )).

tff(u955,axiom,(
    ! [X3,X4] : k3_xboole_0(X4,X3) = k3_xboole_0(X3,k3_xboole_0(X4,X3)) )).

tff(u954,axiom,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(k3_xboole_0(X9,X10),X10) )).

tff(u953,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0) )).

tff(u952,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k2_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0) )).

tff(u951,axiom,(
    ! [X3,X2] : k3_xboole_0(X3,X2) = k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X3,X2)),k1_xboole_0) )).

tff(u950,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

tff(u949,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

tff(u948,axiom,(
    ! [X11,X10] : k3_xboole_0(k2_xboole_0(X10,X11),X10) = X10 )).

tff(u947,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u946,negated_conjecture,
    ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,u1_struct_0(sK1))
    | k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u945,axiom,(
    ! [X22,X23] : k4_xboole_0(X22,k3_xboole_0(X22,X23)) = k4_xboole_0(X22,X23) )).

tff(u944,axiom,(
    ! [X5,X4] : k4_xboole_0(X4,k3_xboole_0(X5,X4)) = k4_xboole_0(X4,X5) )).

tff(u943,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u942,axiom,(
    ! [X7,X8] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X8,X7)) )).

tff(u941,axiom,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) )).

tff(u940,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),sK2)
    | k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u939,axiom,(
    ! [X22,X23] : k4_xboole_0(k2_xboole_0(X22,X23),X22) = k5_xboole_0(k2_xboole_0(X22,X23),X22) )).

tff(u938,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u937,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u936,axiom,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 )).

tff(u935,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u934,axiom,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) )).

tff(u933,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

tff(u932,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u931,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u930,axiom,(
    ! [X3,X4] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X3),X3) )).

tff(u929,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u928,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,u1_struct_0(sK1))
    | k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u927,axiom,(
    ! [X3,X2] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) )).

tff(u926,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u925,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )).

tff(u924,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),sK2,sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2) )).

tff(u923,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 )).

tff(u922,axiom,(
    ! [X20,X21] : k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(X20,k3_xboole_0(X20,X21))) = X20 )).

tff(u921,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0 )).

tff(u920,axiom,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 )).

tff(u919,axiom,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 )).

tff(u918,axiom,(
    ! [X3,X2] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2 )).

tff(u917,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 )).

tff(u916,axiom,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 )).

tff(u915,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u914,axiom,(
    ! [X5,X6] : k2_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) = X5 )).

tff(u913,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

tff(u912,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))
    | k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) )).

tff(u911,axiom,(
    ! [X5,X4] : k2_xboole_0(k3_xboole_0(X4,X5),X4) = k5_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) )).

tff(u910,axiom,(
    ! [X5,X6] : k2_xboole_0(k3_xboole_0(X6,X5),X5) = k5_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) )).

tff(u909,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) )).

tff(u908,axiom,(
    ! [X20,X21] : k2_xboole_0(X20,X21) = k2_xboole_0(X20,k4_xboole_0(k2_xboole_0(X20,X21),X20)) )).

tff(u907,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u906,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u905,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u904,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u903,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2))
    | u1_struct_0(sK1) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2)) )).

tff(u902,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,u1_struct_0(sK1))
    | sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u901,negated_conjecture,
    ( sK2 != k3_xboole_0(u1_struct_0(sK1),sK2)
    | sK2 = k3_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u900,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u899,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u898,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u897,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u896,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u895,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u894,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u893,axiom,(
    ! [X1] : ~ sP0(k2_struct_0(X1),X1) )).

tff(u892,axiom,(
    ! [X1,X0] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ) )).

tff(u891,negated_conjecture,
    ( ~ sP0(sK2,sK1)
    | sP0(sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (28982)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.50  % (28990)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (28983)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (28999)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.51  % (28990)Refutation not found, incomplete strategy% (28990)------------------------------
% 0.22/0.51  % (28990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28978)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (28990)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28990)Memory used [KB]: 10618
% 0.22/0.52  % (28990)Time elapsed: 0.113 s
% 0.22/0.52  % (28990)------------------------------
% 0.22/0.52  % (28990)------------------------------
% 0.22/0.52  % (28994)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (29005)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (29009)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (28978)Refutation not found, incomplete strategy% (28978)------------------------------
% 0.22/0.53  % (28978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28978)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28978)Memory used [KB]: 1663
% 0.22/0.53  % (28978)Time elapsed: 0.105 s
% 0.22/0.53  % (28978)------------------------------
% 0.22/0.53  % (28978)------------------------------
% 0.22/0.53  % (28988)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (29003)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (28984)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (28985)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (29003)Refutation not found, incomplete strategy% (29003)------------------------------
% 0.22/0.53  % (29003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28995)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (28995)Refutation not found, incomplete strategy% (28995)------------------------------
% 0.22/0.53  % (28995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29002)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (29010)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (28991)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28995)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28995)Memory used [KB]: 6140
% 0.22/0.53  % (28995)Time elapsed: 0.003 s
% 0.22/0.53  % (28995)------------------------------
% 0.22/0.53  % (28995)------------------------------
% 0.22/0.53  % (29003)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29003)Memory used [KB]: 1791
% 0.22/0.53  % (29003)Time elapsed: 0.083 s
% 0.22/0.53  % (29003)------------------------------
% 0.22/0.53  % (29003)------------------------------
% 0.22/0.53  % (28988)Refutation not found, incomplete strategy% (28988)------------------------------
% 0.22/0.53  % (28988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28988)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28988)Memory used [KB]: 10618
% 0.22/0.53  % (28988)Time elapsed: 0.091 s
% 0.22/0.53  % (28988)------------------------------
% 0.22/0.53  % (28988)------------------------------
% 0.22/0.53  % (29001)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (28980)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (29007)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (29002)Refutation not found, incomplete strategy% (29002)------------------------------
% 0.22/0.54  % (29002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29002)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (29002)Memory used [KB]: 10746
% 0.22/0.54  % (29002)Time elapsed: 0.128 s
% 0.22/0.54  % (29002)------------------------------
% 0.22/0.54  % (29002)------------------------------
% 0.22/0.54  % (28979)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (28997)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (28997)Refutation not found, incomplete strategy% (28997)------------------------------
% 0.22/0.54  % (28997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28989)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (28992)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (28998)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (28997)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28997)Memory used [KB]: 10618
% 0.22/0.54  % (28997)Time elapsed: 0.137 s
% 0.22/0.54  % (28997)------------------------------
% 0.22/0.54  % (28997)------------------------------
% 0.22/0.54  % (29004)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (28989)Refutation not found, incomplete strategy% (28989)------------------------------
% 0.22/0.54  % (28989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28996)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (29000)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (28986)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (29000)Refutation not found, incomplete strategy% (29000)------------------------------
% 0.22/0.55  % (29000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (29000)Memory used [KB]: 10746
% 0.22/0.55  % (29000)Time elapsed: 0.143 s
% 0.22/0.55  % (29000)------------------------------
% 0.22/0.55  % (29000)------------------------------
% 0.22/0.55  % (28989)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28989)Memory used [KB]: 10618
% 0.22/0.55  % (28989)Time elapsed: 0.139 s
% 0.22/0.55  % (28989)------------------------------
% 0.22/0.55  % (28989)------------------------------
% 0.22/0.55  % (28987)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (28984)Refutation not found, incomplete strategy% (28984)------------------------------
% 0.22/0.56  % (28984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (28984)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (28984)Memory used [KB]: 6396
% 0.22/0.56  % (28984)Time elapsed: 0.147 s
% 0.22/0.56  % (28984)------------------------------
% 0.22/0.56  % (28984)------------------------------
% 0.22/0.57  % (29008)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (28986)Refutation not found, incomplete strategy% (28986)------------------------------
% 0.22/0.57  % (28986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (28986)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (28986)Memory used [KB]: 6524
% 1.66/0.58  % (28986)Time elapsed: 0.171 s
% 1.66/0.58  % (28986)------------------------------
% 1.66/0.58  % (28986)------------------------------
% 2.13/0.65  % (29104)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.13/0.65  % (29106)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.13/0.65  % (29109)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.13/0.66  % (29103)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.13/0.66  % (29098)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.13/0.66  % (29098)Refutation not found, incomplete strategy% (29098)------------------------------
% 2.13/0.66  % (29098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.66  % (29098)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.66  
% 2.13/0.66  % (29098)Memory used [KB]: 6140
% 2.13/0.66  % (29098)Time elapsed: 0.108 s
% 2.13/0.66  % (29098)------------------------------
% 2.13/0.66  % (29098)------------------------------
% 2.13/0.66  % (28979)Refutation not found, incomplete strategy% (28979)------------------------------
% 2.13/0.66  % (28979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (29118)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.13/0.67  % (28979)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.67  
% 2.13/0.67  % (28979)Memory used [KB]: 6268
% 2.13/0.67  % (28979)Time elapsed: 0.250 s
% 2.13/0.67  % (28979)------------------------------
% 2.13/0.67  % (28979)------------------------------
% 2.13/0.67  % (29106)Refutation not found, incomplete strategy% (29106)------------------------------
% 2.13/0.67  % (29106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (29120)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.13/0.67  % (29103)Refutation not found, incomplete strategy% (29103)------------------------------
% 2.13/0.67  % (29103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.67  % (29103)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.67  
% 2.13/0.67  % (29103)Memory used [KB]: 6396
% 2.13/0.67  % (29103)Time elapsed: 0.100 s
% 2.13/0.67  % (29103)------------------------------
% 2.13/0.67  % (29103)------------------------------
% 2.13/0.68  % (29106)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.68  
% 2.13/0.68  % (29106)Memory used [KB]: 10874
% 2.13/0.68  % (29106)Time elapsed: 0.111 s
% 2.13/0.68  % (29106)------------------------------
% 2.13/0.68  % (29106)------------------------------
% 2.13/0.68  % (29100)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.13/0.69  % (29123)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.13/0.69  % (29123)Refutation not found, incomplete strategy% (29123)------------------------------
% 2.13/0.69  % (29123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.69  % (29123)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.69  
% 2.13/0.69  % (29123)Memory used [KB]: 1791
% 2.13/0.69  % (29123)Time elapsed: 0.116 s
% 2.13/0.69  % (29123)------------------------------
% 2.13/0.69  % (29123)------------------------------
% 2.13/0.70  % (29126)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.68/0.71  % (29118)Refutation not found, incomplete strategy% (29118)------------------------------
% 2.68/0.71  % (29118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.71  % (29118)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.71  
% 2.68/0.71  % (29118)Memory used [KB]: 2046
% 2.68/0.71  % (29118)Time elapsed: 0.103 s
% 2.68/0.71  % (29118)------------------------------
% 2.68/0.71  % (29118)------------------------------
% 2.68/0.72  % (29135)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.08/0.79  % (29154)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.08/0.79  % (29162)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.08/0.82  % (29160)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.08/0.82  % (29160)Refutation not found, incomplete strategy% (29160)------------------------------
% 3.08/0.82  % (29160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.82  % (29160)Termination reason: Refutation not found, incomplete strategy
% 3.08/0.82  
% 3.08/0.82  % (29160)Memory used [KB]: 1663
% 3.08/0.82  % (29160)Time elapsed: 0.094 s
% 3.08/0.82  % (29160)------------------------------
% 3.08/0.82  % (29160)------------------------------
% 3.08/0.82  % (29100)Refutation not found, incomplete strategy% (29100)------------------------------
% 3.08/0.82  % (29100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.82  % (29100)Termination reason: Refutation not found, incomplete strategy
% 3.08/0.82  
% 3.08/0.82  % (29100)Memory used [KB]: 6140
% 3.08/0.82  % (29100)Time elapsed: 0.267 s
% 3.08/0.82  % (29100)------------------------------
% 3.08/0.82  % (29100)------------------------------
% 3.08/0.82  % (29158)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.08/0.82  % (29174)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.08/0.83  % (29165)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.04/0.93  % (28991)Time limit reached!
% 4.04/0.93  % (28991)------------------------------
% 4.04/0.93  % (28991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.93  % (28991)Termination reason: Time limit
% 4.04/0.93  
% 4.04/0.93  % (28991)Memory used [KB]: 10618
% 4.04/0.93  % (28991)Time elapsed: 0.523 s
% 4.04/0.93  % (28991)------------------------------
% 4.04/0.93  % (28991)------------------------------
% 4.04/0.93  % (29223)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.10/0.95  % (29224)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 4.10/0.96  % (29223)Refutation not found, incomplete strategy% (29223)------------------------------
% 4.10/0.96  % (29223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.96  % (29223)Termination reason: Refutation not found, incomplete strategy
% 4.10/0.96  
% 4.10/0.96  % (29223)Memory used [KB]: 6268
% 4.10/0.96  % (29223)Time elapsed: 0.100 s
% 4.10/0.96  % (29223)------------------------------
% 4.10/0.96  % (29223)------------------------------
% 4.10/0.96  % (29104)Time limit reached!
% 4.10/0.96  % (29104)------------------------------
% 4.10/0.96  % (29104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.97  % (29104)Termination reason: Time limit
% 4.10/0.97  % (29104)Termination phase: Saturation
% 4.10/0.97  
% 4.10/0.97  % (29104)Memory used [KB]: 7547
% 4.10/0.97  % (29104)Time elapsed: 0.400 s
% 4.10/0.97  % (29104)------------------------------
% 4.10/0.97  % (29104)------------------------------
% 4.10/0.98  % (29158)Refutation not found, incomplete strategy% (29158)------------------------------
% 4.10/0.98  % (29158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.98  % (29158)Termination reason: Refutation not found, incomplete strategy
% 4.10/0.98  
% 4.10/0.98  % (29158)Memory used [KB]: 1918
% 4.10/0.98  % (29158)Time elapsed: 0.256 s
% 4.10/0.98  % (29158)------------------------------
% 4.10/0.98  % (29158)------------------------------
% 4.61/1.03  % (28996)Time limit reached!
% 4.61/1.03  % (28996)------------------------------
% 4.61/1.03  % (28996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.04  % (28996)Termination reason: Time limit
% 4.61/1.04  
% 4.61/1.04  % (28996)Memory used [KB]: 15735
% 4.61/1.04  % (28996)Time elapsed: 0.628 s
% 4.61/1.04  % (28996)------------------------------
% 4.61/1.04  % (28996)------------------------------
% 4.61/1.04  % (29009)Time limit reached!
% 4.61/1.04  % (29009)------------------------------
% 4.61/1.04  % (29009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.04  % (29009)Termination reason: Time limit
% 4.61/1.04  % (29009)Termination phase: Saturation
% 4.61/1.04  
% 4.61/1.04  % (29009)Memory used [KB]: 8827
% 4.61/1.04  % (29009)Time elapsed: 0.600 s
% 4.61/1.04  % (29009)------------------------------
% 4.61/1.04  % (29009)------------------------------
% 4.61/1.06  % (29225)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 5.63/1.08  % (29226)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 5.63/1.10  % (29227)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 5.63/1.11  % SZS status CounterSatisfiable for theBenchmark
% 5.63/1.12  % (29228)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.63/1.13  % (29224)# SZS output start Saturation.
% 5.63/1.13  tff(u961,negated_conjecture,
% 5.63/1.13      ((~(sK2 != k2_struct_0(sK1))) | (sK2 != k2_struct_0(sK1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u960,axiom,
% 5.63/1.13      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u959,axiom,
% 5.63/1.13      (![X3, X2] : ((k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u958,axiom,
% 5.63/1.13      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2))))).
% 5.63/1.13  
% 5.63/1.13  tff(u957,axiom,
% 5.63/1.13      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2))))).
% 5.63/1.13  
% 5.63/1.13  tff(u956,axiom,
% 5.63/1.13      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u955,axiom,
% 5.63/1.13      (![X3, X4] : ((k3_xboole_0(X4,X3) = k3_xboole_0(X3,k3_xboole_0(X4,X3)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u954,axiom,
% 5.63/1.13      (![X9, X10] : ((k3_xboole_0(X9,X10) = k3_xboole_0(k3_xboole_0(X9,X10),X10))))).
% 5.63/1.13  
% 5.63/1.13  tff(u953,axiom,
% 5.63/1.13      (![X1, X0] : ((k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u952,axiom,
% 5.63/1.13      (![X1, X2] : ((k3_xboole_0(X1,X2) = k2_xboole_0(k3_xboole_0(X1,k3_xboole_0(X1,X2)),k1_xboole_0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u951,axiom,
% 5.63/1.13      (![X3, X2] : ((k3_xboole_0(X3,X2) = k2_xboole_0(k3_xboole_0(X2,k3_xboole_0(X3,X2)),k1_xboole_0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u950,axiom,
% 5.63/1.13      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u949,axiom,
% 5.63/1.13      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u948,axiom,
% 5.63/1.13      (![X11, X10] : ((k3_xboole_0(k2_xboole_0(X10,X11),X10) = X10)))).
% 5.63/1.13  
% 5.63/1.13  tff(u947,axiom,
% 5.63/1.13      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u946,negated_conjecture,
% 5.63/1.13      ((~(k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1)))) | (k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u945,axiom,
% 5.63/1.13      (![X22, X23] : ((k4_xboole_0(X22,k3_xboole_0(X22,X23)) = k4_xboole_0(X22,X23))))).
% 5.63/1.13  
% 5.63/1.13  tff(u944,axiom,
% 5.63/1.13      (![X5, X4] : ((k4_xboole_0(X4,k3_xboole_0(X5,X4)) = k4_xboole_0(X4,X5))))).
% 5.63/1.13  
% 5.63/1.13  tff(u943,axiom,
% 5.63/1.13      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u942,axiom,
% 5.63/1.13      (![X7, X8] : ((k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X8,X7)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u941,axiom,
% 5.63/1.13      (![X1] : ((k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u940,negated_conjecture,
% 5.63/1.13      ((~(k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2))) | (k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u939,axiom,
% 5.63/1.13      (![X22, X23] : ((k4_xboole_0(k2_xboole_0(X22,X23),X22) = k5_xboole_0(k2_xboole_0(X22,X23),X22))))).
% 5.63/1.13  
% 5.63/1.13  tff(u938,axiom,
% 5.63/1.13      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u937,axiom,
% 5.63/1.13      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u936,axiom,
% 5.63/1.13      (![X1] : ((k5_xboole_0(k1_xboole_0,X1) = X1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u935,axiom,
% 5.63/1.13      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u934,axiom,
% 5.63/1.13      (![X1] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u933,axiom,
% 5.63/1.13      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u932,axiom,
% 5.63/1.13      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u931,axiom,
% 5.63/1.13      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u930,axiom,
% 5.63/1.13      (![X3, X4] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X3),X3))))).
% 5.63/1.13  
% 5.63/1.13  tff(u929,axiom,
% 5.63/1.13      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u928,negated_conjecture,
% 5.63/1.13      ((~(k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1)))) | (k1_xboole_0 = k4_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u927,axiom,
% 5.63/1.13      (![X3, X2] : ((k1_xboole_0 = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u926,axiom,
% 5.63/1.13      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u925,negated_conjecture,
% 5.63/1.13      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u924,negated_conjecture,
% 5.63/1.13      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u923,axiom,
% 5.63/1.13      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u922,axiom,
% 5.63/1.13      (![X20, X21] : ((k2_xboole_0(k3_xboole_0(X20,X21),k4_xboole_0(X20,k3_xboole_0(X20,X21))) = X20)))).
% 5.63/1.13  
% 5.63/1.13  tff(u921,axiom,
% 5.63/1.13      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u920,axiom,
% 5.63/1.13      (![X0] : ((k2_xboole_0(k1_xboole_0,X0) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u919,axiom,
% 5.63/1.13      (![X2] : ((k2_xboole_0(X2,X2) = X2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u918,axiom,
% 5.63/1.13      (![X3, X2] : ((k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u917,axiom,
% 5.63/1.13      (![X1, X2] : ((k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u916,axiom,
% 5.63/1.13      (![X1] : ((k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u915,axiom,
% 5.63/1.13      (![X1] : ((k2_xboole_0(X1,k1_xboole_0) = X1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u914,axiom,
% 5.63/1.13      (![X5, X6] : ((k2_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) = X5)))).
% 5.63/1.13  
% 5.63/1.13  tff(u913,axiom,
% 5.63/1.13      (![X1, X0] : ((k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u912,negated_conjecture,
% 5.63/1.13      ((~(k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)))) | (k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))))).
% 5.63/1.13  
% 5.63/1.13  tff(u911,axiom,
% 5.63/1.13      (![X5, X4] : ((k2_xboole_0(k3_xboole_0(X4,X5),X4) = k5_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u910,axiom,
% 5.63/1.13      (![X5, X6] : ((k2_xboole_0(k3_xboole_0(X6,X5),X5) = k5_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u909,axiom,
% 5.63/1.13      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u908,axiom,
% 5.63/1.13      (![X20, X21] : ((k2_xboole_0(X20,X21) = k2_xboole_0(X20,k4_xboole_0(k2_xboole_0(X20,X21),X20)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u907,axiom,
% 5.63/1.13      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u906,axiom,
% 5.63/1.13      (![X0] : ((k2_subset_1(X0) = X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u905,negated_conjecture,
% 5.63/1.13      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u904,negated_conjecture,
% 5.63/1.13      ((~(u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2))) | (u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u903,negated_conjecture,
% 5.63/1.13      ((~(u1_struct_0(sK1) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2)))) | (u1_struct_0(sK1) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK1),sK2))))).
% 5.63/1.13  
% 5.63/1.13  tff(u902,negated_conjecture,
% 5.63/1.13      ((~(sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)))) | (sK2 = k3_xboole_0(sK2,u1_struct_0(sK1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u901,negated_conjecture,
% 5.63/1.13      ((~(sK2 = k3_xboole_0(u1_struct_0(sK1),sK2))) | (sK2 = k3_xboole_0(u1_struct_0(sK1),sK2)))).
% 5.63/1.13  
% 5.63/1.13  tff(u900,axiom,
% 5.63/1.13      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u899,negated_conjecture,
% 5.63/1.13      ((~r1_tarski(sK2,u1_struct_0(sK1))) | r1_tarski(sK2,u1_struct_0(sK1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u898,axiom,
% 5.63/1.13      (![X0] : (r1_tarski(X0,X0)))).
% 5.63/1.13  
% 5.63/1.13  tff(u897,axiom,
% 5.63/1.13      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u896,axiom,
% 5.63/1.13      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u895,negated_conjecture,
% 5.63/1.13      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 5.63/1.13  
% 5.63/1.13  tff(u894,axiom,
% 5.63/1.13      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 5.63/1.13  
% 5.63/1.13  tff(u893,axiom,
% 5.63/1.13      (![X1] : (~sP0(k2_struct_0(X1),X1)))).
% 5.63/1.13  
% 5.63/1.13  tff(u892,axiom,
% 5.63/1.13      (![X1, X0] : ((~sP0(X0,X1) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)))))).
% 5.63/1.13  
% 5.63/1.13  tff(u891,negated_conjecture,
% 5.63/1.13      ((~sP0(sK2,sK1)) | sP0(sK2,sK1))).
% 5.63/1.13  
% 5.63/1.13  % (29224)# SZS output end Saturation.
% 5.63/1.13  % (29224)------------------------------
% 5.63/1.13  % (29224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.13  % (29224)Termination reason: Satisfiable
% 5.63/1.13  
% 5.63/1.13  % (29224)Memory used [KB]: 6524
% 5.63/1.13  % (29224)Time elapsed: 0.256 s
% 5.63/1.13  % (29224)------------------------------
% 5.63/1.13  % (29224)------------------------------
% 5.63/1.13  % (28974)Success in time 0.766 s
%------------------------------------------------------------------------------
