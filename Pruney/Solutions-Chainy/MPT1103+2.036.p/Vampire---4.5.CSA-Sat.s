%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:38 EST 2020

% Result     : CounterSatisfiable 6.58s
% Output     : Saturation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   80 (  80 expanded)
%              Number of leaves         :   80 (  80 expanded)
%              Depth                    :    0
%              Number of atoms          :  125 ( 125 expanded)
%              Number of equality atoms :   81 (  81 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u675,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | k1_xboole_0 != u1_struct_0(sK1) )).

tff(u674,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != sK2 )
    | u1_struct_0(sK1) != sK2 )).

tff(u673,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)) )
    | u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)) )).

tff(u672,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0) )
    | u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0) )).

tff(u671,negated_conjecture,
    ( ~ ( u1_struct_0(sK1) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) )
    | u1_struct_0(sK1) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) )).

tff(u670,negated_conjecture,
    ( ~ ( k2_struct_0(sK1) != sK2 )
    | k2_struct_0(sK1) != sK2 )).

tff(u669,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u668,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u667,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 )).

tff(u666,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u665,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )).

tff(u664,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

tff(u663,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))
    | k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) )).

tff(u662,axiom,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) )).

tff(u661,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u660,axiom,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 )).

tff(u659,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) )).

tff(u658,axiom,(
    ! [X3,X4] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) )).

tff(u657,negated_conjecture,
    ( k4_xboole_0(sK2,sK2) != k4_xboole_0(sK2,u1_struct_0(sK1))
    | k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u656,axiom,(
    ! [X3,X2] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),X2) )).

tff(u655,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u654,axiom,(
    ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) )).

tff(u653,axiom,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) )).

tff(u652,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) )).

tff(u651,negated_conjecture,
    ( k4_xboole_0(u1_struct_0(sK1),sK2) != k5_xboole_0(u1_struct_0(sK1),sK2)
    | k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u650,axiom,(
    ! [X3,X4] : k4_xboole_0(k4_xboole_0(X3,X4),X3) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) )).

tff(u649,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) )).

tff(u648,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | ! [X0] : k4_xboole_0(u1_struct_0(sK1),X0) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),X0))) )).

tff(u647,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u646,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u645,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u644,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u643,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )).

tff(u642,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),sK2,sK2)
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2) )).

tff(u641,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | ! [X0] : k1_xboole_0 = k7_subset_1(sK2,k1_xboole_0,X0) )).

tff(u640,axiom,(
    ! [X3,X4] : k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,X4) )).

tff(u639,axiom,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) )).

tff(u638,axiom,(
    ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) )).

tff(u637,axiom,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) )).

tff(u636,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = k4_xboole_0(sK2,sK2) )).

tff(u635,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u634,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u633,axiom,(
    ! [X1,X0,X2] : k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) )).

tff(u632,negated_conjecture,
    ( u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1)))
    | u1_struct_0(sK1) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1))) )).

tff(u631,negated_conjecture,
    ( u1_struct_0(sK1) != k2_xboole_0(u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2) )).

tff(u630,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))
    | sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) )).

tff(u629,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0)
    | sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0) )).

tff(u628,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2))
    | sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)) )).

tff(u627,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0)
    | sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0) )).

tff(u626,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,u1_struct_0(sK1))
    | sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)) )).

tff(u625,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u624,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) )).

tff(u623,axiom,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | k1_xboole_0 = X2 ) )).

tff(u622,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))
    | ~ r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)) )).

tff(u621,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | ! [X0] : ~ r1_tarski(u1_struct_0(sK1),k4_xboole_0(X0,u1_struct_0(sK1))) )).

tff(u620,negated_conjecture,
    ( ~ ~ r1_tarski(u1_struct_0(sK1),k1_xboole_0)
    | ~ r1_tarski(u1_struct_0(sK1),k1_xboole_0) )).

tff(u619,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u618,axiom,(
    ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) )).

tff(u617,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | r1_tarski(k1_xboole_0,sK2) )).

tff(u616,axiom,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) )).

tff(u615,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | r1_tarski(sK2,u1_struct_0(sK1)) )).

tff(u614,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) )).

tff(u613,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u612,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ l1_struct_0(X0) ) )).

tff(u611,negated_conjecture,
    ( ~ ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2))) )).

tff(u610,negated_conjecture,
    ( ~ ( k1_xboole_0 != u1_struct_0(sK1) )
    | ! [X0] : ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(X0,u1_struct_0(sK1)))) )).

tff(u609,negated_conjecture,
    ( ~ ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)) )).

tff(u608,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

tff(u607,axiom,(
    ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) )).

tff(u606,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) )).

tff(u605,axiom,(
    ! [X5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5)) )).

tff(u604,axiom,(
    ! [X1,X0] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

tff(u603,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) )).

tff(u602,axiom,(
    ! [X3] :
      ( ~ l1_struct_0(X3)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k1_xboole_0)) ) )).

tff(u601,axiom,(
    ! [X3,X4] :
      ( ~ l1_struct_0(X3)
      | k4_xboole_0(u1_struct_0(X3),X4) = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k4_xboole_0(u1_struct_0(X3),X4))) ) )).

tff(u600,axiom,(
    ! [X2] :
      ( ~ l1_struct_0(X2)
      | u1_struct_0(X2) = k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),u1_struct_0(X2))) ) )).

tff(u599,negated_conjecture,
    ( ~ l1_struct_0(sK1)
    | l1_struct_0(sK1) )).

tff(u598,axiom,(
    ! [X1] : ~ sP0(k2_struct_0(X1),X1) )).

tff(u597,axiom,(
    ! [X1,X0] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0) ) )).

tff(u596,negated_conjecture,
    ( ~ sP0(sK2,sK1)
    | sP0(sK2,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (20313)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.49  % (20305)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (20313)Refutation not found, incomplete strategy% (20313)------------------------------
% 0.22/0.51  % (20313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20313)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20313)Memory used [KB]: 10746
% 0.22/0.51  % (20313)Time elapsed: 0.095 s
% 0.22/0.51  % (20313)------------------------------
% 0.22/0.51  % (20313)------------------------------
% 0.22/0.51  % (20304)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (20304)Refutation not found, incomplete strategy% (20304)------------------------------
% 0.22/0.51  % (20304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20304)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20304)Memory used [KB]: 10618
% 0.22/0.51  % (20304)Time elapsed: 0.097 s
% 0.22/0.51  % (20304)------------------------------
% 0.22/0.51  % (20304)------------------------------
% 0.22/0.51  % (20295)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (20321)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (20298)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (20315)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (20312)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (20296)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (20307)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (20317)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (20294)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (20310)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (20308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (20303)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (20308)Refutation not found, incomplete strategy% (20308)------------------------------
% 0.22/0.53  % (20308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20308)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20308)Memory used [KB]: 6140
% 0.22/0.53  % (20308)Time elapsed: 0.002 s
% 0.22/0.53  % (20308)------------------------------
% 0.22/0.53  % (20308)------------------------------
% 0.22/0.54  % (20293)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20303)Refutation not found, incomplete strategy% (20303)------------------------------
% 0.22/0.54  % (20303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20303)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20303)Memory used [KB]: 10618
% 0.22/0.54  % (20303)Time elapsed: 0.124 s
% 0.22/0.54  % (20303)------------------------------
% 0.22/0.54  % (20303)------------------------------
% 0.22/0.54  % (20293)Refutation not found, incomplete strategy% (20293)------------------------------
% 0.22/0.54  % (20293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20293)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20293)Memory used [KB]: 1663
% 0.22/0.54  % (20293)Time elapsed: 0.126 s
% 0.22/0.54  % (20293)------------------------------
% 0.22/0.54  % (20293)------------------------------
% 0.22/0.54  % (20322)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (20299)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (20318)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (20297)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (20300)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (20297)Refutation not found, incomplete strategy% (20297)------------------------------
% 0.22/0.54  % (20297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20297)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20297)Memory used [KB]: 6268
% 0.22/0.54  % (20297)Time elapsed: 0.128 s
% 0.22/0.54  % (20297)------------------------------
% 0.22/0.54  % (20297)------------------------------
% 0.22/0.54  % (20309)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (20311)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (20300)Refutation not found, incomplete strategy% (20300)------------------------------
% 0.22/0.54  % (20300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20300)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20300)Memory used [KB]: 6396
% 0.22/0.54  % (20300)Time elapsed: 0.134 s
% 0.22/0.54  % (20300)------------------------------
% 0.22/0.54  % (20300)------------------------------
% 0.22/0.54  % (20302)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (20315)Refutation not found, incomplete strategy% (20315)------------------------------
% 0.22/0.54  % (20315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20315)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20315)Memory used [KB]: 10746
% 0.22/0.54  % (20315)Time elapsed: 0.108 s
% 0.22/0.54  % (20315)------------------------------
% 0.22/0.54  % (20315)------------------------------
% 0.22/0.55  % (20302)Refutation not found, incomplete strategy% (20302)------------------------------
% 0.22/0.55  % (20302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20302)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20302)Memory used [KB]: 10618
% 0.22/0.55  % (20302)Time elapsed: 0.139 s
% 0.22/0.55  % (20302)------------------------------
% 0.22/0.55  % (20302)------------------------------
% 0.22/0.55  % (20310)Refutation not found, incomplete strategy% (20310)------------------------------
% 0.22/0.55  % (20310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20310)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20310)Memory used [KB]: 10618
% 0.22/0.55  % (20310)Time elapsed: 0.138 s
% 0.22/0.55  % (20310)------------------------------
% 0.22/0.55  % (20310)------------------------------
% 0.22/0.55  % (20319)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (20301)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (20314)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (20316)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (20316)Refutation not found, incomplete strategy% (20316)------------------------------
% 0.22/0.55  % (20316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20316)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20316)Memory used [KB]: 1791
% 0.22/0.55  % (20316)Time elapsed: 0.122 s
% 0.22/0.55  % (20316)------------------------------
% 0.22/0.55  % (20316)------------------------------
% 0.22/0.56  % (20320)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (20306)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.02/0.62  % (20323)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.64  % (20323)Refutation not found, incomplete strategy% (20323)------------------------------
% 2.11/0.64  % (20323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.64  % (20323)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.64  
% 2.11/0.64  % (20323)Memory used [KB]: 6396
% 2.11/0.64  % (20323)Time elapsed: 0.025 s
% 2.11/0.64  % (20323)------------------------------
% 2.11/0.64  % (20323)------------------------------
% 2.11/0.65  % (20324)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.66  % (20326)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.67  % (20325)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.68  % (20329)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.11/0.68  % (20330)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.11/0.68  % (20327)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.11/0.68  % (20331)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.11/0.69  % (20331)Refutation not found, incomplete strategy% (20331)------------------------------
% 2.11/0.69  % (20331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.69  % (20331)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.69  
% 2.11/0.69  % (20331)Memory used [KB]: 1791
% 2.11/0.69  % (20331)Time elapsed: 0.111 s
% 2.11/0.69  % (20331)------------------------------
% 2.11/0.69  % (20331)------------------------------
% 2.11/0.69  % (20332)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.11/0.70  % (20328)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.11/0.70  % (20294)Refutation not found, incomplete strategy% (20294)------------------------------
% 2.11/0.70  % (20294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.70  % (20294)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.70  
% 2.11/0.70  % (20294)Memory used [KB]: 6396
% 2.11/0.70  % (20294)Time elapsed: 0.271 s
% 2.11/0.70  % (20294)------------------------------
% 2.11/0.70  % (20294)------------------------------
% 2.11/0.70  % (20329)Refutation not found, incomplete strategy% (20329)------------------------------
% 2.11/0.70  % (20329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.70  % (20329)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.70  
% 2.11/0.70  % (20329)Memory used [KB]: 1918
% 2.11/0.70  % (20329)Time elapsed: 0.135 s
% 2.11/0.70  % (20329)------------------------------
% 2.11/0.70  % (20329)------------------------------
% 2.75/0.74  % (20333)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.75/0.76  % (20334)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.19/0.81  % (20324)Refutation not found, incomplete strategy% (20324)------------------------------
% 3.19/0.81  % (20324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.81  % (20324)Termination reason: Refutation not found, incomplete strategy
% 3.19/0.81  
% 3.19/0.81  % (20324)Memory used [KB]: 6268
% 3.19/0.81  % (20324)Time elapsed: 0.249 s
% 3.19/0.81  % (20324)------------------------------
% 3.19/0.81  % (20324)------------------------------
% 3.19/0.82  % (20298)Time limit reached!
% 3.19/0.82  % (20298)------------------------------
% 3.19/0.82  % (20298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.82  % (20298)Termination reason: Time limit
% 3.19/0.82  
% 3.19/0.82  % (20298)Memory used [KB]: 8571
% 3.19/0.82  % (20298)Time elapsed: 0.416 s
% 3.19/0.82  % (20298)------------------------------
% 3.19/0.82  % (20298)------------------------------
% 3.19/0.83  % (20335)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.19/0.84  % (20336)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.19/0.84  % (20336)Refutation not found, incomplete strategy% (20336)------------------------------
% 3.19/0.84  % (20336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.84  % (20336)Termination reason: Refutation not found, incomplete strategy
% 3.19/0.84  
% 3.19/0.84  % (20336)Memory used [KB]: 1663
% 3.19/0.84  % (20336)Time elapsed: 0.116 s
% 3.19/0.84  % (20336)------------------------------
% 3.19/0.84  % (20336)------------------------------
% 3.19/0.86  % (20337)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.97/0.91  % (20305)Time limit reached!
% 3.97/0.91  % (20305)------------------------------
% 3.97/0.91  % (20305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.91  % (20305)Termination reason: Time limit
% 3.97/0.91  % (20305)Termination phase: Saturation
% 3.97/0.91  
% 3.97/0.91  % (20305)Memory used [KB]: 9978
% 3.97/0.91  % (20305)Time elapsed: 0.500 s
% 3.97/0.91  % (20305)------------------------------
% 3.97/0.91  % (20305)------------------------------
% 4.18/0.95  % (20338)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.18/0.95  % (20339)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.18/0.97  % (20326)Time limit reached!
% 4.18/0.97  % (20326)------------------------------
% 4.18/0.97  % (20326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.97  % (20326)Termination reason: Time limit
% 4.18/0.97  
% 4.18/0.97  % (20326)Memory used [KB]: 6780
% 4.18/0.97  % (20326)Time elapsed: 0.402 s
% 4.18/0.97  % (20326)------------------------------
% 4.18/0.97  % (20326)------------------------------
% 4.18/0.98  % (20340)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.18/0.98  % (20340)Refutation not found, incomplete strategy% (20340)------------------------------
% 4.18/0.98  % (20340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.98  % (20340)Termination reason: Refutation not found, incomplete strategy
% 4.18/0.98  
% 4.18/0.98  % (20340)Memory used [KB]: 6268
% 4.18/0.98  % (20340)Time elapsed: 0.111 s
% 4.18/0.98  % (20340)------------------------------
% 4.18/0.98  % (20340)------------------------------
% 4.18/0.98  % (20327)Time limit reached!
% 4.18/0.98  % (20327)------------------------------
% 4.18/0.98  % (20327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.98  % (20327)Termination reason: Time limit
% 4.18/0.98  % (20327)Termination phase: Saturation
% 4.18/0.98  
% 4.18/0.98  % (20327)Memory used [KB]: 12665
% 4.18/0.98  % (20327)Time elapsed: 0.421 s
% 4.18/0.98  % (20327)------------------------------
% 4.18/0.98  % (20327)------------------------------
% 4.18/0.99  % (20335)Refutation not found, incomplete strategy% (20335)------------------------------
% 4.18/0.99  % (20335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.99  % (20335)Termination reason: Refutation not found, incomplete strategy
% 4.18/0.99  
% 4.18/0.99  % (20335)Memory used [KB]: 1791
% 4.18/0.99  % (20335)Time elapsed: 0.261 s
% 4.18/0.99  % (20335)------------------------------
% 4.18/0.99  % (20335)------------------------------
% 4.74/1.01  % (20321)Time limit reached!
% 4.74/1.01  % (20321)------------------------------
% 4.74/1.01  % (20321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.01  % (20321)Termination reason: Time limit
% 4.74/1.01  % (20321)Termination phase: Saturation
% 4.74/1.01  
% 4.74/1.01  % (20321)Memory used [KB]: 8187
% 4.74/1.01  % (20321)Time elapsed: 0.600 s
% 4.74/1.01  % (20321)------------------------------
% 4.74/1.01  % (20321)------------------------------
% 4.74/1.03  % (20341)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 4.74/1.04  % (20309)Time limit reached!
% 4.74/1.04  % (20309)------------------------------
% 4.74/1.04  % (20309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.74/1.04  % (20309)Termination reason: Time limit
% 4.74/1.04  
% 4.74/1.04  % (20309)Memory used [KB]: 15095
% 4.74/1.04  % (20309)Time elapsed: 0.629 s
% 4.74/1.04  % (20309)------------------------------
% 4.74/1.04  % (20309)------------------------------
% 5.14/1.10  % (20342)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 5.14/1.10  % (20344)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 5.14/1.11  % (20343)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 5.14/1.13  % (20345)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.14/1.15  % (20346)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 6.40/1.18  % (20347)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 6.58/1.20  % SZS status CounterSatisfiable for theBenchmark
% 6.58/1.20  % (20341)# SZS output start Saturation.
% 6.58/1.20  tff(u675,negated_conjecture,
% 6.58/1.20      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (k1_xboole_0 != u1_struct_0(sK1)))).
% 6.58/1.20  
% 6.58/1.20  tff(u674,negated_conjecture,
% 6.58/1.20      ((~(u1_struct_0(sK1) != sK2)) | (u1_struct_0(sK1) != sK2))).
% 6.58/1.20  
% 6.58/1.20  tff(u673,negated_conjecture,
% 6.58/1.20      ((~(u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)))) | (u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2))))).
% 6.58/1.20  
% 6.58/1.20  tff(u672,negated_conjecture,
% 6.58/1.20      ((~(u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0))) | (u1_struct_0(sK1) != k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u671,negated_conjecture,
% 6.58/1.20      ((~(u1_struct_0(sK1) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) | (u1_struct_0(sK1) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))))).
% 6.58/1.20  
% 6.58/1.20  tff(u670,negated_conjecture,
% 6.58/1.20      ((~(k2_struct_0(sK1) != sK2)) | (k2_struct_0(sK1) != sK2))).
% 6.58/1.20  
% 6.58/1.20  tff(u669,axiom,
% 6.58/1.20      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u668,axiom,
% 6.58/1.20      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 6.58/1.20  
% 6.58/1.20  tff(u667,axiom,
% 6.58/1.20      (![X0] : ((k2_xboole_0(X0,X0) = X0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u666,axiom,
% 6.58/1.20      (![X1] : ((k2_xboole_0(X1,k1_xboole_0) = X1)))).
% 6.58/1.20  
% 6.58/1.20  tff(u665,axiom,
% 6.58/1.20      (![X1, X0] : ((k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u664,axiom,
% 6.58/1.20      (![X1, X0] : ((k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u663,negated_conjecture,
% 6.58/1.20      ((~(k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)))) | (k2_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))))).
% 6.58/1.20  
% 6.58/1.20  tff(u662,axiom,
% 6.58/1.20      (![X1] : ((k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1))))).
% 6.58/1.20  
% 6.58/1.20  tff(u661,axiom,
% 6.58/1.20      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u660,axiom,
% 6.58/1.20      (![X0] : ((k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u659,axiom,
% 6.58/1.20      (![X1, X0] : ((k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0))))).
% 6.58/1.20  
% 6.58/1.20  tff(u658,axiom,
% 6.58/1.20      (![X3, X4] : ((k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u657,negated_conjecture,
% 6.58/1.20      ((~(k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1)))) | (k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,u1_struct_0(sK1))))).
% 6.58/1.20  
% 6.58/1.20  tff(u656,axiom,
% 6.58/1.20      (![X3, X2] : ((k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X2,X3),X2))))).
% 6.58/1.20  
% 6.58/1.20  tff(u655,axiom,
% 6.58/1.20      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u654,axiom,
% 6.58/1.20      (![X3, X2] : ((k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u653,axiom,
% 6.58/1.20      (![X1] : ((k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1))))).
% 6.58/1.20  
% 6.58/1.20  tff(u652,axiom,
% 6.58/1.20      (![X1, X2] : ((k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u651,negated_conjecture,
% 6.58/1.20      ((~(k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2))) | (k4_xboole_0(u1_struct_0(sK1),sK2) = k5_xboole_0(u1_struct_0(sK1),sK2)))).
% 6.58/1.20  
% 6.58/1.20  tff(u650,axiom,
% 6.58/1.20      (![X3, X4] : ((k4_xboole_0(k4_xboole_0(X3,X4),X3) = k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u649,axiom,
% 6.58/1.20      (![X1, X0] : ((k4_xboole_0(X0,X1) = k6_subset_1(X0,X1))))).
% 6.58/1.20  
% 6.58/1.20  tff(u648,negated_conjecture,
% 6.58/1.20      ((~l1_struct_0(sK1)) | (![X0] : ((k4_xboole_0(u1_struct_0(sK1),X0) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),X0)))))))).
% 6.58/1.20  
% 6.58/1.20  tff(u647,axiom,
% 6.58/1.20      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 6.58/1.20  
% 6.58/1.20  tff(u646,axiom,
% 6.58/1.20      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 6.58/1.20  
% 6.58/1.20  tff(u645,axiom,
% 6.58/1.20      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 6.58/1.20  
% 6.58/1.20  tff(u644,axiom,
% 6.58/1.20      (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))))).
% 6.58/1.20  
% 6.58/1.20  tff(u643,negated_conjecture,
% 6.58/1.20      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))).
% 6.58/1.20  
% 6.58/1.20  tff(u642,negated_conjecture,
% 6.58/1.20      ((~(k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2))) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),sK2,sK2)))).
% 6.58/1.20  
% 6.58/1.20  tff(u641,negated_conjecture,
% 6.58/1.20      ((~(k1_xboole_0 = k4_xboole_0(sK2,sK2))) | (![X0] : ((k1_xboole_0 = k7_subset_1(sK2,k1_xboole_0,X0)))))).
% 6.58/1.20  
% 6.58/1.20  tff(u640,axiom,
% 6.58/1.20      (![X3, X4] : ((k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,X4))))).
% 6.58/1.20  
% 6.58/1.20  tff(u639,axiom,
% 6.58/1.20      (![X1] : ((k1_xboole_0 = k4_xboole_0(X1,X1))))).
% 6.58/1.20  
% 6.58/1.20  tff(u638,axiom,
% 6.58/1.20      (![X3, X2] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2))))).
% 6.58/1.20  
% 6.58/1.20  tff(u637,axiom,
% 6.58/1.20      (![X6] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6))))).
% 6.58/1.20  
% 6.58/1.21  tff(u636,negated_conjecture,
% 6.58/1.21      ((~(k1_xboole_0 = k4_xboole_0(sK2,sK2))) | (k1_xboole_0 = k4_xboole_0(sK2,sK2)))).
% 6.58/1.21  
% 6.58/1.21  tff(u635,axiom,
% 6.58/1.21      (![X0] : ((k2_subset_1(X0) = X0)))).
% 6.58/1.21  
% 6.58/1.21  tff(u634,negated_conjecture,
% 6.58/1.21      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 6.58/1.21  
% 6.58/1.21  tff(u633,axiom,
% 6.58/1.21      (![X1, X0, X2] : ((k7_subset_1(X0,k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2))))).
% 6.58/1.21  
% 6.58/1.21  tff(u632,negated_conjecture,
% 6.58/1.21      ((~(u1_struct_0(sK1) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1))))) | (u1_struct_0(sK1) = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),u1_struct_0(sK1)))))).
% 6.58/1.21  
% 6.58/1.21  tff(u631,negated_conjecture,
% 6.58/1.21      ((~(u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2))) | (u1_struct_0(sK1) = k2_xboole_0(u1_struct_0(sK1),sK2)))).
% 6.58/1.21  
% 6.58/1.21  tff(u630,negated_conjecture,
% 6.58/1.21      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)))) | (sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2))))).
% 6.58/1.21  
% 6.58/1.21  tff(u629,negated_conjecture,
% 6.58/1.21      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0))) | (sK2 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),k1_xboole_0)))).
% 6.58/1.21  
% 6.58/1.21  tff(u628,negated_conjecture,
% 6.58/1.21      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2)))) | (sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k4_xboole_0(sK2,sK2))))).
% 6.58/1.21  
% 6.58/1.21  tff(u627,negated_conjecture,
% 6.58/1.21      ((~(sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0))) | (sK2 = k7_subset_1(u1_struct_0(sK1),sK2,k1_xboole_0)))).
% 6.58/1.21  
% 6.58/1.21  tff(u626,negated_conjecture,
% 6.58/1.21      ((~(sK2 = k3_xboole_0(sK2,u1_struct_0(sK1)))) | (sK2 = k3_xboole_0(sK2,u1_struct_0(sK1))))).
% 6.58/1.21  
% 6.58/1.21  tff(u625,axiom,
% 6.58/1.21      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 6.58/1.21  
% 6.58/1.21  tff(u624,axiom,
% 6.58/1.21      (![X1, X0] : ((~r1_tarski(X0,k4_xboole_0(X1,X0)) | (k1_xboole_0 = X0))))).
% 6.58/1.21  
% 6.58/1.21  tff(u623,axiom,
% 6.58/1.21      (![X2] : ((~r1_tarski(X2,k1_xboole_0) | (k1_xboole_0 = X2))))).
% 6.58/1.21  
% 6.58/1.21  tff(u622,negated_conjecture,
% 6.58/1.21      ((~~r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2))) | ~r1_tarski(u1_struct_0(sK1),k4_xboole_0(sK2,sK2)))).
% 6.58/1.21  
% 6.58/1.21  tff(u621,negated_conjecture,
% 6.58/1.21      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (![X0] : (~r1_tarski(u1_struct_0(sK1),k4_xboole_0(X0,u1_struct_0(sK1))))))).
% 6.58/1.21  
% 6.58/1.21  tff(u620,negated_conjecture,
% 6.58/1.21      ((~~r1_tarski(u1_struct_0(sK1),k1_xboole_0)) | ~r1_tarski(u1_struct_0(sK1),k1_xboole_0))).
% 6.58/1.21  
% 6.58/1.21  tff(u619,axiom,
% 6.58/1.21      (![X0] : (r1_tarski(X0,X0)))).
% 6.58/1.21  
% 6.58/1.21  tff(u618,axiom,
% 6.58/1.21      (![X1, X0] : (r1_tarski(k4_xboole_0(X0,X1),X0)))).
% 6.58/1.21  
% 6.58/1.21  tff(u617,negated_conjecture,
% 6.58/1.21      ((~r1_tarski(k1_xboole_0,sK2)) | r1_tarski(k1_xboole_0,sK2))).
% 6.58/1.21  
% 6.58/1.21  tff(u616,axiom,
% 6.58/1.21      (![X6] : (r1_tarski(k1_xboole_0,X6)))).
% 6.58/1.21  
% 6.58/1.21  tff(u615,negated_conjecture,
% 6.58/1.21      ((~r1_tarski(sK2,u1_struct_0(sK1))) | r1_tarski(sK2,u1_struct_0(sK1)))).
% 6.58/1.21  
% 6.58/1.21  tff(u614,axiom,
% 6.58/1.21      (![X1, X0] : ((~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1))))).
% 6.58/1.21  
% 6.58/1.21  tff(u613,axiom,
% 6.58/1.21      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 6.58/1.21  
% 6.58/1.21  tff(u612,axiom,
% 6.58/1.21      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) | ~l1_struct_0(X0))))).
% 6.58/1.21  
% 6.58/1.21  tff(u611,negated_conjecture,
% 6.58/1.21      ((~~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(sK2,sK2))))).
% 6.58/1.21  
% 6.58/1.21  tff(u610,negated_conjecture,
% 6.58/1.21      ((~(k1_xboole_0 != u1_struct_0(sK1))) | (![X0] : (~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k4_xboole_0(X0,u1_struct_0(sK1)))))))).
% 6.58/1.21  
% 6.58/1.21  tff(u609,negated_conjecture,
% 6.58/1.21      ((~~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(k1_xboole_0)))).
% 6.58/1.21  
% 6.58/1.21  tff(u608,axiom,
% 6.58/1.21      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 6.58/1.21  
% 6.58/1.21  tff(u607,axiom,
% 6.58/1.21      (![X1, X0] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))))).
% 6.58/1.21  
% 6.58/1.21  tff(u606,negated_conjecture,
% 6.58/1.21      ((~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)))).
% 6.58/1.21  
% 6.58/1.21  tff(u605,axiom,
% 6.58/1.21      (![X5] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X5))))).
% 6.58/1.21  
% 6.58/1.21  tff(u604,axiom,
% 6.58/1.21      (![X1, X0] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))))).
% 6.58/1.21  
% 6.58/1.21  tff(u603,negated_conjecture,
% 6.58/1.21      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))).
% 6.58/1.21  
% 6.58/1.21  tff(u602,axiom,
% 6.58/1.21      (![X3] : ((~l1_struct_0(X3) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k1_xboole_0))))))).
% 6.58/1.21  
% 6.58/1.21  tff(u601,axiom,
% 6.58/1.21      (![X3, X4] : ((~l1_struct_0(X3) | (k4_xboole_0(u1_struct_0(X3),X4) = k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k7_subset_1(u1_struct_0(X3),k2_struct_0(X3),k4_xboole_0(u1_struct_0(X3),X4)))))))).
% 6.58/1.21  
% 6.58/1.21  tff(u600,axiom,
% 6.58/1.21      (![X2] : ((~l1_struct_0(X2) | (u1_struct_0(X2) = k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),k7_subset_1(u1_struct_0(X2),k2_struct_0(X2),u1_struct_0(X2)))))))).
% 6.58/1.21  
% 6.58/1.21  tff(u599,negated_conjecture,
% 6.58/1.21      ((~l1_struct_0(sK1)) | l1_struct_0(sK1))).
% 6.58/1.21  
% 6.58/1.21  tff(u598,axiom,
% 6.58/1.21      (![X1] : (~sP0(k2_struct_0(X1),X1)))).
% 6.58/1.21  
% 6.58/1.21  tff(u597,axiom,
% 6.58/1.21      (![X1, X0] : ((~sP0(X0,X1) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)))))).
% 6.58/1.21  
% 6.58/1.21  tff(u596,negated_conjecture,
% 6.58/1.21      ((~sP0(sK2,sK1)) | sP0(sK2,sK1))).
% 6.58/1.21  
% 6.58/1.21  % (20341)# SZS output end Saturation.
% 6.58/1.21  % (20341)------------------------------
% 6.58/1.21  % (20341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.58/1.21  % (20341)Termination reason: Satisfiable
% 6.58/1.21  
% 6.58/1.21  % (20341)Memory used [KB]: 6524
% 6.58/1.21  % (20341)Time elapsed: 0.204 s
% 6.58/1.21  % (20341)------------------------------
% 6.58/1.21  % (20341)------------------------------
% 6.58/1.21  % (20292)Success in time 0.837 s
%------------------------------------------------------------------------------
