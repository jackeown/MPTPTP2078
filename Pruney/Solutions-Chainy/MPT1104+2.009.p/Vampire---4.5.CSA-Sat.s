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
% DateTime   : Thu Dec  3 13:08:51 EST 2020

% Result     : CounterSatisfiable 1.59s
% Output     : Saturation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   80 (  80 expanded)
%              Number of leaves         :   80 (  80 expanded)
%              Depth                    :    0
%              Number of atoms          :  131 ( 131 expanded)
%              Number of equality atoms :  101 ( 101 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u833,negated_conjecture,
    ( ~ ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
    | sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u832,axiom,(
    ! [X1,X2] :
      ( k1_xboole_0 != k3_xboole_0(X2,X1)
      | r1_xboole_0(X1,X2) ) )).

tff(u831,axiom,(
    ! [X1,X0] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) )).

tff(u830,axiom,(
    ! [X5,X6] :
      ( k1_xboole_0 != X5
      | r1_xboole_0(X5,k3_tarski(k2_tarski(X6,X5))) ) )).

tff(u829,axiom,(
    ! [X1,X2] :
      ( k1_xboole_0 != X1
      | r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1) ) )).

tff(u828,axiom,(
    ! [X7,X6] :
      ( k1_xboole_0 != X6
      | r1_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6) ) )).

tff(u827,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) ) )).

tff(u826,axiom,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | r1_xboole_0(X1,X1) ) )).

tff(u825,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK2 )
    | k1_xboole_0 != sK2 )).

tff(u824,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK1 )
    | k1_xboole_0 != sK1 )).

tff(u823,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u822,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 )).

tff(u821,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0 )).

tff(u820,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u819,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u818,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

tff(u817,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

tff(u816,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK2,sK1)
    | k1_xboole_0 = k3_xboole_0(sK2,sK1) )).

tff(u815,axiom,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) )).

tff(u814,axiom,(
    ! [X10] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X10) )).

tff(u813,axiom,(
    ! [X0] : k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

tff(u812,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(sK1,sK1,k2_struct_0(sK0))
    | k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

tff(u811,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(sK2,sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) )).

tff(u810,axiom,(
    ! [X7,X6] : k1_xboole_0 = k7_subset_1(X6,X6,k3_tarski(k2_tarski(X6,X7))) )).

tff(u809,axiom,(
    ! [X9,X8] : k1_xboole_0 = k7_subset_1(X8,X8,k3_tarski(k2_tarski(X9,X8))) )).

tff(u808,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u807,axiom,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 )).

tff(u806,axiom,(
    ! [X3,X2] : k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) )).

tff(u805,axiom,(
    ! [X7,X6] : k5_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6) = k7_subset_1(k3_tarski(k2_tarski(X6,X7)),k3_tarski(k2_tarski(X6,X7)),X6) )).

tff(u804,axiom,(
    ! [X9,X8] : k5_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8) = k7_subset_1(k3_tarski(k2_tarski(X9,X8)),k3_tarski(k2_tarski(X9,X8)),X8) )).

tff(u803,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u802,axiom,(
    ! [X7] : k3_tarski(k2_tarski(X7,k1_xboole_0)) = X7 )).

tff(u801,axiom,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 )).

tff(u800,axiom,(
    ! [X1,X0] : k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) )).

tff(u799,axiom,(
    ! [X7,X6] : k3_tarski(k2_tarski(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6)) )).

tff(u798,axiom,(
    ! [X9,X8] : k3_tarski(k2_tarski(X9,X8)) = k5_xboole_0(X8,k5_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8)) )).

tff(u797,axiom,(
    ! [X5,X6] : k3_tarski(k2_tarski(X5,X6)) = k3_tarski(k2_tarski(X5,k3_tarski(k2_tarski(X5,X6)))) )).

tff(u796,axiom,(
    ! [X3,X4] : k3_tarski(k2_tarski(X4,X3)) = k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X4,X3)))) )).

tff(u795,axiom,(
    ! [X0] : k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 )).

tff(u794,negated_conjecture,
    ( k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u793,negated_conjecture,
    ( k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u792,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u791,axiom,(
    ! [X0] : k4_subset_1(X0,X0,X0) = X0 )).

tff(u790,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) )).

tff(u789,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) )).

tff(u788,axiom,(
    ! [X5] : k7_subset_1(X5,X5,k1_xboole_0) = X5 )).

tff(u787,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

tff(u786,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] : k7_subset_1(u1_struct_0(sK0),sK2,X1) = k7_subset_1(sK2,sK2,X1) )).

tff(u785,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2) )).

tff(u784,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u783,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u782,negated_conjecture,
    ( k2_struct_0(sK0) != k5_xboole_0(sK1,sK2)
    | k2_struct_0(sK0) = k5_xboole_0(sK1,sK2) )).

tff(u781,negated_conjecture,
    ( k2_struct_0(sK0) != k5_xboole_0(sK2,sK1)
    | k2_struct_0(sK0) = k5_xboole_0(sK2,sK1) )).

tff(u780,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,sK2))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)) )).

tff(u779,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK1,k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) )).

tff(u778,negated_conjecture,
    ( k2_struct_0(sK0) != k3_tarski(k2_tarski(sK2,k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) )).

tff(u777,negated_conjecture,
    ( sK1 != k3_xboole_0(sK1,k2_struct_0(sK0))
    | sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) )).

tff(u776,negated_conjecture,
    ( sK1 != k5_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u775,negated_conjecture,
    ( sK1 != k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

tff(u774,negated_conjecture,
    ( sK1 != k7_subset_1(sK1,sK1,sK2)
    | sK1 = k7_subset_1(sK1,sK1,sK2) )).

tff(u773,negated_conjecture,
    ( sK1 != k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)
    | sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

tff(u772,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,k2_struct_0(sK0))
    | sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) )).

tff(u771,negated_conjecture,
    ( sK2 != k5_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u770,negated_conjecture,
    ( sK2 != k4_subset_1(u1_struct_0(sK0),sK2,sK2)
    | sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

tff(u769,negated_conjecture,
    ( sK2 != k7_subset_1(sK2,sK2,sK1)
    | sK2 = k7_subset_1(sK2,sK2,sK1) )).

tff(u768,negated_conjecture,
    ( sK2 != k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

tff(u767,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 ) )).

tff(u766,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u765,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

tff(u764,axiom,(
    ! [X5] : r1_xboole_0(k1_xboole_0,X5) )).

tff(u763,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u762,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1) )).

tff(u761,axiom,(
    ! [X3,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k3_tarski(k2_tarski(X3,X2)) = k4_subset_1(X3,X3,X2) ) )).

tff(u760,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) ) )).

tff(u759,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) ) )).

tff(u758,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)) ) )).

tff(u757,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)) ) )).

tff(u756,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u755,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u754,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (5820)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (5820)Refutation not found, incomplete strategy% (5820)------------------------------
% 0.21/0.47  % (5820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5847)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.47  % (5820)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5820)Memory used [KB]: 10746
% 0.21/0.47  % (5820)Time elapsed: 0.072 s
% 0.21/0.47  % (5820)------------------------------
% 0.21/0.47  % (5820)------------------------------
% 0.21/0.48  % (5828)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (5828)Refutation not found, incomplete strategy% (5828)------------------------------
% 0.21/0.48  % (5828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (5828)Memory used [KB]: 10746
% 0.21/0.48  % (5828)Time elapsed: 0.081 s
% 0.21/0.48  % (5828)------------------------------
% 0.21/0.48  % (5828)------------------------------
% 0.21/0.51  % (5841)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (5845)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (5825)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (5821)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (5822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5818)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (5833)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (5833)Refutation not found, incomplete strategy% (5833)------------------------------
% 0.21/0.52  % (5833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5833)Memory used [KB]: 6140
% 0.21/0.52  % (5833)Time elapsed: 0.001 s
% 0.21/0.52  % (5833)------------------------------
% 0.21/0.52  % (5833)------------------------------
% 0.21/0.52  % (5818)Refutation not found, incomplete strategy% (5818)------------------------------
% 0.21/0.52  % (5818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5818)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5818)Memory used [KB]: 1791
% 0.21/0.52  % (5818)Time elapsed: 0.111 s
% 0.21/0.52  % (5818)------------------------------
% 0.21/0.52  % (5818)------------------------------
% 0.21/0.52  % (5822)Refutation not found, incomplete strategy% (5822)------------------------------
% 0.21/0.52  % (5822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5832)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (5822)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5822)Memory used [KB]: 6268
% 0.21/0.53  % (5822)Time elapsed: 0.116 s
% 0.21/0.53  % (5822)------------------------------
% 0.21/0.53  % (5822)------------------------------
% 0.21/0.53  % (5838)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (5824)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (5841)Refutation not found, incomplete strategy% (5841)------------------------------
% 0.21/0.54  % (5841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5841)Memory used [KB]: 1791
% 0.21/0.54  % (5841)Time elapsed: 0.094 s
% 0.21/0.54  % (5841)------------------------------
% 0.21/0.54  % (5841)------------------------------
% 0.21/0.54  % (5843)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5823)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (5840)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.54  % (5844)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.55  % (5819)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.55  % (5826)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.55  % (5834)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.55  % (5837)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (5839)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.55  % (5835)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.55  % (5836)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.55  % (5835)Refutation not found, incomplete strategy% (5835)------------------------------
% 1.39/0.55  % (5835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (5835)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (5835)Memory used [KB]: 10618
% 1.39/0.55  % (5835)Time elapsed: 0.147 s
% 1.39/0.55  % (5835)------------------------------
% 1.39/0.55  % (5835)------------------------------
% 1.39/0.55  % (5830)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (5829)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (5831)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.56  % (5829)Refutation not found, incomplete strategy% (5829)------------------------------
% 1.39/0.56  % (5829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (5838)Refutation not found, incomplete strategy% (5838)------------------------------
% 1.39/0.56  % (5838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (5838)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (5838)Memory used [KB]: 10746
% 1.39/0.56  % (5838)Time elapsed: 0.124 s
% 1.39/0.56  % (5838)------------------------------
% 1.39/0.56  % (5838)------------------------------
% 1.39/0.56  % (5826)Refutation not found, incomplete strategy% (5826)------------------------------
% 1.39/0.56  % (5826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (5846)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.59/0.56  % (5826)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (5826)Memory used [KB]: 10874
% 1.59/0.56  % (5826)Time elapsed: 0.152 s
% 1.59/0.56  % (5826)------------------------------
% 1.59/0.56  % (5826)------------------------------
% 1.59/0.56  % (5829)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.56  
% 1.59/0.56  % (5829)Memory used [KB]: 10746
% 1.59/0.56  % (5829)Time elapsed: 0.148 s
% 1.59/0.56  % (5829)------------------------------
% 1.59/0.56  % (5829)------------------------------
% 1.59/0.57  % (5842)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.57  % (5840)Refutation not found, incomplete strategy% (5840)------------------------------
% 1.59/0.57  % (5840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (5840)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (5840)Memory used [KB]: 10746
% 1.59/0.57  % (5840)Time elapsed: 0.139 s
% 1.59/0.57  % (5840)------------------------------
% 1.59/0.57  % (5840)------------------------------
% 1.59/0.57  % (5843)Refutation not found, incomplete strategy% (5843)------------------------------
% 1.59/0.57  % (5843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (5839)Refutation not found, incomplete strategy% (5839)------------------------------
% 1.59/0.57  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (5839)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (5839)Memory used [KB]: 1663
% 1.59/0.57  % (5839)Time elapsed: 0.136 s
% 1.59/0.57  % (5839)------------------------------
% 1.59/0.57  % (5839)------------------------------
% 1.59/0.57  % (5844)Refutation not found, incomplete strategy% (5844)------------------------------
% 1.59/0.57  % (5844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (5844)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (5844)Memory used [KB]: 10746
% 1.59/0.57  % (5844)Time elapsed: 0.139 s
% 1.59/0.57  % (5844)------------------------------
% 1.59/0.57  % (5844)------------------------------
% 1.59/0.57  % (5827)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.57  % (5843)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (5843)Memory used [KB]: 6396
% 1.59/0.57  % (5843)Time elapsed: 0.158 s
% 1.59/0.57  % (5843)------------------------------
% 1.59/0.57  % (5843)------------------------------
% 1.59/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.59/0.58  % (5834)# SZS output start Saturation.
% 1.59/0.58  tff(u833,negated_conjecture,
% 1.59/0.58      ((~(sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u832,axiom,
% 1.59/0.58      (![X1, X2] : (((k1_xboole_0 != k3_xboole_0(X2,X1)) | r1_xboole_0(X1,X2))))).
% 1.59/0.58  
% 1.59/0.58  tff(u831,axiom,
% 1.59/0.58      (![X1, X0] : (((k3_xboole_0(X0,X1) != k1_xboole_0) | r1_xboole_0(X0,X1))))).
% 1.59/0.58  
% 1.59/0.58  tff(u830,axiom,
% 1.59/0.58      (![X5, X6] : (((k1_xboole_0 != X5) | r1_xboole_0(X5,k3_tarski(k2_tarski(X6,X5))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u829,axiom,
% 1.59/0.58      (![X1, X2] : (((k1_xboole_0 != X1) | r1_xboole_0(k3_tarski(k2_tarski(X2,X1)),X1))))).
% 1.59/0.58  
% 1.59/0.58  tff(u828,axiom,
% 1.59/0.58      (![X7, X6] : (((k1_xboole_0 != X6) | r1_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6))))).
% 1.59/0.58  
% 1.59/0.58  tff(u827,axiom,
% 1.59/0.58      (![X1, X0] : (((k1_xboole_0 != X0) | r1_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u826,axiom,
% 1.59/0.58      (![X1] : (((k1_xboole_0 != X1) | r1_xboole_0(X1,X1))))).
% 1.59/0.58  
% 1.59/0.58  tff(u825,negated_conjecture,
% 1.59/0.58      ((~(k1_xboole_0 != sK2)) | (k1_xboole_0 != sK2))).
% 1.59/0.58  
% 1.59/0.58  tff(u824,negated_conjecture,
% 1.59/0.58      ((~(k1_xboole_0 != sK1)) | (k1_xboole_0 != sK1))).
% 1.59/0.58  
% 1.59/0.58  tff(u823,axiom,
% 1.59/0.58      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u822,axiom,
% 1.59/0.58      (![X1, X0] : ((k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u821,axiom,
% 1.59/0.58      (![X1, X0] : ((k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u820,axiom,
% 1.59/0.58      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u819,axiom,
% 1.59/0.58      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u818,axiom,
% 1.59/0.58      (![X0] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u817,negated_conjecture,
% 1.59/0.58      ((~(k1_xboole_0 = k3_xboole_0(sK1,sK2))) | (k1_xboole_0 = k3_xboole_0(sK1,sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u816,negated_conjecture,
% 1.59/0.58      ((~(k1_xboole_0 = k3_xboole_0(sK2,sK1))) | (k1_xboole_0 = k3_xboole_0(sK2,sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u815,axiom,
% 1.59/0.58      (![X1] : ((k1_xboole_0 = k5_xboole_0(X1,X1))))).
% 1.59/0.58  
% 1.59/0.58  tff(u814,axiom,
% 1.59/0.58      (![X10] : ((k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X10))))).
% 1.59/0.58  
% 1.59/0.58  tff(u813,axiom,
% 1.59/0.58      (![X0] : ((k1_xboole_0 = k7_subset_1(X0,X0,X0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u812,negated_conjecture,
% 1.59/0.58      ((~(k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0)))) | (k1_xboole_0 = k7_subset_1(sK1,sK1,k2_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u811,negated_conjecture,
% 1.59/0.58      ((~(k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0)))) | (k1_xboole_0 = k7_subset_1(sK2,sK2,k2_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u810,axiom,
% 1.59/0.58      (![X7, X6] : ((k1_xboole_0 = k7_subset_1(X6,X6,k3_tarski(k2_tarski(X6,X7))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u809,axiom,
% 1.59/0.58      (![X9, X8] : ((k1_xboole_0 = k7_subset_1(X8,X8,k3_tarski(k2_tarski(X9,X8))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u808,axiom,
% 1.59/0.58      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u807,axiom,
% 1.59/0.58      (![X0] : ((k5_xboole_0(k1_xboole_0,X0) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u806,axiom,
% 1.59/0.58      (![X3, X2] : ((k7_subset_1(X2,X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u805,axiom,
% 1.59/0.58      (![X7, X6] : ((k5_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6) = k7_subset_1(k3_tarski(k2_tarski(X6,X7)),k3_tarski(k2_tarski(X6,X7)),X6))))).
% 1.59/0.58  
% 1.59/0.58  tff(u804,axiom,
% 1.59/0.58      (![X9, X8] : ((k5_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8) = k7_subset_1(k3_tarski(k2_tarski(X9,X8)),k3_tarski(k2_tarski(X9,X8)),X8))))).
% 1.59/0.58  
% 1.59/0.58  tff(u803,axiom,
% 1.59/0.58      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u802,axiom,
% 1.59/0.58      (![X7] : ((k3_tarski(k2_tarski(X7,k1_xboole_0)) = X7)))).
% 1.59/0.58  
% 1.59/0.58  tff(u801,axiom,
% 1.59/0.58      (![X0] : ((k3_tarski(k2_tarski(X0,X0)) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u800,axiom,
% 1.59/0.58      (![X1, X0] : ((k3_tarski(k2_tarski(X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u799,axiom,
% 1.59/0.58      (![X7, X6] : ((k3_tarski(k2_tarski(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k3_tarski(k2_tarski(X6,X7)),X6)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u798,axiom,
% 1.59/0.58      (![X9, X8] : ((k3_tarski(k2_tarski(X9,X8)) = k5_xboole_0(X8,k5_xboole_0(k3_tarski(k2_tarski(X9,X8)),X8)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u797,axiom,
% 1.59/0.58      (![X5, X6] : ((k3_tarski(k2_tarski(X5,X6)) = k3_tarski(k2_tarski(X5,k3_tarski(k2_tarski(X5,X6)))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u796,axiom,
% 1.59/0.58      (![X3, X4] : ((k3_tarski(k2_tarski(X4,X3)) = k3_tarski(k2_tarski(X3,k3_tarski(k2_tarski(X4,X3)))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u795,axiom,
% 1.59/0.58      (![X0] : ((k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u794,negated_conjecture,
% 1.59/0.58      ((~(k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u793,negated_conjecture,
% 1.59/0.58      ((~(k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u792,axiom,
% 1.59/0.58      (![X0] : ((k2_subset_1(X0) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u791,axiom,
% 1.59/0.58      (![X0] : ((k4_subset_1(X0,X0,X0) = X0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u790,negated_conjecture,
% 1.59/0.58      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u789,negated_conjecture,
% 1.59/0.58      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u788,axiom,
% 1.59/0.58      (![X5] : ((k7_subset_1(X5,X5,k1_xboole_0) = X5)))).
% 1.59/0.58  
% 1.59/0.58  tff(u787,negated_conjecture,
% 1.59/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u786,negated_conjecture,
% 1.59/0.58      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((k7_subset_1(u1_struct_0(sK0),sK2,X1) = k7_subset_1(sK2,sK2,X1)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u785,axiom,
% 1.59/0.58      (![X1, X2] : ((k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k7_subset_1(X1,X1,X2))))).
% 1.59/0.58  
% 1.59/0.58  tff(u784,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u783,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u782,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k5_xboole_0(sK1,sK2))) | (k2_struct_0(sK0) = k5_xboole_0(sK1,sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u781,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k5_xboole_0(sK2,sK1))) | (k2_struct_0(sK0) = k5_xboole_0(sK2,sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u780,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2)))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,sK2))))).
% 1.59/0.58  
% 1.59/0.58  tff(u779,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u778,negated_conjecture,
% 1.59/0.58      ((~(k2_struct_0(sK0) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))))) | (k2_struct_0(sK0) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u777,negated_conjecture,
% 1.59/0.58      ((~(sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)))) | (sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u776,negated_conjecture,
% 1.59/0.58      ((~(sK1 = k5_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u775,negated_conjecture,
% 1.59/0.58      ((~(sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1))) | (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u774,negated_conjecture,
% 1.59/0.58      ((~(sK1 = k7_subset_1(sK1,sK1,sK2))) | (sK1 = k7_subset_1(sK1,sK1,sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u773,negated_conjecture,
% 1.59/0.58      ((~(sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2))) | (sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u772,negated_conjecture,
% 1.59/0.58      ((~(sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)))) | (sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u771,negated_conjecture,
% 1.59/0.58      ((~(sK2 = k5_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u770,negated_conjecture,
% 1.59/0.58      ((~(sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2))) | (sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)))).
% 1.59/0.58  
% 1.59/0.58  tff(u769,negated_conjecture,
% 1.59/0.58      ((~(sK2 = k7_subset_1(sK2,sK2,sK1))) | (sK2 = k7_subset_1(sK2,sK2,sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u768,negated_conjecture,
% 1.59/0.58      ((~(sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))) | (sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))).
% 1.59/0.58  
% 1.59/0.58  tff(u767,axiom,
% 1.59/0.58      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u766,axiom,
% 1.59/0.58      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u765,axiom,
% 1.59/0.58      (![X0] : (r1_xboole_0(X0,k1_xboole_0)))).
% 1.59/0.58  
% 1.59/0.58  tff(u764,axiom,
% 1.59/0.58      (![X5] : (r1_xboole_0(k1_xboole_0,X5)))).
% 1.59/0.58  
% 1.59/0.58  tff(u763,negated_conjecture,
% 1.59/0.58      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 1.59/0.58  
% 1.59/0.58  tff(u762,negated_conjecture,
% 1.59/0.58      ((~r1_xboole_0(sK2,sK1)) | r1_xboole_0(sK2,sK1))).
% 1.59/0.58  
% 1.59/0.58  tff(u761,axiom,
% 1.59/0.58      (![X3, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X3)) | (k3_tarski(k2_tarski(X3,X2)) = k4_subset_1(X3,X3,X2)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u760,axiom,
% 1.59/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)))))).
% 1.59/0.58  
% 1.59/0.58  tff(u759,axiom,
% 1.59/0.58      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u758,negated_conjecture,
% 1.59/0.58      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK2,X1) = k3_tarski(k2_tarski(sK2,X1)))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u757,negated_conjecture,
% 1.59/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0)))))))).
% 1.59/0.58  
% 1.59/0.58  tff(u756,negated_conjecture,
% 1.59/0.58      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u755,negated_conjecture,
% 1.59/0.58      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 1.59/0.58  
% 1.59/0.58  tff(u754,axiom,
% 1.59/0.58      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 1.59/0.58  
% 1.59/0.58  % (5834)# SZS output end Saturation.
% 1.59/0.58  % (5834)------------------------------
% 1.59/0.58  % (5834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (5834)Termination reason: Satisfiable
% 1.59/0.58  
% 1.59/0.58  % (5834)Memory used [KB]: 11129
% 1.59/0.58  % (5834)Time elapsed: 0.172 s
% 1.59/0.58  % (5834)------------------------------
% 1.59/0.58  % (5834)------------------------------
% 1.59/0.58  % (5827)Refutation not found, incomplete strategy% (5827)------------------------------
% 1.59/0.58  % (5827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (5827)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (5827)Memory used [KB]: 10746
% 1.59/0.58  % (5827)Time elapsed: 0.170 s
% 1.59/0.58  % (5827)------------------------------
% 1.59/0.58  % (5827)------------------------------
% 1.59/0.58  % (5816)Success in time 0.21 s
%------------------------------------------------------------------------------
