%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:44 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   35 (  58 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :   36 (  59 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f19,f145])).

fof(f145,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(backward_demodulation,[],[f54,f143])).

fof(f143,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k1_enumset1(X4,X5,X6),k2_tarski(X7,X8)) = k3_enumset1(X4,X5,X6,X7,X8) ),
    inference(forward_demodulation,[],[f141,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k3_enumset1(X4,X0,X1,X2,X3) ),
    inference(forward_demodulation,[],[f49,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f29,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f141,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k1_enumset1(X4,X5,X6),k2_tarski(X7,X8)) = k4_enumset1(X4,X5,X5,X6,X7,X8) ),
    inference(superposition,[],[f30,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X1,X2) ),
    inference(forward_demodulation,[],[f119,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f119,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X1,X2) ),
    inference(superposition,[],[f109,f26])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_enumset1(X2,X3,X0,X1) ),
    inference(backward_demodulation,[],[f45,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f104,f26])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f99,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f54,f51])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f28,f22])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f30,f25])).

fof(f19,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.38  ipcrm: permission denied for id (1214349313)
% 0.22/0.38  ipcrm: permission denied for id (1217921026)
% 0.22/0.38  ipcrm: permission denied for id (1217953795)
% 0.22/0.38  ipcrm: permission denied for id (1220804612)
% 0.22/0.38  ipcrm: permission denied for id (1218019333)
% 0.22/0.38  ipcrm: permission denied for id (1214513158)
% 0.22/0.38  ipcrm: permission denied for id (1218052103)
% 0.22/0.38  ipcrm: permission denied for id (1220902921)
% 0.22/0.38  ipcrm: permission denied for id (1220935690)
% 0.22/0.39  ipcrm: permission denied for id (1220968459)
% 0.22/0.39  ipcrm: permission denied for id (1218215948)
% 0.22/0.39  ipcrm: permission denied for id (1214709773)
% 0.22/0.39  ipcrm: permission denied for id (1214742542)
% 0.22/0.39  ipcrm: permission denied for id (1218248719)
% 0.22/0.39  ipcrm: permission denied for id (1218281488)
% 0.22/0.39  ipcrm: permission denied for id (1218347026)
% 0.22/0.39  ipcrm: permission denied for id (1218379795)
% 0.22/0.39  ipcrm: permission denied for id (1218445333)
% 0.22/0.40  ipcrm: permission denied for id (1214939158)
% 0.22/0.40  ipcrm: permission denied for id (1218478103)
% 0.22/0.40  ipcrm: permission denied for id (1218510872)
% 0.22/0.40  ipcrm: permission denied for id (1221066777)
% 0.22/0.40  ipcrm: permission denied for id (1215070234)
% 0.22/0.40  ipcrm: permission denied for id (1218576411)
% 0.22/0.40  ipcrm: permission denied for id (1215103004)
% 0.22/0.40  ipcrm: permission denied for id (1218609181)
% 0.22/0.40  ipcrm: permission denied for id (1221099550)
% 0.22/0.40  ipcrm: permission denied for id (1218674719)
% 0.22/0.40  ipcrm: permission denied for id (1215234080)
% 0.22/0.41  ipcrm: permission denied for id (1218707489)
% 0.22/0.41  ipcrm: permission denied for id (1218740258)
% 0.22/0.41  ipcrm: permission denied for id (1221165092)
% 0.22/0.41  ipcrm: permission denied for id (1215365158)
% 0.22/0.41  ipcrm: permission denied for id (1218871335)
% 0.22/0.41  ipcrm: permission denied for id (1218904104)
% 0.22/0.41  ipcrm: permission denied for id (1218936873)
% 0.22/0.41  ipcrm: permission denied for id (1218969642)
% 0.22/0.41  ipcrm: permission denied for id (1215463467)
% 0.22/0.42  ipcrm: permission denied for id (1221230636)
% 0.22/0.42  ipcrm: permission denied for id (1221263405)
% 0.22/0.42  ipcrm: permission denied for id (1215561774)
% 0.22/0.42  ipcrm: permission denied for id (1219133488)
% 0.22/0.42  ipcrm: permission denied for id (1221328945)
% 0.22/0.42  ipcrm: permission denied for id (1215692850)
% 0.22/0.42  ipcrm: permission denied for id (1215725619)
% 0.22/0.43  ipcrm: permission denied for id (1221427254)
% 0.22/0.43  ipcrm: permission denied for id (1215823927)
% 0.22/0.43  ipcrm: permission denied for id (1215856696)
% 0.22/0.43  ipcrm: permission denied for id (1219297337)
% 0.22/0.43  ipcrm: permission denied for id (1219330106)
% 0.22/0.43  ipcrm: permission denied for id (1215955003)
% 0.22/0.43  ipcrm: permission denied for id (1215987772)
% 0.22/0.43  ipcrm: permission denied for id (1221460029)
% 0.22/0.43  ipcrm: permission denied for id (1216020542)
% 0.22/0.44  ipcrm: permission denied for id (1216118849)
% 0.22/0.44  ipcrm: permission denied for id (1216151618)
% 0.22/0.44  ipcrm: permission denied for id (1216184387)
% 0.22/0.44  ipcrm: permission denied for id (1221558340)
% 0.22/0.44  ipcrm: permission denied for id (1216249925)
% 0.22/0.44  ipcrm: permission denied for id (1216282694)
% 0.22/0.44  ipcrm: permission denied for id (1216315463)
% 0.22/0.44  ipcrm: permission denied for id (1219526728)
% 0.22/0.44  ipcrm: permission denied for id (1219559497)
% 0.22/0.44  ipcrm: permission denied for id (1219625035)
% 0.22/0.45  ipcrm: permission denied for id (1216413772)
% 0.22/0.45  ipcrm: permission denied for id (1216446541)
% 0.22/0.45  ipcrm: permission denied for id (1221656655)
% 0.22/0.45  ipcrm: permission denied for id (1221689424)
% 0.22/0.45  ipcrm: permission denied for id (1216577617)
% 0.22/0.45  ipcrm: permission denied for id (1221722194)
% 0.22/0.45  ipcrm: permission denied for id (1216643155)
% 0.22/0.45  ipcrm: permission denied for id (1219788884)
% 0.22/0.45  ipcrm: permission denied for id (1221754965)
% 0.22/0.45  ipcrm: permission denied for id (1221787734)
% 0.22/0.46  ipcrm: permission denied for id (1219919960)
% 0.22/0.46  ipcrm: permission denied for id (1219952729)
% 0.22/0.46  ipcrm: permission denied for id (1219985498)
% 0.22/0.46  ipcrm: permission denied for id (1216872539)
% 0.22/0.46  ipcrm: permission denied for id (1221853276)
% 0.22/0.46  ipcrm: permission denied for id (1220083806)
% 0.22/0.46  ipcrm: permission denied for id (1216970847)
% 0.22/0.46  ipcrm: permission denied for id (1217003616)
% 0.22/0.46  ipcrm: permission denied for id (1220116577)
% 0.22/0.47  ipcrm: permission denied for id (1220149346)
% 0.22/0.47  ipcrm: permission denied for id (1220182115)
% 0.22/0.47  ipcrm: permission denied for id (1217101924)
% 0.22/0.47  ipcrm: permission denied for id (1221918821)
% 0.22/0.47  ipcrm: permission denied for id (1221951590)
% 0.22/0.47  ipcrm: permission denied for id (1220280423)
% 0.22/0.47  ipcrm: permission denied for id (1222017129)
% 0.22/0.47  ipcrm: permission denied for id (1222049898)
% 0.22/0.47  ipcrm: permission denied for id (1217298539)
% 0.22/0.47  ipcrm: permission denied for id (1217331308)
% 0.22/0.48  ipcrm: permission denied for id (1217364077)
% 0.22/0.48  ipcrm: permission denied for id (1217396846)
% 0.22/0.48  ipcrm: permission denied for id (1220411503)
% 0.22/0.48  ipcrm: permission denied for id (1222082672)
% 0.22/0.48  ipcrm: permission denied for id (1222115441)
% 0.22/0.48  ipcrm: permission denied for id (1217495154)
% 0.22/0.48  ipcrm: permission denied for id (1222148211)
% 0.22/0.48  ipcrm: permission denied for id (1222180980)
% 0.22/0.48  ipcrm: permission denied for id (1220608118)
% 0.22/0.48  ipcrm: permission denied for id (1217626231)
% 0.22/0.49  ipcrm: permission denied for id (1220640888)
% 0.22/0.49  ipcrm: permission denied for id (1217691769)
% 0.22/0.49  ipcrm: permission denied for id (1217724538)
% 0.22/0.49  ipcrm: permission denied for id (1217790076)
% 0.22/0.49  ipcrm: permission denied for id (1217822845)
% 0.22/0.49  ipcrm: permission denied for id (1220706430)
% 0.22/0.49  ipcrm: permission denied for id (1222279295)
% 0.99/0.60  % (18578)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.99/0.60  % (18569)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.99/0.61  % (18566)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.99/0.61  % (18575)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.99/0.61  % (18573)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.99/0.61  % (18579)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.99/0.61  % (18565)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.99/0.61  % (18576)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.99/0.61  % (18567)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.99/0.61  % (18570)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.99/0.61  % (18568)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.99/0.62  % (18565)Refutation found. Thanks to Tanya!
% 0.99/0.62  % SZS status Theorem for theBenchmark
% 0.99/0.62  % SZS output start Proof for theBenchmark
% 0.99/0.62  fof(f174,plain,(
% 0.99/0.62    $false),
% 0.99/0.62    inference(trivial_inequality_removal,[],[f173])).
% 0.99/0.62  fof(f173,plain,(
% 0.99/0.62    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 0.99/0.62    inference(superposition,[],[f19,f145])).
% 0.99/0.62  fof(f145,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.99/0.62    inference(backward_demodulation,[],[f54,f143])).
% 0.99/0.62  fof(f143,plain,(
% 0.99/0.62    ( ! [X6,X4,X8,X7,X5] : (k2_xboole_0(k1_enumset1(X4,X5,X6),k2_tarski(X7,X8)) = k3_enumset1(X4,X5,X6,X7,X8)) )),
% 0.99/0.62    inference(forward_demodulation,[],[f141,f51])).
% 0.99/0.62  fof(f51,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k3_enumset1(X4,X0,X1,X2,X3)) )),
% 0.99/0.62    inference(forward_demodulation,[],[f49,f27])).
% 0.99/0.62  fof(f27,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.99/0.62    inference(cnf_transformation,[],[f5])).
% 0.99/0.62  fof(f5,axiom,(
% 0.99/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.99/0.62  fof(f49,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X4,X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) )),
% 0.99/0.62    inference(superposition,[],[f29,f26])).
% 0.99/0.62  fof(f26,plain,(
% 0.99/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.99/0.62    inference(cnf_transformation,[],[f13])).
% 0.99/0.62  fof(f13,axiom,(
% 0.99/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.99/0.62  fof(f29,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.99/0.62    inference(cnf_transformation,[],[f7])).
% 0.99/0.62  fof(f7,axiom,(
% 0.99/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.99/0.62  fof(f141,plain,(
% 0.99/0.62    ( ! [X6,X4,X8,X7,X5] : (k2_xboole_0(k1_enumset1(X4,X5,X6),k2_tarski(X7,X8)) = k4_enumset1(X4,X5,X5,X6,X7,X8)) )),
% 0.99/0.62    inference(superposition,[],[f30,f128])).
% 0.99/0.62  fof(f128,plain,(
% 0.99/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X1,X2)) )),
% 0.99/0.62    inference(forward_demodulation,[],[f119,f25])).
% 0.99/0.62  fof(f25,plain,(
% 0.99/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.99/0.62    inference(cnf_transformation,[],[f12])).
% 0.99/0.62  fof(f12,axiom,(
% 0.99/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.99/0.62  fof(f119,plain,(
% 0.99/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X1,X2)) )),
% 0.99/0.62    inference(superposition,[],[f109,f26])).
% 0.99/0.62  fof(f109,plain,(
% 0.99/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_enumset1(X2,X3,X0,X1)) )),
% 0.99/0.62    inference(backward_demodulation,[],[f45,f105])).
% 0.99/0.62  fof(f105,plain,(
% 0.99/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.99/0.62    inference(forward_demodulation,[],[f104,f26])).
% 0.99/0.62  fof(f104,plain,(
% 0.99/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.99/0.62    inference(forward_demodulation,[],[f99,f22])).
% 0.99/0.62  fof(f22,plain,(
% 0.99/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.99/0.62    inference(cnf_transformation,[],[f11])).
% 0.99/0.62  fof(f11,axiom,(
% 0.99/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.99/0.62  fof(f99,plain,(
% 0.99/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X0,X1),k2_tarski(X2,X3))) )),
% 0.99/0.62    inference(superposition,[],[f54,f51])).
% 0.99/0.62  fof(f45,plain,(
% 0.99/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 0.99/0.62    inference(superposition,[],[f28,f22])).
% 0.99/0.62  fof(f28,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.99/0.62    inference(cnf_transformation,[],[f6])).
% 0.99/0.62  fof(f6,axiom,(
% 0.99/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.99/0.62  fof(f30,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 0.99/0.62    inference(cnf_transformation,[],[f8])).
% 0.99/0.62  fof(f8,axiom,(
% 0.99/0.62    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_enumset1)).
% 0.99/0.62  fof(f54,plain,(
% 0.99/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.99/0.62    inference(superposition,[],[f30,f25])).
% 0.99/0.62  fof(f19,plain,(
% 0.99/0.62    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.99/0.62    inference(cnf_transformation,[],[f18])).
% 0.99/0.62  fof(f18,plain,(
% 0.99/0.62    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.99/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 0.99/0.62  fof(f17,plain,(
% 0.99/0.62    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 0.99/0.62    introduced(choice_axiom,[])).
% 0.99/0.62  fof(f16,plain,(
% 0.99/0.62    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.99/0.62    inference(ennf_transformation,[],[f15])).
% 0.99/0.62  fof(f15,negated_conjecture,(
% 0.99/0.62    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.99/0.62    inference(negated_conjecture,[],[f14])).
% 0.99/0.62  fof(f14,conjecture,(
% 0.99/0.62    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.99/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.99/0.62  % SZS output end Proof for theBenchmark
% 0.99/0.62  % (18565)------------------------------
% 0.99/0.62  % (18565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.99/0.62  % (18565)Termination reason: Refutation
% 0.99/0.62  
% 0.99/0.62  % (18565)Memory used [KB]: 1663
% 0.99/0.62  % (18565)Time elapsed: 0.071 s
% 0.99/0.62  % (18565)------------------------------
% 0.99/0.62  % (18565)------------------------------
% 0.99/0.62  % (18571)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.99/0.62  % (18422)Success in time 0.249 s
%------------------------------------------------------------------------------
