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
% DateTime   : Thu Dec  3 12:50:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  95 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(resolution,[],[f132,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f19,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f132,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f127,f24])).

fof(f24,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f127,plain,(
    ! [X9] : ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(sK0,X9)),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f28,f111])).

fof(f111,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f21,f15])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f28,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  ipcrm: permission denied for id (1211662336)
% 0.12/0.36  ipcrm: permission denied for id (1215496194)
% 0.12/0.36  ipcrm: permission denied for id (1215561732)
% 0.12/0.36  ipcrm: permission denied for id (1211858952)
% 0.12/0.37  ipcrm: permission denied for id (1211957259)
% 0.12/0.37  ipcrm: permission denied for id (1211990028)
% 0.12/0.37  ipcrm: permission denied for id (1212055567)
% 0.12/0.37  ipcrm: permission denied for id (1212088336)
% 0.12/0.37  ipcrm: permission denied for id (1212121105)
% 0.12/0.37  ipcrm: permission denied for id (1215823890)
% 0.12/0.38  ipcrm: permission denied for id (1212186643)
% 0.12/0.38  ipcrm: permission denied for id (1212219412)
% 0.12/0.38  ipcrm: permission denied for id (1215856661)
% 0.12/0.38  ipcrm: permission denied for id (1215889430)
% 0.12/0.38  ipcrm: permission denied for id (1212317719)
% 0.12/0.38  ipcrm: permission denied for id (1215954968)
% 0.12/0.38  ipcrm: permission denied for id (1212383257)
% 0.12/0.38  ipcrm: permission denied for id (1212416026)
% 0.12/0.38  ipcrm: permission denied for id (1212514331)
% 0.12/0.39  ipcrm: permission denied for id (1212481564)
% 0.12/0.39  ipcrm: permission denied for id (1212547101)
% 0.12/0.39  ipcrm: permission denied for id (1215987742)
% 0.12/0.39  ipcrm: permission denied for id (1216020511)
% 0.12/0.39  ipcrm: permission denied for id (1212678177)
% 0.12/0.39  ipcrm: permission denied for id (1216086050)
% 0.12/0.40  ipcrm: permission denied for id (1216151588)
% 0.12/0.40  ipcrm: permission denied for id (1216184357)
% 0.12/0.40  ipcrm: permission denied for id (1212809254)
% 0.19/0.40  ipcrm: permission denied for id (1216282665)
% 0.19/0.41  ipcrm: permission denied for id (1212973101)
% 0.19/0.41  ipcrm: permission denied for id (1216413742)
% 0.19/0.41  ipcrm: permission denied for id (1213038639)
% 0.19/0.41  ipcrm: permission denied for id (1213071408)
% 0.19/0.41  ipcrm: permission denied for id (1213104177)
% 0.19/0.41  ipcrm: permission denied for id (1213136946)
% 0.19/0.41  ipcrm: permission denied for id (1213169715)
% 0.19/0.42  ipcrm: permission denied for id (1216479285)
% 0.19/0.42  ipcrm: permission denied for id (1213268022)
% 0.19/0.42  ipcrm: permission denied for id (1213300791)
% 0.19/0.42  ipcrm: permission denied for id (1213333561)
% 0.19/0.42  ipcrm: permission denied for id (1213366330)
% 0.19/0.42  ipcrm: permission denied for id (1213431868)
% 0.19/0.42  ipcrm: permission denied for id (1216577597)
% 0.19/0.43  ipcrm: permission denied for id (1216610366)
% 0.19/0.43  ipcrm: permission denied for id (1213530175)
% 0.19/0.43  ipcrm: permission denied for id (1216643136)
% 0.19/0.43  ipcrm: permission denied for id (1213595713)
% 0.19/0.43  ipcrm: permission denied for id (1213661251)
% 0.19/0.43  ipcrm: permission denied for id (1213694020)
% 0.19/0.43  ipcrm: permission denied for id (1216708677)
% 0.19/0.44  ipcrm: permission denied for id (1216741446)
% 0.19/0.44  ipcrm: permission denied for id (1213792327)
% 0.19/0.44  ipcrm: permission denied for id (1213825096)
% 0.19/0.44  ipcrm: permission denied for id (1213857865)
% 0.19/0.44  ipcrm: permission denied for id (1216774218)
% 0.19/0.44  ipcrm: permission denied for id (1216806987)
% 0.19/0.44  ipcrm: permission denied for id (1213956172)
% 0.19/0.44  ipcrm: permission denied for id (1213988941)
% 0.19/0.45  ipcrm: permission denied for id (1214021710)
% 0.19/0.45  ipcrm: permission denied for id (1214054479)
% 0.19/0.45  ipcrm: permission denied for id (1214087251)
% 0.19/0.45  ipcrm: permission denied for id (1214120020)
% 0.19/0.45  ipcrm: permission denied for id (1214152790)
% 0.19/0.46  ipcrm: permission denied for id (1214185560)
% 0.19/0.46  ipcrm: permission denied for id (1217003609)
% 0.19/0.46  ipcrm: permission denied for id (1214218330)
% 0.19/0.46  ipcrm: permission denied for id (1214251099)
% 0.19/0.46  ipcrm: permission denied for id (1214283868)
% 0.19/0.47  ipcrm: permission denied for id (1214382175)
% 0.19/0.47  ipcrm: permission denied for id (1217101920)
% 0.19/0.47  ipcrm: permission denied for id (1214447713)
% 0.19/0.47  ipcrm: permission denied for id (1217200228)
% 0.19/0.47  ipcrm: permission denied for id (1214578789)
% 0.19/0.47  ipcrm: permission denied for id (1217232998)
% 0.19/0.47  ipcrm: permission denied for id (1214644327)
% 0.19/0.48  ipcrm: permission denied for id (1217265768)
% 0.19/0.48  ipcrm: permission denied for id (1214709865)
% 0.19/0.48  ipcrm: permission denied for id (1217298538)
% 0.19/0.48  ipcrm: permission denied for id (1217331307)
% 0.19/0.48  ipcrm: permission denied for id (1214808172)
% 0.19/0.48  ipcrm: permission denied for id (1217364077)
% 0.19/0.49  ipcrm: permission denied for id (1214939248)
% 0.19/0.49  ipcrm: permission denied for id (1214972017)
% 0.19/0.49  ipcrm: permission denied for id (1215004786)
% 0.19/0.49  ipcrm: permission denied for id (1217462387)
% 0.19/0.49  ipcrm: permission denied for id (1215070324)
% 0.19/0.49  ipcrm: permission denied for id (1215103093)
% 0.19/0.49  ipcrm: permission denied for id (1215135862)
% 0.19/0.49  ipcrm: permission denied for id (1215168631)
% 0.19/0.49  ipcrm: permission denied for id (1215201400)
% 0.19/0.50  ipcrm: permission denied for id (1215299707)
% 0.19/0.50  ipcrm: permission denied for id (1215332476)
% 0.19/0.50  ipcrm: permission denied for id (1217560701)
% 0.19/0.50  ipcrm: permission denied for id (1217593470)
% 0.19/0.50  ipcrm: permission denied for id (1215430783)
% 0.19/0.56  % (8643)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.19/0.57  % (8645)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.57  % (8641)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.57  % (8647)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.19/0.57  % (8640)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.58  % (8638)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.19/0.58  % (8640)Refutation found. Thanks to Tanya!
% 0.19/0.58  % SZS status Theorem for theBenchmark
% 0.19/0.58  % SZS output start Proof for theBenchmark
% 0.19/0.58  fof(f137,plain,(
% 0.19/0.58    $false),
% 0.19/0.58    inference(resolution,[],[f132,f23])).
% 0.19/0.58  fof(f23,plain,(
% 0.19/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.19/0.58    inference(superposition,[],[f19,f18])).
% 0.19/0.58  fof(f18,plain,(
% 0.19/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.58    inference(cnf_transformation,[],[f4])).
% 0.19/0.58  fof(f4,axiom,(
% 0.19/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.58  fof(f19,plain,(
% 0.19/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f3])).
% 0.19/0.58  fof(f3,axiom,(
% 0.19/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.58  fof(f132,plain,(
% 0.19/0.58    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1))),
% 0.19/0.58    inference(superposition,[],[f127,f24])).
% 0.19/0.58  fof(f24,plain,(
% 0.19/0.58    sK1 = k2_xboole_0(sK0,sK1)),
% 0.19/0.58    inference(resolution,[],[f20,f16])).
% 0.19/0.58  fof(f16,plain,(
% 0.19/0.58    r1_tarski(sK0,sK1)),
% 0.19/0.58    inference(cnf_transformation,[],[f14])).
% 0.19/0.58  fof(f14,plain,(
% 0.19/0.58    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.19/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.19/0.58  fof(f13,plain,(
% 0.19/0.58    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.19/0.58    introduced(choice_axiom,[])).
% 0.19/0.58  fof(f9,plain,(
% 0.19/0.58    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.19/0.58    inference(flattening,[],[f8])).
% 0.19/0.58  fof(f8,plain,(
% 0.19/0.58    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.19/0.58    inference(ennf_transformation,[],[f7])).
% 0.19/0.58  fof(f7,negated_conjecture,(
% 0.19/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.58    inference(negated_conjecture,[],[f6])).
% 0.19/0.58  fof(f6,conjecture,(
% 0.19/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.19/0.58  fof(f20,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.58    inference(cnf_transformation,[],[f10])).
% 0.19/0.58  fof(f10,plain,(
% 0.19/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.58    inference(ennf_transformation,[],[f2])).
% 0.19/0.58  fof(f2,axiom,(
% 0.19/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.58  fof(f127,plain,(
% 0.19/0.58    ( ! [X9] : (~r1_tarski(k10_relat_1(sK2,k2_xboole_0(sK0,X9)),k10_relat_1(sK2,sK1))) )),
% 0.19/0.58    inference(superposition,[],[f28,f111])).
% 0.19/0.58  fof(f111,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 0.19/0.58    inference(resolution,[],[f21,f15])).
% 0.19/0.58  fof(f15,plain,(
% 0.19/0.58    v1_relat_1(sK2)),
% 0.19/0.58    inference(cnf_transformation,[],[f14])).
% 0.19/0.58  fof(f21,plain,(
% 0.19/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.19/0.58    inference(cnf_transformation,[],[f11])).
% 0.19/0.58  fof(f11,plain,(
% 0.19/0.58    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.19/0.58    inference(ennf_transformation,[],[f5])).
% 0.19/0.58  fof(f5,axiom,(
% 0.19/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.19/0.58  fof(f28,plain,(
% 0.19/0.58    ( ! [X0] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))) )),
% 0.19/0.58    inference(resolution,[],[f22,f17])).
% 0.19/0.58  fof(f17,plain,(
% 0.19/0.58    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.58    inference(cnf_transformation,[],[f14])).
% 0.19/0.58  fof(f22,plain,(
% 0.19/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f12])).
% 0.19/0.58  fof(f12,plain,(
% 0.19/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.19/0.58    inference(ennf_transformation,[],[f1])).
% 0.19/0.58  fof(f1,axiom,(
% 0.19/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.19/0.58  % SZS output end Proof for theBenchmark
% 0.19/0.58  % (8640)------------------------------
% 0.19/0.58  % (8640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (8640)Termination reason: Refutation
% 0.19/0.58  
% 0.19/0.58  % (8640)Memory used [KB]: 6140
% 0.19/0.58  % (8640)Time elapsed: 0.007 s
% 0.19/0.58  % (8640)------------------------------
% 0.19/0.58  % (8640)------------------------------
% 0.19/0.58  % (8501)Success in time 0.236 s
%------------------------------------------------------------------------------
