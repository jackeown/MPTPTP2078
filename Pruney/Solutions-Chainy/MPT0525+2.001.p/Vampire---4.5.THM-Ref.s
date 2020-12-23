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
% DateTime   : Thu Dec  3 12:48:56 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   19 (  32 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  77 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f12])).

fof(f12,plain,(
    sK1 != k8_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k8_relat_1(X0,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f18,plain,(
    sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f17,f11])).

fof(f11,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | sK1 = k8_relat_1(X0,sK1) ) ),
    inference(forward_demodulation,[],[f16,f15])).

fof(f15,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0)) ),
    inference(resolution,[],[f13,f10])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f16,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | sK1 = k5_relat_1(sK1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f14,f10])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.37  ipcrm: permission denied for id (1224933376)
% 0.20/0.37  ipcrm: permission denied for id (1225752577)
% 0.20/0.37  ipcrm: permission denied for id (1229586435)
% 0.20/0.37  ipcrm: permission denied for id (1229651973)
% 0.20/0.37  ipcrm: permission denied for id (1224998918)
% 0.20/0.37  ipcrm: permission denied for id (1225916423)
% 0.20/0.38  ipcrm: permission denied for id (1226014730)
% 0.20/0.38  ipcrm: permission denied for id (1226047499)
% 0.20/0.38  ipcrm: permission denied for id (1229750284)
% 0.20/0.39  ipcrm: permission denied for id (1226276882)
% 0.20/0.39  ipcrm: permission denied for id (1225064468)
% 0.20/0.39  ipcrm: permission denied for id (1226342421)
% 0.20/0.39  ipcrm: permission denied for id (1225097238)
% 0.20/0.39  ipcrm: permission denied for id (1230012439)
% 0.20/0.40  ipcrm: permission denied for id (1230045208)
% 0.20/0.40  ipcrm: permission denied for id (1226440729)
% 0.20/0.40  ipcrm: permission denied for id (1230077978)
% 0.20/0.40  ipcrm: permission denied for id (1230110747)
% 0.20/0.40  ipcrm: permission denied for id (1230143516)
% 0.20/0.40  ipcrm: permission denied for id (1226571805)
% 0.20/0.40  ipcrm: permission denied for id (1230176286)
% 0.20/0.41  ipcrm: permission denied for id (1226670112)
% 0.20/0.41  ipcrm: permission denied for id (1225162786)
% 0.20/0.41  ipcrm: permission denied for id (1230274595)
% 0.20/0.41  ipcrm: permission denied for id (1226801189)
% 0.20/0.41  ipcrm: permission denied for id (1230372902)
% 0.20/0.41  ipcrm: permission denied for id (1226866727)
% 0.20/0.42  ipcrm: permission denied for id (1226965034)
% 0.20/0.42  ipcrm: permission denied for id (1227030572)
% 0.20/0.42  ipcrm: permission denied for id (1227063341)
% 0.20/0.42  ipcrm: permission denied for id (1227096110)
% 0.20/0.42  ipcrm: permission denied for id (1230503983)
% 0.20/0.42  ipcrm: permission denied for id (1227161648)
% 0.20/0.43  ipcrm: permission denied for id (1225228337)
% 0.20/0.43  ipcrm: permission denied for id (1227292725)
% 0.20/0.43  ipcrm: permission denied for id (1227325494)
% 0.20/0.43  ipcrm: permission denied for id (1227358263)
% 0.20/0.43  ipcrm: permission denied for id (1227391032)
% 0.20/0.44  ipcrm: permission denied for id (1230635065)
% 0.20/0.44  ipcrm: permission denied for id (1227456570)
% 0.20/0.44  ipcrm: permission denied for id (1227489339)
% 0.20/0.44  ipcrm: permission denied for id (1227522108)
% 0.20/0.44  ipcrm: permission denied for id (1230667837)
% 0.20/0.44  ipcrm: permission denied for id (1227587646)
% 0.20/0.44  ipcrm: permission denied for id (1230700607)
% 0.20/0.45  ipcrm: permission denied for id (1227685952)
% 0.20/0.45  ipcrm: permission denied for id (1227718721)
% 0.20/0.45  ipcrm: permission denied for id (1227751490)
% 0.20/0.45  ipcrm: permission denied for id (1230733379)
% 0.20/0.45  ipcrm: permission denied for id (1230766148)
% 0.20/0.45  ipcrm: permission denied for id (1230798917)
% 0.20/0.45  ipcrm: permission denied for id (1227882566)
% 0.20/0.45  ipcrm: permission denied for id (1227915335)
% 0.20/0.45  ipcrm: permission denied for id (1227948104)
% 0.20/0.46  ipcrm: permission denied for id (1227980873)
% 0.20/0.46  ipcrm: permission denied for id (1230831690)
% 0.20/0.46  ipcrm: permission denied for id (1225261131)
% 0.20/0.46  ipcrm: permission denied for id (1228111950)
% 0.20/0.46  ipcrm: permission denied for id (1225293904)
% 0.20/0.47  ipcrm: permission denied for id (1225359442)
% 0.20/0.47  ipcrm: permission denied for id (1230995539)
% 0.20/0.47  ipcrm: permission denied for id (1228275796)
% 0.20/0.47  ipcrm: permission denied for id (1228341334)
% 0.20/0.47  ipcrm: permission denied for id (1228374103)
% 0.20/0.48  ipcrm: permission denied for id (1228439641)
% 0.20/0.48  ipcrm: permission denied for id (1228472410)
% 0.20/0.48  ipcrm: permission denied for id (1228505179)
% 0.20/0.48  ipcrm: permission denied for id (1228537948)
% 0.20/0.48  ipcrm: permission denied for id (1225457758)
% 0.20/0.48  ipcrm: permission denied for id (1228603487)
% 0.20/0.48  ipcrm: permission denied for id (1228636256)
% 0.20/0.49  ipcrm: permission denied for id (1225490530)
% 0.20/0.49  ipcrm: permission denied for id (1228701795)
% 0.20/0.49  ipcrm: permission denied for id (1228734564)
% 0.20/0.49  ipcrm: permission denied for id (1228800102)
% 0.20/0.49  ipcrm: permission denied for id (1225556071)
% 0.20/0.49  ipcrm: permission denied for id (1228832872)
% 0.20/0.50  ipcrm: permission denied for id (1228865641)
% 0.20/0.50  ipcrm: permission denied for id (1228898410)
% 0.20/0.50  ipcrm: permission denied for id (1228931179)
% 0.20/0.50  ipcrm: permission denied for id (1228963948)
% 0.20/0.50  ipcrm: permission denied for id (1229029486)
% 0.20/0.50  ipcrm: permission denied for id (1229062255)
% 0.20/0.50  ipcrm: permission denied for id (1229095024)
% 0.20/0.51  ipcrm: permission denied for id (1229127793)
% 0.20/0.51  ipcrm: permission denied for id (1231224946)
% 0.20/0.51  ipcrm: permission denied for id (1225621619)
% 0.20/0.51  ipcrm: permission denied for id (1229193332)
% 0.20/0.51  ipcrm: permission denied for id (1229226101)
% 0.20/0.51  ipcrm: permission denied for id (1225654390)
% 0.20/0.51  ipcrm: permission denied for id (1231323255)
% 0.20/0.51  ipcrm: permission denied for id (1229291640)
% 0.20/0.52  ipcrm: permission denied for id (1229324409)
% 0.20/0.52  ipcrm: permission denied for id (1229357178)
% 0.20/0.52  ipcrm: permission denied for id (1231356028)
% 0.20/0.52  ipcrm: permission denied for id (1231388797)
% 0.20/0.52  ipcrm: permission denied for id (1229488254)
% 0.20/0.52  ipcrm: permission denied for id (1231421567)
% 0.73/0.59  % (27927)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.73/0.59  % (27921)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.73/0.59  % (27921)Refutation found. Thanks to Tanya!
% 0.73/0.59  % SZS status Theorem for theBenchmark
% 0.73/0.59  % SZS output start Proof for theBenchmark
% 0.73/0.59  fof(f19,plain,(
% 0.73/0.59    $false),
% 0.73/0.59    inference(subsumption_resolution,[],[f18,f12])).
% 0.73/0.59  fof(f12,plain,(
% 0.73/0.59    sK1 != k8_relat_1(sK0,sK1)),
% 0.73/0.59    inference(cnf_transformation,[],[f6])).
% 0.73/0.59  fof(f6,plain,(
% 0.73/0.59    ? [X0,X1] : (k8_relat_1(X0,X1) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.73/0.59    inference(flattening,[],[f5])).
% 0.73/0.59  fof(f5,plain,(
% 0.73/0.59    ? [X0,X1] : ((k8_relat_1(X0,X1) != X1 & r1_tarski(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.73/0.59    inference(ennf_transformation,[],[f4])).
% 0.73/0.59  fof(f4,negated_conjecture,(
% 0.73/0.59    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.73/0.59    inference(negated_conjecture,[],[f3])).
% 0.73/0.59  fof(f3,conjecture,(
% 0.73/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.73/0.59  fof(f18,plain,(
% 0.73/0.59    sK1 = k8_relat_1(sK0,sK1)),
% 0.73/0.59    inference(resolution,[],[f17,f11])).
% 0.73/0.59  fof(f11,plain,(
% 0.73/0.59    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.73/0.59    inference(cnf_transformation,[],[f6])).
% 0.73/0.59  fof(f17,plain,(
% 0.73/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | sK1 = k8_relat_1(X0,sK1)) )),
% 0.73/0.59    inference(forward_demodulation,[],[f16,f15])).
% 0.73/0.59  fof(f15,plain,(
% 0.73/0.59    ( ! [X0] : (k8_relat_1(X0,sK1) = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.73/0.59    inference(resolution,[],[f13,f10])).
% 0.73/0.59  fof(f10,plain,(
% 0.73/0.59    v1_relat_1(sK1)),
% 0.73/0.59    inference(cnf_transformation,[],[f6])).
% 0.73/0.59  fof(f13,plain,(
% 0.73/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.73/0.59    inference(cnf_transformation,[],[f7])).
% 0.73/0.59  fof(f7,plain,(
% 0.73/0.59    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.73/0.59    inference(ennf_transformation,[],[f1])).
% 0.73/0.59  fof(f1,axiom,(
% 0.73/0.59    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.73/0.59  fof(f16,plain,(
% 0.73/0.59    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | sK1 = k5_relat_1(sK1,k6_relat_1(X0))) )),
% 0.73/0.59    inference(resolution,[],[f14,f10])).
% 0.73/0.59  fof(f14,plain,(
% 0.73/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.73/0.59    inference(cnf_transformation,[],[f9])).
% 0.73/0.59  fof(f9,plain,(
% 0.73/0.59    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.73/0.59    inference(flattening,[],[f8])).
% 0.73/0.59  fof(f8,plain,(
% 0.73/0.59    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.73/0.59    inference(ennf_transformation,[],[f2])).
% 0.73/0.59  fof(f2,axiom,(
% 0.73/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.73/0.59  % SZS output end Proof for theBenchmark
% 0.73/0.59  % (27921)------------------------------
% 0.73/0.59  % (27921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.73/0.59  % (27921)Termination reason: Refutation
% 0.73/0.59  
% 0.73/0.59  % (27921)Memory used [KB]: 10490
% 0.73/0.59  % (27921)Time elapsed: 0.026 s
% 0.73/0.59  % (27921)------------------------------
% 0.73/0.59  % (27921)------------------------------
% 0.73/0.59  % (27783)Success in time 0.231 s
%------------------------------------------------------------------------------
