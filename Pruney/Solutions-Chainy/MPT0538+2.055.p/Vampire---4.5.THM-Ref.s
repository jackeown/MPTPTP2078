%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   28 (  30 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f30])).

fof(f30,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f10,f25])).

fof(f25,plain,(
    ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f24,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(X0)) ),
    inference(resolution,[],[f13,f12])).

fof(f12,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f24,plain,(
    ! [X2] : k8_relat_1(X2,k1_xboole_0) = k5_relat_1(k1_xboole_0,k6_relat_1(X2)) ),
    inference(resolution,[],[f15,f16])).

fof(f16,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f12,f11])).

fof(f11,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f10,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

% (13106)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
fof(f7,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:07:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (13104)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (13105)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (13097)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.43  % (13101)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (13097)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0),
% 0.22/0.43    inference(superposition,[],[f10,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X2] : (k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f24,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(X0))) )),
% 0.22/0.43    inference(resolution,[],[f13,f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X2] : (k8_relat_1(X2,k1_xboole_0) = k5_relat_1(k1_xboole_0,k6_relat_1(X2))) )),
% 0.22/0.43    inference(resolution,[],[f15,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    v1_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(superposition,[],[f12,f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  % (13106)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (13097)------------------------------
% 0.22/0.43  % (13097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (13097)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (13097)Memory used [KB]: 10490
% 0.22/0.43  % (13097)Time elapsed: 0.005 s
% 0.22/0.43  % (13097)------------------------------
% 0.22/0.43  % (13097)------------------------------
% 0.22/0.43  % (13096)Success in time 0.076 s
%------------------------------------------------------------------------------
