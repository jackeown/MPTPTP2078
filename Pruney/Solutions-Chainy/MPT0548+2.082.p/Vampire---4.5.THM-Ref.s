%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  49 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f15,f35])).

fof(f35,plain,(
    ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f34,f18])).

fof(f18,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f34,plain,(
    ! [X2] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f33,f31])).

fof(f31,plain,(
    ! [X2] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f30,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k5_relat_1(k6_relat_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f30,plain,(
    ! [X2] : k7_relat_1(k1_xboole_0,X2) = k5_relat_1(k6_relat_1(X2),k1_xboole_0) ),
    inference(resolution,[],[f22,f24])).

fof(f24,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f19,f16])).

fof(f16,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f33,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(k1_xboole_0,X2)) = k9_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (11266)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (11271)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.43  % (11269)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (11271)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f15,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f34,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f33,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f30,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k6_relat_1(X0),k1_xboole_0)) )),
% 0.20/0.43    inference(resolution,[],[f21,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2] : (k7_relat_1(k1_xboole_0,X2) = k5_relat_1(k6_relat_1(X2),k1_xboole_0)) )),
% 0.20/0.43    inference(resolution,[],[f22,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(superposition,[],[f19,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X2] : (k2_relat_1(k7_relat_1(k1_xboole_0,X2)) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.20/0.43    inference(resolution,[],[f23,f24])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (11271)------------------------------
% 0.20/0.43  % (11271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (11271)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (11271)Memory used [KB]: 10490
% 0.20/0.43  % (11271)Time elapsed: 0.005 s
% 0.20/0.43  % (11271)------------------------------
% 0.20/0.43  % (11271)------------------------------
% 0.20/0.43  % (11259)Success in time 0.077 s
%------------------------------------------------------------------------------
