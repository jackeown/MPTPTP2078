%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:31 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   35 (  43 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f39])).

fof(f39,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f16,f38])).

fof(f38,plain,(
    ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f37,f30])).

fof(f30,plain,(
    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f29,f19])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f29,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f28,f18])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f37,plain,(
    ! [X2] : k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f36,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X2] : k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(forward_demodulation,[],[f35,f18])).

fof(f35,plain,(
    ! [X2] : k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X2)) ),
    inference(resolution,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f16,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (29565)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.14/0.41  % (29563)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.14/0.42  % (29563)Refutation found. Thanks to Tanya!
% 0.14/0.42  % SZS status Theorem for theBenchmark
% 0.14/0.42  % SZS output start Proof for theBenchmark
% 0.14/0.42  fof(f40,plain,(
% 0.14/0.42    $false),
% 0.14/0.42    inference(trivial_inequality_removal,[],[f39])).
% 0.14/0.42  fof(f39,plain,(
% 0.14/0.42    k1_xboole_0 != k1_xboole_0),
% 0.14/0.42    inference(superposition,[],[f16,f38])).
% 0.14/0.42  fof(f38,plain,(
% 0.14/0.42    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) )),
% 0.14/0.42    inference(forward_demodulation,[],[f37,f30])).
% 0.14/0.42  fof(f30,plain,(
% 0.14/0.42    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.14/0.42    inference(forward_demodulation,[],[f29,f19])).
% 0.14/0.42  fof(f19,plain,(
% 0.14/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.14/0.42    inference(cnf_transformation,[],[f6])).
% 0.14/0.42  fof(f6,axiom,(
% 0.14/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.14/0.42  fof(f29,plain,(
% 0.14/0.42    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.14/0.42    inference(forward_demodulation,[],[f28,f18])).
% 0.14/0.42  fof(f18,plain,(
% 0.14/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.14/0.42    inference(cnf_transformation,[],[f6])).
% 0.14/0.42  fof(f28,plain,(
% 0.14/0.42    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.14/0.42    inference(resolution,[],[f22,f25])).
% 0.14/0.42  fof(f25,plain,(
% 0.14/0.42    v1_relat_1(k1_xboole_0)),
% 0.14/0.42    inference(superposition,[],[f20,f17])).
% 0.14/0.42  fof(f17,plain,(
% 0.14/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.14/0.42    inference(cnf_transformation,[],[f7])).
% 0.14/0.42  fof(f7,axiom,(
% 0.14/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.14/0.42  fof(f20,plain,(
% 0.14/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f3])).
% 0.14/0.42  fof(f3,axiom,(
% 0.14/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.14/0.42  fof(f22,plain,(
% 0.14/0.42    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f11])).
% 0.14/0.42  fof(f11,plain,(
% 0.14/0.42    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.14/0.42    inference(ennf_transformation,[],[f5])).
% 0.14/0.42  fof(f5,axiom,(
% 0.14/0.42    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.14/0.42  fof(f37,plain,(
% 0.14/0.42    ( ! [X2] : (k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)) )),
% 0.14/0.42    inference(forward_demodulation,[],[f36,f26])).
% 0.14/0.42  fof(f26,plain,(
% 0.14/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.14/0.42    inference(resolution,[],[f24,f21])).
% 0.14/0.42  fof(f21,plain,(
% 0.14/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.14/0.42    inference(cnf_transformation,[],[f2])).
% 0.14/0.42  fof(f2,axiom,(
% 0.14/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.14/0.42  fof(f24,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.14/0.42    inference(cnf_transformation,[],[f13])).
% 0.14/0.42  fof(f13,plain,(
% 0.14/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f1])).
% 0.14/0.42  fof(f1,axiom,(
% 0.14/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.14/0.42  fof(f36,plain,(
% 0.14/0.42    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 0.14/0.42    inference(forward_demodulation,[],[f35,f18])).
% 0.14/0.42  fof(f35,plain,(
% 0.14/0.42    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X2))) )),
% 0.14/0.42    inference(resolution,[],[f23,f25])).
% 0.14/0.42  fof(f23,plain,(
% 0.14/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.14/0.42    inference(cnf_transformation,[],[f12])).
% 0.14/0.42  fof(f12,plain,(
% 0.14/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.14/0.42    inference(ennf_transformation,[],[f4])).
% 0.14/0.42  fof(f4,axiom,(
% 0.14/0.42    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.14/0.42  fof(f16,plain,(
% 0.14/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.14/0.42    inference(cnf_transformation,[],[f15])).
% 0.14/0.42  fof(f15,plain,(
% 0.14/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.14/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.14/0.42  fof(f14,plain,(
% 0.14/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.14/0.42    introduced(choice_axiom,[])).
% 0.14/0.42  fof(f10,plain,(
% 0.14/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.14/0.42    inference(ennf_transformation,[],[f9])).
% 0.14/0.42  fof(f9,negated_conjecture,(
% 0.14/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.14/0.42    inference(negated_conjecture,[],[f8])).
% 0.14/0.42  fof(f8,conjecture,(
% 0.14/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.14/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.14/0.42  % SZS output end Proof for theBenchmark
% 0.14/0.42  % (29563)------------------------------
% 0.14/0.42  % (29563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.42  % (29563)Termination reason: Refutation
% 0.14/0.42  
% 0.14/0.42  % (29563)Memory used [KB]: 6012
% 0.14/0.42  % (29563)Time elapsed: 0.005 s
% 0.14/0.42  % (29563)------------------------------
% 0.14/0.42  % (29563)------------------------------
% 0.14/0.42  % (29555)Success in time 0.064 s
%------------------------------------------------------------------------------
