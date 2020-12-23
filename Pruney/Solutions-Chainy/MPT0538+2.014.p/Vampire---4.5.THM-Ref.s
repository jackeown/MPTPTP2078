%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  38 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f14,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f29,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(X0)) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f29,plain,(
    ! [X0] : k8_relat_1(X0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k6_relat_1(X0)) ),
    inference(resolution,[],[f28,f15])).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f28,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X3)
      | k8_relat_1(X2,X3) = k5_relat_1(X3,k6_relat_1(X2)) ) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f14,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (14691)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (14691)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    k1_xboole_0 != k1_xboole_0),
% 0.22/0.44    inference(superposition,[],[f14,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f29,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,k6_relat_1(X0))) )),
% 0.22/0.44    inference(resolution,[],[f18,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(X0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k6_relat_1(X0))) )),
% 0.22/0.44    inference(resolution,[],[f28,f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X2,X3] : (~v1_xboole_0(X3) | k8_relat_1(X2,X3) = k5_relat_1(X3,k6_relat_1(X2))) )),
% 0.22/0.44    inference(resolution,[],[f20,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,negated_conjecture,(
% 0.22/0.44    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.44    inference(negated_conjecture,[],[f6])).
% 0.22/0.44  fof(f6,conjecture,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (14691)------------------------------
% 0.22/0.44  % (14691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (14691)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (14691)Memory used [KB]: 6012
% 0.22/0.44  % (14691)Time elapsed: 0.005 s
% 0.22/0.44  % (14691)------------------------------
% 0.22/0.44  % (14691)------------------------------
% 0.22/0.44  % (14682)Success in time 0.077 s
%------------------------------------------------------------------------------
