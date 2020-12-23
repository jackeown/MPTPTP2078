%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  56 expanded)
%              Number of equality atoms :   28 (  30 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f21])).

fof(f21,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(subsumption_resolution,[],[f58,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f54,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f54,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f53,f23])).

fof(f23,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f16])).

fof(f16,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

fof(f53,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f52,f39])).

fof(f39,plain,(
    k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f52,plain,
    ( k3_relat_1(k1_xboole_0) = k3_tarski(k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f51,f46])).

fof(f46,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f32,f28])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f47,f26])).

fof(f26,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f47,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (7296)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (7296)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(resolution,[],[f59,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    v1_xboole_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    v1_xboole_0(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f58,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(superposition,[],[f54,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ~v1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f53,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,negated_conjecture,(
% 0.20/0.46    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(negated_conjecture,[],[f15])).
% 0.20/0.46  fof(f15,conjecture,(
% 0.20/0.46    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    k1_xboole_0 = k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(forward_demodulation,[],[f52,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0))),
% 0.20/0.46    inference(superposition,[],[f27,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    k3_relat_1(k1_xboole_0) = k3_tarski(k1_tarski(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(forward_demodulation,[],[f51,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(superposition,[],[f32,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(forward_demodulation,[],[f47,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,axiom,(
% 0.20/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(superposition,[],[f29,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (7296)------------------------------
% 0.20/0.46  % (7296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (7296)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (7296)Memory used [KB]: 1663
% 0.20/0.46  % (7296)Time elapsed: 0.053 s
% 0.20/0.46  % (7296)------------------------------
% 0.20/0.46  % (7296)------------------------------
% 0.20/0.46  % (7290)Success in time 0.105 s
%------------------------------------------------------------------------------
