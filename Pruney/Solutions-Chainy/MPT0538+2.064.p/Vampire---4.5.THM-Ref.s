%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  52 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f26])).

fof(f26,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f15,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f24,f21])).

fof(f21,plain,(
    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK1) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( v1_relat_1(sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f24,plain,(
    ! [X0] : k8_relat_1(k1_xboole_0,sK1) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,sK1)) ),
    inference(resolution,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(k1_xboole_0,X1) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,X1)) ) ),
    inference(resolution,[],[f18,f16])).

fof(f16,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f15,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).

fof(f11,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

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
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:44:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (24281)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (24281)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    k1_xboole_0 != k1_xboole_0),
% 0.22/0.44    inference(superposition,[],[f15,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f24,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    k1_xboole_0 = k8_relat_1(k1_xboole_0,sK1)),
% 0.22/0.44    inference(resolution,[],[f17,f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    v1_relat_1(sK1) & ~v1_xboole_0(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0)) => (v1_relat_1(sK1) & ~v1_xboole_0(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0] : (k8_relat_1(k1_xboole_0,sK1) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,sK1))) )),
% 0.22/0.44    inference(resolution,[],[f22,f20])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(k1_xboole_0,X1) = k8_relat_1(X0,k8_relat_1(k1_xboole_0,X1))) )),
% 0.22/0.44    inference(resolution,[],[f18,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (24281)------------------------------
% 0.22/0.44  % (24281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (24281)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (24281)Memory used [KB]: 6012
% 0.22/0.44  % (24281)Time elapsed: 0.004 s
% 0.22/0.44  % (24281)------------------------------
% 0.22/0.44  % (24281)------------------------------
% 0.22/0.44  % (24276)Success in time 0.077 s
%------------------------------------------------------------------------------
