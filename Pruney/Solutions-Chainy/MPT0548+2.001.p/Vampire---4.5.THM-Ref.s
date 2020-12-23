%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   64 (  85 expanded)
%              Number of equality atoms :   47 (  60 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f76,f72])).

fof(f72,plain,(
    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f71,f29])).

fof(f29,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f71,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f70,f28])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f45,f27])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(resolution,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f76,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f75,f65])).

fof(f65,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f61,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f61,plain,(
    ! [X2] : k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f59,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f58,f48])).

fof(f48,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f47,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f46,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f38,f30])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f38,f57])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f56,f32])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f75,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f74,f28])).

fof(f74,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X0)) ),
    inference(resolution,[],[f73,f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f40,f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f26,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f24])).

fof(f24,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:29:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (20977)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.44  % (20977)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f26,f77])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f76,f72])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.44    inference(forward_demodulation,[],[f71,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,axiom,(
% 0.22/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.22/0.44    inference(forward_demodulation,[],[f70,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 0.22/0.44    inference(resolution,[],[f45,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    v1_xboole_0(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.44    inference(resolution,[],[f34,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f75,f65])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f61,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ( ! [X2] : (k3_xboole_0(k1_xboole_0,X2) = k4_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.44    inference(superposition,[],[f59,f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.44    inference(forward_demodulation,[],[f58,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.22/0.44    inference(superposition,[],[f47,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(forward_demodulation,[],[f46,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(superposition,[],[f38,f30])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(superposition,[],[f38,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(forward_demodulation,[],[f56,f32])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(superposition,[],[f39,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f74,f28])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k3_xboole_0(k1_relat_1(k1_xboole_0),X0))) )),
% 0.22/0.44    inference(resolution,[],[f73,f27])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_xboole_0(X0) | k9_relat_1(X0,X1) = k9_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))) )),
% 0.22/0.44    inference(resolution,[],[f40,f33])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.44    inference(ennf_transformation,[],[f19])).
% 0.22/0.44  fof(f19,negated_conjecture,(
% 0.22/0.44    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.44    inference(negated_conjecture,[],[f18])).
% 0.22/0.44  fof(f18,conjecture,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (20977)------------------------------
% 0.22/0.44  % (20977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (20977)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (20977)Memory used [KB]: 6140
% 0.22/0.44  % (20977)Time elapsed: 0.006 s
% 0.22/0.44  % (20977)------------------------------
% 0.22/0.44  % (20977)------------------------------
% 0.22/0.45  % (20960)Success in time 0.082 s
%------------------------------------------------------------------------------
