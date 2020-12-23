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
% DateTime   : Thu Dec  3 12:53:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 145 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 452 expanded)
%              Number of equality atoms :   50 ( 202 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f542,plain,(
    $false ),
    inference(subsumption_resolution,[],[f541,f540])).

fof(f540,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f539])).

fof(f539,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2)
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f20,f538])).

fof(f538,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(forward_demodulation,[],[f534,f32])).

fof(f32,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(resolution,[],[f26,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
      | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
    & r1_tarski(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
          | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))
        | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) )
      & r1_tarski(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2))
        | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
            & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f534,plain,(
    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(superposition,[],[f444,f37])).

fof(f37,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0) ),
    inference(superposition,[],[f34,f31])).

fof(f31,plain,(
    sK0 = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f28,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f29,f33])).

fof(f33,plain,(
    ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f26,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f29,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f25,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f444,plain,(
    ! [X0,X1] : k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,sK2)) ),
    inference(forward_demodulation,[],[f438,f32])).

fof(f438,plain,(
    ! [X0,X1] : k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k5_relat_1(sK2,k6_relat_1(X1))) ),
    inference(resolution,[],[f122,f17])).

fof(f122,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | k8_relat_1(X2,k5_relat_1(X3,k6_relat_1(X4))) = k5_relat_1(X3,k8_relat_1(X2,k6_relat_1(X4))) ) ),
    inference(resolution,[],[f27,f21])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f20,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f541,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f535,f32])).

fof(f535,plain,(
    k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k5_relat_1(sK2,k6_relat_1(sK0)) ),
    inference(superposition,[],[f444,f191])).

fof(f191,plain,(
    k6_relat_1(sK0) = k8_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(superposition,[],[f35,f31])).

fof(f35,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_tarski(X1,X0))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (27669)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (27669)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f542,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f541,f540])).
% 0.20/0.46  fof(f540,plain,(
% 0.20/0.46    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.46    inference(trivial_inequality_removal,[],[f539])).
% 0.20/0.46  fof(f539,plain,(
% 0.20/0.46    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.46    inference(backward_demodulation,[],[f20,f538])).
% 0.20/0.46  fof(f538,plain,(
% 0.20/0.46    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f534,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.20/0.46    inference(resolution,[],[f26,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    (k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => ((k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))) & r1_tarski(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.46    inference(flattening,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (((k8_relat_1(X0,X2) != k8_relat_1(X0,k8_relat_1(X1,X2)) | k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))) & r1_tarski(X0,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r1_tarski(X0,X1) => (k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.46  fof(f534,plain,(
% 0.20/0.46    k8_relat_1(sK0,k8_relat_1(sK1,sK2)) = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.20/0.46    inference(superposition,[],[f444,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(sK0)),
% 0.20/0.46    inference(superposition,[],[f34,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    sK0 = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.46    inference(resolution,[],[f30,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f28,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_tarski(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.46    inference(backward_demodulation,[],[f29,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.20/0.46    inference(resolution,[],[f26,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f25,f24])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.46  fof(f444,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,sK2))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f438,f32])).
% 0.20/0.46  fof(f438,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_relat_1(sK2,k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k5_relat_1(sK2,k6_relat_1(X1)))) )),
% 0.20/0.46    inference(resolution,[],[f122,f17])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | k8_relat_1(X2,k5_relat_1(X3,k6_relat_1(X4))) = k5_relat_1(X3,k8_relat_1(X2,k6_relat_1(X4)))) )),
% 0.20/0.46    inference(resolution,[],[f27,f21])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | k8_relat_1(sK0,sK2) != k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f541,plain,(
% 0.20/0.46    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f535,f32])).
% 0.20/0.46  fof(f535,plain,(
% 0.20/0.46    k8_relat_1(sK1,k8_relat_1(sK0,sK2)) = k5_relat_1(sK2,k6_relat_1(sK0))),
% 0.20/0.46    inference(superposition,[],[f444,f191])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    k6_relat_1(sK0) = k8_relat_1(sK1,k6_relat_1(sK0))),
% 0.20/0.46    inference(superposition,[],[f35,f31])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_tarski(X1,X0))) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.46    inference(superposition,[],[f34,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (27669)------------------------------
% 0.20/0.46  % (27669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (27669)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (27669)Memory used [KB]: 2046
% 0.20/0.46  % (27669)Time elapsed: 0.032 s
% 0.20/0.46  % (27669)------------------------------
% 0.20/0.46  % (27669)------------------------------
% 0.20/0.46  % (27655)Success in time 0.101 s
%------------------------------------------------------------------------------
