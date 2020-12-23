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
% DateTime   : Thu Dec  3 12:48:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 423 expanded)
%              Number of leaves         :    5 (  95 expanded)
%              Depth                    :   20
%              Number of atoms          :   67 ( 718 expanded)
%              Number of equality atoms :   41 ( 330 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f524,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f523])).

fof(f523,plain,(
    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f13,f475])).

fof(f475,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1)) ),
    inference(superposition,[],[f431,f152])).

fof(f152,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(X0,sK1))) ),
    inference(superposition,[],[f80,f33])).

fof(f33,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X0,sK1)) ),
    inference(resolution,[],[f19,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k8_relat_1(k2_relat_1(k8_relat_1(X0,X1)),k8_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f14,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f80,plain,(
    ! [X0,X1] : k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X1,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1,k8_relat_1(X0,sK1))) ),
    inference(forward_demodulation,[],[f79,f68])).

fof(f68,plain,(
    ! [X2,X1] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1,k8_relat_1(X2,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k8_relat_1(X2,sK1))),sK1) ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1) ),
    inference(resolution,[],[f17,f12])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(f25,plain,(
    ! [X0] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),sK1) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0) ),
    inference(resolution,[],[f16,f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f79,plain,(
    ! [X0,X1] : k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X1,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k8_relat_1(X0,sK1))),sK1) ),
    inference(superposition,[],[f23,f38])).

fof(f38,plain,(
    ! [X6,X5] : k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k2_relat_1(k8_relat_1(X6,sK1)),X5) ),
    inference(resolution,[],[f31,f16])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(superposition,[],[f27,f18])).

fof(f18,plain,(
    sK1 = k8_relat_1(k2_relat_1(sK1),sK1) ),
    inference(resolution,[],[f14,f12])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X0,k8_relat_1(X1,sK1))) ),
    inference(subsumption_resolution,[],[f26,f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,k8_relat_1(X1,sK1)))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f15,f23])).

fof(f431,plain,(
    ! [X4,X3] : k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) ),
    inference(forward_demodulation,[],[f430,f365])).

fof(f365,plain,(
    ! [X4,X3] : k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1)))))) ),
    inference(forward_demodulation,[],[f349,f43])).

fof(f43,plain,(
    ! [X6,X4,X8,X7,X5] : k8_relat_1(X4,k8_relat_1(X5,k8_relat_1(X6,k8_relat_1(X7,k8_relat_1(X8,sK1))))) = k8_relat_1(k3_xboole_0(X4,X5),k8_relat_1(X6,k8_relat_1(X7,k8_relat_1(X8,sK1)))) ),
    inference(resolution,[],[f32,f17])).

fof(f32,plain,(
    ! [X2,X3,X1] : v1_relat_1(k8_relat_1(X3,k8_relat_1(X1,k8_relat_1(X2,sK1)))) ),
    inference(superposition,[],[f27,f23])).

fof(f349,plain,(
    ! [X4,X3] : k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X3,X4),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))))) ),
    inference(superposition,[],[f322,f23])).

fof(f322,plain,(
    ! [X0] : k8_relat_1(X0,sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)))) ),
    inference(superposition,[],[f182,f18])).

fof(f182,plain,(
    ! [X4,X3] : k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,k8_relat_1(X3,k8_relat_1(X4,sK1))))) ),
    inference(forward_demodulation,[],[f170,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,k8_relat_1(X3,sK1)))) = k8_relat_1(k3_xboole_0(X0,X1),k8_relat_1(X2,k8_relat_1(X3,sK1))) ),
    inference(resolution,[],[f27,f17])).

fof(f170,plain,(
    ! [X4,X3] : k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X3,X4),k8_relat_1(X3,k8_relat_1(X4,sK1)))) ),
    inference(superposition,[],[f152,f23])).

fof(f430,plain,(
    ! [X4,X3] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1)))))) ),
    inference(forward_demodulation,[],[f412,f43])).

fof(f412,plain,(
    ! [X4,X3] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X3,X4),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))))) ),
    inference(superposition,[],[f276,f23])).

fof(f276,plain,(
    ! [X0] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)))) ),
    inference(forward_demodulation,[],[f243,f25])).

fof(f243,plain,(
    ! [X0] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),sK1))) ),
    inference(superposition,[],[f211,f33])).

fof(f211,plain,(
    ! [X4,X3] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X4,k8_relat_1(X3,sK1))) ),
    inference(superposition,[],[f97,f80])).

fof(f97,plain,(
    ! [X0,X1] : k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(X1,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X1,sK1)) ),
    inference(superposition,[],[f37,f21])).

fof(f37,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k3_xboole_0(X2,X3),k8_relat_1(X4,sK1)) ),
    inference(resolution,[],[f31,f17])).

fof(f13,plain,(
    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:14 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.42  % (9602)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (9609)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (9603)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (9602)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f524,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f523])).
% 0.21/0.44  fof(f523,plain,(
% 0.21/0.44    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,sK1)),
% 0.21/0.44    inference(superposition,[],[f13,f475])).
% 0.21/0.44  fof(f475,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(X0,k8_relat_1(X0,sK1))) )),
% 0.21/0.44    inference(superposition,[],[f431,f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(X0,sK1)))) )),
% 0.21/0.44    inference(superposition,[],[f80,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X0,sK1))) )),
% 0.21/0.44    inference(resolution,[],[f19,f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0,X1] : (k8_relat_1(X0,X1) != k8_relat_1(X0,k8_relat_1(X0,X1)) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k8_relat_1(X0,k8_relat_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_relat_1)).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k8_relat_1(k2_relat_1(k8_relat_1(X0,X1)),k8_relat_1(X0,X1))) )),
% 0.21/0.44    inference(resolution,[],[f14,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X1,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1,k8_relat_1(X0,sK1)))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f79,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X1,k8_relat_1(X2,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k8_relat_1(X2,sK1))),sK1)) )),
% 0.21/0.44    inference(superposition,[],[f25,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK1)) = k8_relat_1(k3_xboole_0(X0,X1),sK1)) )),
% 0.21/0.44    inference(resolution,[],[f17,f12])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),sK1)) )),
% 0.21/0.44    inference(superposition,[],[f23,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK1)) = k3_xboole_0(k2_relat_1(sK1),X0)) )),
% 0.21/0.44    inference(resolution,[],[f16,f12])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X1,sK1)) = k8_relat_1(k2_relat_1(k8_relat_1(X1,k8_relat_1(X0,sK1))),sK1)) )),
% 0.21/0.44    inference(superposition,[],[f23,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X6,X5] : (k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k2_relat_1(k8_relat_1(X6,sK1)),X5)) )),
% 0.21/0.44    inference(resolution,[],[f31,f16])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) )),
% 0.21/0.44    inference(superposition,[],[f27,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    sK1 = k8_relat_1(k2_relat_1(sK1),sK1)),
% 0.21/0.44    inference(resolution,[],[f14,f12])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,k8_relat_1(X1,sK1)))) )),
% 0.21/0.44    inference(subsumption_resolution,[],[f26,f12])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,k8_relat_1(X1,sK1))) | ~v1_relat_1(sK1)) )),
% 0.21/0.44    inference(superposition,[],[f15,f23])).
% 0.21/0.44  fof(f431,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1)))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f430,f365])).
% 0.21/0.44  fof(f365,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))))))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f349,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X6,X4,X8,X7,X5] : (k8_relat_1(X4,k8_relat_1(X5,k8_relat_1(X6,k8_relat_1(X7,k8_relat_1(X8,sK1))))) = k8_relat_1(k3_xboole_0(X4,X5),k8_relat_1(X6,k8_relat_1(X7,k8_relat_1(X8,sK1))))) )),
% 0.21/0.44    inference(resolution,[],[f32,f17])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X2,X3,X1] : (v1_relat_1(k8_relat_1(X3,k8_relat_1(X1,k8_relat_1(X2,sK1))))) )),
% 0.21/0.44    inference(superposition,[],[f27,f23])).
% 0.21/0.44  fof(f349,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X3,X4),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1)))))) )),
% 0.21/0.44    inference(superposition,[],[f322,f23])).
% 0.21/0.44  fof(f322,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(X0,sK1) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1))))) )),
% 0.21/0.44    inference(superposition,[],[f182,f18])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,k8_relat_1(X3,k8_relat_1(X4,sK1)))))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f170,f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (k8_relat_1(X0,k8_relat_1(X1,k8_relat_1(X2,k8_relat_1(X3,sK1)))) = k8_relat_1(k3_xboole_0(X0,X1),k8_relat_1(X2,k8_relat_1(X3,sK1)))) )),
% 0.21/0.44    inference(resolution,[],[f27,f17])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(X3,k8_relat_1(X4,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X3,X4),k8_relat_1(X3,k8_relat_1(X4,sK1))))) )),
% 0.21/0.44    inference(superposition,[],[f152,f23])).
% 0.21/0.44  fof(f430,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))))))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f412,f43])).
% 0.21/0.44  fof(f412,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(k3_xboole_0(X3,X4),k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1)))))) )),
% 0.21/0.44    inference(superposition,[],[f276,f23])).
% 0.21/0.44  fof(f276,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1))))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f243,f25])).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    ( ! [X0] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,sK1)) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),sK1)))) )),
% 0.21/0.44    inference(superposition,[],[f211,f33])).
% 0.21/0.44  fof(f211,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k2_relat_1(sK1),k8_relat_1(X4,k8_relat_1(X3,sK1)))) )),
% 0.21/0.44    inference(superposition,[],[f97,f80])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k8_relat_1(k2_relat_1(sK1),k8_relat_1(X0,k8_relat_1(X1,sK1))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,sK1)),k8_relat_1(X1,sK1))) )),
% 0.21/0.44    inference(superposition,[],[f37,f21])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X4,X2,X3] : (k8_relat_1(X2,k8_relat_1(X3,k8_relat_1(X4,sK1))) = k8_relat_1(k3_xboole_0(X2,X3),k8_relat_1(X4,sK1))) )),
% 0.21/0.44    inference(resolution,[],[f31,f17])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k8_relat_1(sK0,sK1) != k8_relat_1(sK0,k8_relat_1(sK0,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9602)------------------------------
% 0.21/0.44  % (9602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9602)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9602)Memory used [KB]: 10874
% 0.21/0.44  % (9602)Time elapsed: 0.019 s
% 0.21/0.44  % (9602)------------------------------
% 0.21/0.44  % (9602)------------------------------
% 0.21/0.44  % (9597)Success in time 0.075 s
%------------------------------------------------------------------------------
