%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 100 expanded)
%              Number of leaves         :    9 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  110 ( 240 expanded)
%              Number of equality atoms :   26 (  70 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f112])).

fof(f112,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f111,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f111,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f23,f106])).

fof(f106,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f102,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f102,plain,(
    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    inference(forward_demodulation,[],[f100,f26])).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f100,plain,(
    r1_tarski(k2_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(sK0,sK2)))),sK1) ),
    inference(superposition,[],[f42,f81])).

fof(f81,plain,(
    k6_relat_1(k2_relat_1(k8_relat_1(sK0,sK2))) = k8_relat_1(sK1,k6_relat_1(k2_relat_1(k8_relat_1(sK0,sK2)))) ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X0) ),
    inference(global_subsumption,[],[f21,f24,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f35,f26])).

fof(f35,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),k2_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f27,f32])).

fof(f32,plain,(
    ! [X0] : k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0)) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k6_relat_1(X0) = k8_relat_1(sK1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f53,f22])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f24,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f30,f26])).

fof(f42,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X2) ),
    inference(global_subsumption,[],[f24,f41])).

fof(f41,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(global_subsumption,[],[f24,f40])).

fof(f40,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X2)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X1] : k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f29,f24])).

fof(f23,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (23263)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (23261)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (23262)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (23261)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f21,f112])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ~v1_relat_1(sK2)),
% 0.21/0.43    inference(resolution,[],[f111,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.21/0.43    inference(global_subsumption,[],[f23,f106])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.21/0.43    inference(resolution,[],[f102,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(flattening,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 0.21/0.43    inference(forward_demodulation,[],[f100,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    r1_tarski(k2_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(sK0,sK2)))),sK1)),
% 0.21/0.43    inference(superposition,[],[f42,f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    k6_relat_1(k2_relat_1(k8_relat_1(sK0,sK2))) = k8_relat_1(sK1,k6_relat_1(k2_relat_1(k8_relat_1(sK0,sK2))))),
% 0.21/0.43    inference(resolution,[],[f67,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X0)) )),
% 0.21/0.43    inference(global_subsumption,[],[f21,f24,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK2)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f35,f26])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),k2_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK2)) )),
% 0.21/0.43    inference(superposition,[],[f27,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (k8_relat_1(X0,sK2) = k5_relat_1(sK2,k6_relat_1(X0))) )),
% 0.21/0.43    inference(resolution,[],[f29,f21])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(X0,sK0) | k6_relat_1(X0) = k8_relat_1(sK1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(resolution,[],[f53,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(resolution,[],[f48,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(global_subsumption,[],[f24,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(superposition,[],[f30,f26])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X2)) )),
% 0.21/0.43    inference(global_subsumption,[],[f24,f41])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.21/0.43    inference(global_subsumption,[],[f24,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X2) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f36,f26])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.21/0.43    inference(superposition,[],[f27,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X2,X1] : (k8_relat_1(X1,k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 0.21/0.43    inference(resolution,[],[f29,f24])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (23261)------------------------------
% 0.21/0.43  % (23261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (23261)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (23261)Memory used [KB]: 6268
% 0.21/0.43  % (23261)Time elapsed: 0.015 s
% 0.21/0.43  % (23261)------------------------------
% 0.21/0.43  % (23261)------------------------------
% 0.21/0.43  % (23256)Success in time 0.077 s
%------------------------------------------------------------------------------
