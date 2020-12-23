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
% DateTime   : Thu Dec  3 12:48:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 126 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 314 expanded)
%              Number of equality atoms :   43 ( 116 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(global_subsumption,[],[f22,f299])).

fof(f299,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f297,f32])).

fof(f32,plain,(
    sK1 = k4_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f26,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( sK1 != k5_relat_1(sK1,k6_relat_1(sK0))
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f297,plain,(
    k5_relat_1(sK1,k6_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK1)) ),
    inference(superposition,[],[f295,f114])).

fof(f114,plain,(
    k4_relat_1(sK1) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) ),
    inference(superposition,[],[f113,f74])).

fof(f74,plain,(
    k4_relat_1(sK1) = k5_relat_1(k6_relat_1(sK0),k4_relat_1(sK1)) ),
    inference(global_subsumption,[],[f20,f73])).

fof(f73,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k6_relat_1(sK0),k4_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f72,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f72,plain,
    ( ~ v1_relat_1(k4_relat_1(sK1))
    | k4_relat_1(sK1) = k5_relat_1(k6_relat_1(sK0),k4_relat_1(sK1)) ),
    inference(resolution,[],[f69,f21])).

fof(f21,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | k4_relat_1(sK1) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1))
      | ~ v1_relat_1(k4_relat_1(sK1)) ) ),
    inference(superposition,[],[f30,f37])).

fof(f37,plain,(
    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1)) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f113,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f111,f24])).

fof(f24,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f111,plain,(
    ! [X0] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(sK1)) ),
    inference(resolution,[],[f100,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(sK1,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK1)) ) ),
    inference(resolution,[],[f29,f20])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f295,plain,(
    ! [X1] : k5_relat_1(sK1,k6_relat_1(X1)) = k4_relat_1(k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1)))) ),
    inference(forward_demodulation,[],[f294,f24])).

fof(f294,plain,(
    ! [X1] : k5_relat_1(sK1,k4_relat_1(k6_relat_1(X1))) = k4_relat_1(k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1)))) ),
    inference(forward_demodulation,[],[f291,f113])).

fof(f291,plain,(
    ! [X1] : k5_relat_1(sK1,k4_relat_1(k6_relat_1(X1))) = k4_relat_1(k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1))) ),
    inference(resolution,[],[f289,f23])).

fof(f289,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(sK1,k4_relat_1(X7)) = k4_relat_1(k5_relat_1(X7,k4_relat_1(sK1))) ) ),
    inference(forward_demodulation,[],[f282,f32])).

fof(f282,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(X7,k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k4_relat_1(X7)) ) ),
    inference(resolution,[],[f99,f20])).

fof(f99,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X3)
      | k4_relat_1(k5_relat_1(X4,k4_relat_1(X3))) = k5_relat_1(k4_relat_1(k4_relat_1(X3)),k4_relat_1(X4)) ) ),
    inference(resolution,[],[f29,f25])).

fof(f22,plain,(
    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (32332)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (32336)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (32332)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f300,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(global_subsumption,[],[f22,f299])).
% 0.21/0.42  fof(f299,plain,(
% 0.21/0.42    sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.21/0.42    inference(forward_demodulation,[],[f297,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    sK1 = k4_relat_1(k4_relat_1(sK1))),
% 0.21/0.42    inference(resolution,[],[f26,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1)) => (sK1 != k5_relat_1(sK1,k6_relat_1(sK0)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.42  fof(f297,plain,(
% 0.21/0.42    k5_relat_1(sK1,k6_relat_1(sK0)) = k4_relat_1(k4_relat_1(sK1))),
% 0.21/0.42    inference(superposition,[],[f295,f114])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    k4_relat_1(sK1) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))),
% 0.21/0.42    inference(superposition,[],[f113,f74])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    k4_relat_1(sK1) = k5_relat_1(k6_relat_1(sK0),k4_relat_1(sK1))),
% 0.21/0.42    inference(global_subsumption,[],[f20,f73])).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    k4_relat_1(sK1) = k5_relat_1(k6_relat_1(sK0),k4_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.42    inference(resolution,[],[f72,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ~v1_relat_1(k4_relat_1(sK1)) | k4_relat_1(sK1) = k5_relat_1(k6_relat_1(sK0),k4_relat_1(sK1))),
% 0.21/0.42    inference(resolution,[],[f69,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | k4_relat_1(sK1) = k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1))) )),
% 0.21/0.42    inference(superposition,[],[f30,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    k2_relat_1(sK1) = k1_relat_1(k4_relat_1(sK1))),
% 0.21/0.42    inference(resolution,[],[f27,f20])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0)))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f111,f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    ( ! [X0] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(sK1))) )),
% 0.21/0.42    inference(resolution,[],[f100,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK1,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK1))) )),
% 0.21/0.42    inference(resolution,[],[f29,f20])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.42  fof(f295,plain,(
% 0.21/0.42    ( ! [X1] : (k5_relat_1(sK1,k6_relat_1(X1)) = k4_relat_1(k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f294,f24])).
% 0.21/0.42  fof(f294,plain,(
% 0.21/0.42    ( ! [X1] : (k5_relat_1(sK1,k4_relat_1(k6_relat_1(X1))) = k4_relat_1(k4_relat_1(k5_relat_1(sK1,k6_relat_1(X1))))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f291,f113])).
% 0.21/0.42  fof(f291,plain,(
% 0.21/0.42    ( ! [X1] : (k5_relat_1(sK1,k4_relat_1(k6_relat_1(X1))) = k4_relat_1(k5_relat_1(k6_relat_1(X1),k4_relat_1(sK1)))) )),
% 0.21/0.42    inference(resolution,[],[f289,f23])).
% 0.21/0.42  fof(f289,plain,(
% 0.21/0.42    ( ! [X7] : (~v1_relat_1(X7) | k5_relat_1(sK1,k4_relat_1(X7)) = k4_relat_1(k5_relat_1(X7,k4_relat_1(sK1)))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f282,f32])).
% 0.21/0.42  fof(f282,plain,(
% 0.21/0.42    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(X7,k4_relat_1(sK1))) = k5_relat_1(k4_relat_1(k4_relat_1(sK1)),k4_relat_1(X7))) )),
% 0.21/0.42    inference(resolution,[],[f99,f20])).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X4,X3] : (~v1_relat_1(X4) | ~v1_relat_1(X3) | k4_relat_1(k5_relat_1(X4,k4_relat_1(X3))) = k5_relat_1(k4_relat_1(k4_relat_1(X3)),k4_relat_1(X4))) )),
% 0.21/0.42    inference(resolution,[],[f29,f25])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    sK1 != k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (32332)------------------------------
% 0.21/0.42  % (32332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (32332)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (32332)Memory used [KB]: 6268
% 0.21/0.42  % (32332)Time elapsed: 0.012 s
% 0.21/0.42  % (32332)------------------------------
% 0.21/0.42  % (32332)------------------------------
% 0.21/0.43  % (32337)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (32326)Success in time 0.069 s
%------------------------------------------------------------------------------
