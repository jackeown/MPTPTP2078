%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  75 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 150 expanded)
%              Number of equality atoms :   29 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f114])).

fof(f114,plain,(
    ! [X12,X11] : k8_relat_1(X11,k7_relat_1(sK2,X12)) = k7_relat_1(k8_relat_1(X11,sK2),X12) ),
    inference(backward_demodulation,[],[f43,f113])).

fof(f113,plain,(
    ! [X0,X1] : k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,sK2),X0) ),
    inference(forward_demodulation,[],[f112,f63])).

fof(f63,plain,(
    ! [X15,X16] : k7_relat_1(k8_relat_1(X15,sK2),X16) = k5_relat_1(k6_relat_1(X16),k8_relat_1(X15,sK2)) ),
    inference(resolution,[],[f31,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f31,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X6)
      | k7_relat_1(k8_relat_1(X5,X6),X7) = k5_relat_1(k6_relat_1(X7),k8_relat_1(X5,X6)) ) ),
    inference(resolution,[],[f24,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f112,plain,(
    ! [X0,X1] : k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,sK2)) ),
    inference(forward_demodulation,[],[f107,f32])).

fof(f32,plain,(
    ! [X8] : k7_relat_1(sK2,X8) = k5_relat_1(k6_relat_1(X8),sK2) ),
    inference(resolution,[],[f24,f17])).

fof(f107,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,sK2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k6_relat_1(X1)) ),
    inference(resolution,[],[f78,f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f78,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X15,sK2),k6_relat_1(X16)) = k5_relat_1(X15,k8_relat_1(X16,sK2)) ) ),
    inference(forward_demodulation,[],[f75,f28])).

fof(f28,plain,(
    ! [X8] : k8_relat_1(X8,sK2) = k5_relat_1(sK2,k6_relat_1(X8)) ),
    inference(resolution,[],[f23,f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f75,plain,(
    ! [X15,X16] :
      ( k5_relat_1(k5_relat_1(X15,sK2),k6_relat_1(X16)) = k5_relat_1(X15,k5_relat_1(sK2,k6_relat_1(X16)))
      | ~ v1_relat_1(X15) ) ),
    inference(resolution,[],[f34,f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f20,f19])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f43,plain,(
    ! [X12,X11] : k8_relat_1(X11,k7_relat_1(sK2,X12)) = k5_relat_1(k7_relat_1(sK2,X12),k6_relat_1(X11)) ),
    inference(resolution,[],[f26,f17])).

fof(f26,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | k8_relat_1(X2,k7_relat_1(X3,X4)) = k5_relat_1(k7_relat_1(X3,X4),k6_relat_1(X2)) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f18,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.39  % (8661)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (8666)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (8666)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f18,f114])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X12,X11] : (k8_relat_1(X11,k7_relat_1(sK2,X12)) = k7_relat_1(k8_relat_1(X11,sK2),X12)) )),
% 0.21/0.43    inference(backward_demodulation,[],[f43,f113])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,sK2),X0)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f112,f63])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X15,X16] : (k7_relat_1(k8_relat_1(X15,sK2),X16) = k5_relat_1(k6_relat_1(X16),k8_relat_1(X15,sK2))) )),
% 0.21/0.43    inference(resolution,[],[f31,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    v1_relat_1(sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2)) => (k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X6,X7,X5] : (~v1_relat_1(X6) | k7_relat_1(k8_relat_1(X5,X6),X7) = k5_relat_1(k6_relat_1(X7),k8_relat_1(X5,X6))) )),
% 0.21/0.43    inference(resolution,[],[f24,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k7_relat_1(sK2,X0),k6_relat_1(X1)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,sK2))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f107,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X8] : (k7_relat_1(sK2,X8) = k5_relat_1(k6_relat_1(X8),sK2)) )),
% 0.21/0.43    inference(resolution,[],[f24,f17])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,sK2)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),sK2),k6_relat_1(X1))) )),
% 0.21/0.43    inference(resolution,[],[f78,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ( ! [X15,X16] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X15,sK2),k6_relat_1(X16)) = k5_relat_1(X15,k8_relat_1(X16,sK2))) )),
% 0.21/0.43    inference(forward_demodulation,[],[f75,f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X8] : (k8_relat_1(X8,sK2) = k5_relat_1(sK2,k6_relat_1(X8))) )),
% 0.21/0.43    inference(resolution,[],[f23,f17])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X15,X16] : (k5_relat_1(k5_relat_1(X15,sK2),k6_relat_1(X16)) = k5_relat_1(X15,k5_relat_1(sK2,k6_relat_1(X16))) | ~v1_relat_1(X15)) )),
% 0.21/0.43    inference(resolution,[],[f34,f17])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(resolution,[],[f20,f19])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X12,X11] : (k8_relat_1(X11,k7_relat_1(sK2,X12)) = k5_relat_1(k7_relat_1(sK2,X12),k6_relat_1(X11))) )),
% 0.21/0.43    inference(resolution,[],[f26,f17])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | k8_relat_1(X2,k7_relat_1(X3,X4)) = k5_relat_1(k7_relat_1(X3,X4),k6_relat_1(X2))) )),
% 0.21/0.43    inference(resolution,[],[f23,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (8666)------------------------------
% 0.21/0.43  % (8666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (8666)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (8666)Memory used [KB]: 10746
% 0.21/0.43  % (8666)Time elapsed: 0.011 s
% 0.21/0.43  % (8666)------------------------------
% 0.21/0.43  % (8666)------------------------------
% 0.21/0.44  % (8659)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (8656)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.44  % (8651)Success in time 0.081 s
%------------------------------------------------------------------------------
