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
% DateTime   : Thu Dec  3 12:49:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  61 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 ( 122 expanded)
%              Number of equality atoms :   24 (  51 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,(
    k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f17,f118])).

fof(f118,plain,(
    ! [X4,X3] : k8_relat_1(X3,k7_relat_1(sK2,X4)) = k7_relat_1(k8_relat_1(X3,sK2),X4) ),
    inference(forward_demodulation,[],[f117,f23])).

fof(f23,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f117,plain,(
    ! [X4,X3] : k7_relat_1(k8_relat_1(X3,sK2),X4) = k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK2)) ),
    inference(forward_demodulation,[],[f105,f46])).

fof(f46,plain,(
    ! [X2,X3] : k7_relat_1(k8_relat_1(X2,sK2),X3) = k5_relat_1(k6_relat_1(X3),k8_relat_1(X2,sK2)) ),
    inference(resolution,[],[f44,f19])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(global_subsumption,[],[f16,f18,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k8_relat_1(X0,sK2))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f22,f42])).

fof(f42,plain,(
    ! [X14] : k8_relat_1(X14,sK2) = k5_relat_1(sK2,k6_relat_1(X14)) ),
    inference(resolution,[],[f20,f16])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f18,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f105,plain,(
    ! [X4,X3] : k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,sK2)) ),
    inference(resolution,[],[f89,f18])).

fof(f89,plain,(
    ! [X50,X49] :
      ( ~ v1_relat_1(X49)
      | k8_relat_1(X50,k5_relat_1(X49,sK2)) = k5_relat_1(X49,k8_relat_1(X50,sK2)) ) ),
    inference(resolution,[],[f21,f16])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f17,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.43  % (30798)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (30795)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (30795)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f122,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f120])).
% 0.22/0.43  fof(f120,plain,(
% 0.22/0.43    k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.22/0.43    inference(superposition,[],[f17,f118])).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ( ! [X4,X3] : (k8_relat_1(X3,k7_relat_1(sK2,X4)) = k7_relat_1(k8_relat_1(X3,sK2),X4)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f117,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.22/0.43    inference(resolution,[],[f19,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2)) => (k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.43  fof(f117,plain,(
% 0.22/0.43    ( ! [X4,X3] : (k7_relat_1(k8_relat_1(X3,sK2),X4) = k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK2))) )),
% 0.22/0.43    inference(forward_demodulation,[],[f105,f46])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X2,X3] : (k7_relat_1(k8_relat_1(X2,sK2),X3) = k5_relat_1(k6_relat_1(X3),k8_relat_1(X2,sK2))) )),
% 0.22/0.43    inference(resolution,[],[f44,f19])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.22/0.43    inference(global_subsumption,[],[f16,f18,f43])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(sK2)) )),
% 0.22/0.43    inference(superposition,[],[f22,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X14] : (k8_relat_1(X14,sK2) = k5_relat_1(sK2,k6_relat_1(X14))) )),
% 0.22/0.43    inference(resolution,[],[f20,f16])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    ( ! [X4,X3] : (k8_relat_1(X3,k5_relat_1(k6_relat_1(X4),sK2)) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X3,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f89,f18])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    ( ! [X50,X49] : (~v1_relat_1(X49) | k8_relat_1(X50,k5_relat_1(X49,sK2)) = k5_relat_1(X49,k8_relat_1(X50,sK2))) )),
% 0.22/0.44    inference(resolution,[],[f21,f16])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (30795)------------------------------
% 0.22/0.44  % (30795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (30795)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (30795)Memory used [KB]: 6268
% 0.22/0.44  % (30795)Time elapsed: 0.005 s
% 0.22/0.44  % (30795)------------------------------
% 0.22/0.44  % (30795)------------------------------
% 0.22/0.44  % (30796)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (30790)Success in time 0.079 s
%------------------------------------------------------------------------------
