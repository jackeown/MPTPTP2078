%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  67 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :   69 ( 162 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,(
    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f73,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0) ),
    inference(superposition,[],[f20,f71])).

fof(f71,plain,(
    ! [X2,X3] : k9_relat_1(k8_relat_1(X2,sK2),X3) = k3_xboole_0(k9_relat_1(sK2,X3),X2) ),
    inference(superposition,[],[f68,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).

fof(f29,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X5)
      | k2_relat_1(k7_relat_1(k8_relat_1(X4,X5),X6)) = k9_relat_1(k8_relat_1(X4,X5),X6) ) ),
    inference(resolution,[],[f24,f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f68,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k3_xboole_0(k9_relat_1(sK2,X1),X0) ),
    inference(forward_demodulation,[],[f67,f33])).

fof(f33,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK2),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1)) ),
    inference(resolution,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f67,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X1),X0) ),
    inference(forward_demodulation,[],[f62,f27])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f24,f18])).

fof(f62,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0) ),
    inference(resolution,[],[f31,f18])).

fof(f31,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(k8_relat_1(X1,k7_relat_1(X2,X3))) = k3_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),X1) ) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f20,plain,(
    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:52:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.41  % (20104)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.41  % (20104)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f76,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(trivial_inequality_removal,[],[f75])).
% 0.22/0.41  fof(f75,plain,(
% 0.22/0.41    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.41    inference(superposition,[],[f73,f21])).
% 0.22/0.41  fof(f21,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.41  fof(f73,plain,(
% 0.22/0.41    k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) != k3_xboole_0(k9_relat_1(sK2,sK1),sK0)),
% 0.22/0.41    inference(superposition,[],[f20,f71])).
% 0.22/0.41  fof(f71,plain,(
% 0.22/0.41    ( ! [X2,X3] : (k9_relat_1(k8_relat_1(X2,sK2),X3) = k3_xboole_0(k9_relat_1(sK2,X3),X2)) )),
% 0.22/0.41    inference(superposition,[],[f68,f55])).
% 0.22/0.41  fof(f55,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k9_relat_1(k8_relat_1(X0,sK2),X1)) )),
% 0.22/0.41    inference(resolution,[],[f29,f18])).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    v1_relat_1(sK2)),
% 0.22/0.41    inference(cnf_transformation,[],[f17])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f16])).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.41    inference(flattening,[],[f9])).
% 0.22/0.41  fof(f9,plain,(
% 0.22/0.41    ? [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) != k3_xboole_0(X0,k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.41    inference(ennf_transformation,[],[f8])).
% 0.22/0.41  fof(f8,negated_conjecture,(
% 0.22/0.41    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.41    inference(negated_conjecture,[],[f7])).
% 0.22/0.41  fof(f7,conjecture,(
% 0.22/0.41    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_funct_1)).
% 0.22/0.41  fof(f29,plain,(
% 0.22/0.41    ( ! [X6,X4,X5] : (~v1_relat_1(X5) | k2_relat_1(k7_relat_1(k8_relat_1(X4,X5),X6)) = k9_relat_1(k8_relat_1(X4,X5),X6)) )),
% 0.22/0.41    inference(resolution,[],[f24,f23])).
% 0.22/0.41  fof(f23,plain,(
% 0.22/0.41    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f12])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.41  fof(f24,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f6])).
% 0.22/0.41  fof(f6,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.41  fof(f68,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k8_relat_1(X0,sK2),X1)) = k3_xboole_0(k9_relat_1(sK2,X1),X0)) )),
% 0.22/0.41    inference(forward_demodulation,[],[f67,f33])).
% 0.22/0.41  fof(f33,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK2),X1) = k8_relat_1(X0,k7_relat_1(sK2,X1))) )),
% 0.22/0.41    inference(resolution,[],[f26,f18])).
% 0.22/0.41  fof(f26,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 0.22/0.41    inference(cnf_transformation,[],[f15])).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.41    inference(ennf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,axiom,(
% 0.22/0.41    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.22/0.41  fof(f67,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X1),X0)) )),
% 0.22/0.41    inference(forward_demodulation,[],[f62,f27])).
% 0.22/0.41  fof(f27,plain,(
% 0.22/0.41    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.22/0.41    inference(resolution,[],[f24,f18])).
% 0.22/0.41  fof(f62,plain,(
% 0.22/0.41    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k7_relat_1(sK2,X1))) = k3_xboole_0(k2_relat_1(k7_relat_1(sK2,X1)),X0)) )),
% 0.22/0.41    inference(resolution,[],[f31,f18])).
% 0.22/0.41  fof(f31,plain,(
% 0.22/0.41    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | k2_relat_1(k8_relat_1(X1,k7_relat_1(X2,X3))) = k3_xboole_0(k2_relat_1(k7_relat_1(X2,X3)),X1)) )),
% 0.22/0.41    inference(resolution,[],[f25,f22])).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f11])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.41    inference(ennf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.41  fof(f25,plain,(
% 0.22/0.41    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f14])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.41    inference(ennf_transformation,[],[f4])).
% 0.22/0.41  fof(f4,axiom,(
% 0.22/0.41    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.41  fof(f20,plain,(
% 0.22/0.41    k9_relat_1(k8_relat_1(sK0,sK2),sK1) != k3_xboole_0(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.41    inference(cnf_transformation,[],[f17])).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (20104)------------------------------
% 0.22/0.41  % (20104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (20104)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (20104)Memory used [KB]: 6140
% 0.22/0.41  % (20104)Time elapsed: 0.005 s
% 0.22/0.41  % (20104)------------------------------
% 0.22/0.41  % (20104)------------------------------
% 0.22/0.41  % (20098)Success in time 0.05 s
%------------------------------------------------------------------------------
