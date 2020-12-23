%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  92 expanded)
%              Number of equality atoms :   21 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,(
    k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f14,f36])).

fof(f36,plain,(
    ! [X2,X1] : k7_relat_1(k8_relat_1(X1,sK2),X2) = k8_relat_1(X1,k7_relat_1(sK2,X2)) ),
    inference(forward_demodulation,[],[f35,f19])).

fof(f19,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2) ),
    inference(resolution,[],[f17,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f35,plain,(
    ! [X2,X1] : k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),sK2)) = k7_relat_1(k8_relat_1(X1,sK2),X2) ),
    inference(forward_demodulation,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k7_relat_1(k8_relat_1(X0,sK2),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f21,f13])).

fof(f21,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(X4)
      | k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4)) ) ),
    inference(resolution,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f33,plain,(
    ! [X2,X1] : k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),sK2)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,sK2)) ),
    inference(resolution,[],[f25,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(X1,k5_relat_1(X0,sK2)) = k5_relat_1(X0,k8_relat_1(X1,sK2)) ) ),
    inference(resolution,[],[f18,f13])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f14,plain,(
    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (19084)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (19084)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    k8_relat_1(sK0,k7_relat_1(sK2,sK1)) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.21/0.42    inference(superposition,[],[f14,f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X2,X1] : (k7_relat_1(k8_relat_1(X1,sK2),X2) = k8_relat_1(X1,k7_relat_1(sK2,X2))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f35,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(sK2,X0) = k5_relat_1(k6_relat_1(X0),sK2)) )),
% 0.21/0.42    inference(resolution,[],[f17,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    v1_relat_1(sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2)) => (k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) != k8_relat_1(X0,k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X2,X1] : (k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),sK2)) = k7_relat_1(k8_relat_1(X1,sK2),X2)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f33,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,sK2),X1) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,sK2))) )),
% 0.21/0.42    inference(resolution,[],[f21,f13])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X4,X5,X3] : (~v1_relat_1(X4) | k7_relat_1(k8_relat_1(X3,X4),X5) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X3,X4))) )),
% 0.21/0.42    inference(resolution,[],[f17,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X2,X1] : (k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),sK2)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,sK2))) )),
% 0.21/0.42    inference(resolution,[],[f25,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k8_relat_1(X1,k5_relat_1(X0,sK2)) = k5_relat_1(X0,k8_relat_1(X1,sK2))) )),
% 0.21/0.42    inference(resolution,[],[f18,f13])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k7_relat_1(k8_relat_1(sK0,sK2),sK1) != k8_relat_1(sK0,k7_relat_1(sK2,sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (19084)------------------------------
% 0.21/0.42  % (19084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (19084)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (19084)Memory used [KB]: 6140
% 0.21/0.42  % (19084)Time elapsed: 0.005 s
% 0.21/0.42  % (19084)------------------------------
% 0.21/0.42  % (19084)------------------------------
% 0.21/0.43  % (19079)Success in time 0.062 s
%------------------------------------------------------------------------------
