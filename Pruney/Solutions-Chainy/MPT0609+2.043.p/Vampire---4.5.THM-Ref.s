%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:30 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   25 (  62 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   41 ( 119 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f25])).

fof(f25,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] : k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f16,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f24,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f13,f23])).

fof(f23,plain,(
    ! [X0] : k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f22,f21])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(forward_demodulation,[],[f18,f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f14,f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f18,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(resolution,[],[f15,f12])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f13,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 13:25:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.44  % (16160)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.44  % (16164)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.23/0.44  % (16160)Refutation found. Thanks to Tanya!
% 0.23/0.44  % SZS status Theorem for theBenchmark
% 0.23/0.44  % SZS output start Proof for theBenchmark
% 0.23/0.44  fof(f26,plain,(
% 0.23/0.44    $false),
% 0.23/0.44    inference(trivial_inequality_removal,[],[f25])).
% 0.23/0.44  fof(f25,plain,(
% 0.23/0.44    k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.23/0.44    inference(superposition,[],[f24,f21])).
% 0.23/0.44  fof(f21,plain,(
% 0.23/0.44    ( ! [X0] : (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0)) )),
% 0.23/0.44    inference(resolution,[],[f16,f12])).
% 0.23/0.44  fof(f12,plain,(
% 0.23/0.44    v1_relat_1(sK1)),
% 0.23/0.44    inference(cnf_transformation,[],[f11])).
% 0.23/0.44  fof(f11,plain,(
% 0.23/0.44    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.23/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f10])).
% 0.23/0.44  fof(f10,plain,(
% 0.23/0.44    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.23/0.44    introduced(choice_axiom,[])).
% 0.23/0.44  fof(f6,plain,(
% 0.23/0.44    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f5])).
% 0.23/0.44  fof(f5,negated_conjecture,(
% 0.23/0.44    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.23/0.44    inference(negated_conjecture,[],[f4])).
% 0.23/0.44  fof(f4,conjecture,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 0.23/0.44  fof(f16,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)) )),
% 0.23/0.44    inference(cnf_transformation,[],[f9])).
% 0.23/0.44  fof(f9,plain,(
% 0.23/0.44    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f2])).
% 0.23/0.44  fof(f2,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 0.23/0.44  fof(f24,plain,(
% 0.23/0.44    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.23/0.44    inference(superposition,[],[f13,f23])).
% 0.23/0.44  fof(f23,plain,(
% 0.23/0.44    ( ! [X0] : (k6_subset_1(k1_relat_1(sK1),X0) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.23/0.44    inference(forward_demodulation,[],[f22,f21])).
% 0.23/0.44  fof(f22,plain,(
% 0.23/0.44    ( ! [X0] : (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.23/0.44    inference(superposition,[],[f21,f19])).
% 0.23/0.44  fof(f19,plain,(
% 0.23/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) )),
% 0.23/0.44    inference(forward_demodulation,[],[f18,f17])).
% 0.23/0.44  fof(f17,plain,(
% 0.23/0.44    ( ! [X0] : (k3_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.23/0.44    inference(resolution,[],[f14,f12])).
% 0.23/0.44  fof(f14,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f7])).
% 0.23/0.44  fof(f7,plain,(
% 0.23/0.44    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f3])).
% 0.23/0.44  fof(f3,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.23/0.44  fof(f18,plain,(
% 0.23/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X0))) )),
% 0.23/0.44    inference(resolution,[],[f15,f12])).
% 0.23/0.44  fof(f15,plain,(
% 0.23/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) )),
% 0.23/0.44    inference(cnf_transformation,[],[f8])).
% 0.23/0.44  fof(f8,plain,(
% 0.23/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.44    inference(ennf_transformation,[],[f1])).
% 0.23/0.44  fof(f1,axiom,(
% 0.23/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.23/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.23/0.44  fof(f13,plain,(
% 0.23/0.44    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.23/0.44    inference(cnf_transformation,[],[f11])).
% 0.23/0.44  % SZS output end Proof for theBenchmark
% 0.23/0.44  % (16160)------------------------------
% 0.23/0.44  % (16160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.44  % (16160)Termination reason: Refutation
% 0.23/0.44  
% 0.23/0.44  % (16160)Memory used [KB]: 6012
% 0.23/0.44  % (16160)Time elapsed: 0.004 s
% 0.23/0.44  % (16160)------------------------------
% 0.23/0.44  % (16160)------------------------------
% 0.23/0.45  % (16155)Success in time 0.072 s
%------------------------------------------------------------------------------
