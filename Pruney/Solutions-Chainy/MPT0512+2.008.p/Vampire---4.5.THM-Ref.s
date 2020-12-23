%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  43 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  62 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f41])).

fof(f41,plain,(
    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f39,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f36,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f27,f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X2] : k1_xboole_0 = k7_relat_1(sK0,k4_xboole_0(X2,X2)) ),
    inference(superposition,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1)) = k7_relat_1(sK0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k7_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) ) ),
    inference(forward_demodulation,[],[f34,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:16 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.42  % (21184)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.42  % (21184)Refutation not found, incomplete strategy% (21184)------------------------------
% 0.21/0.42  % (21184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (21184)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (21184)Memory used [KB]: 10618
% 0.21/0.42  % (21184)Time elapsed: 0.003 s
% 0.21/0.42  % (21184)------------------------------
% 0.21/0.42  % (21184)------------------------------
% 0.22/0.46  % (21190)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.46  % (21190)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f21,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.22/0.46    inference(forward_demodulation,[],[f39,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.46    inference(forward_demodulation,[],[f36,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.46    inference(superposition,[],[f27,f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.46    inference(rectify,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X2] : (k1_xboole_0 = k7_relat_1(sK0,k4_xboole_0(X2,X2))) )),
% 0.22/0.46    inference(superposition,[],[f38,f37])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(k7_relat_1(sK0,X0),k7_relat_1(sK0,X1)) = k7_relat_1(sK0,k4_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(resolution,[],[f35,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    v1_relat_1(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ? [X0] : (k1_xboole_0 != k7_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,negated_conjecture,(
% 0.22/0.46    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.46    inference(negated_conjecture,[],[f13])).
% 0.22/0.46  fof(f13,conjecture,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f34,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(forward_demodulation,[],[f29,f24])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    k1_xboole_0 != k7_relat_1(sK0,k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f19])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (21190)------------------------------
% 0.22/0.46  % (21190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (21190)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (21190)Memory used [KB]: 6140
% 0.22/0.46  % (21190)Time elapsed: 0.047 s
% 0.22/0.46  % (21190)------------------------------
% 0.22/0.46  % (21190)------------------------------
% 0.22/0.46  % (21172)Success in time 0.097 s
%------------------------------------------------------------------------------
