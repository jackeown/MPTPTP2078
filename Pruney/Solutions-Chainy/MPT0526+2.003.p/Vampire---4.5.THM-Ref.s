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
% DateTime   : Thu Dec  3 12:48:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f29])).

fof(f29,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f16,f28])).

fof(f28,plain,(
    sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f22,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(k2_relat_1(sK0),X0)
      | sK0 = k8_relat_1(X0,sK0) ) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | sK0 = k8_relat_1(X0,sK0) ) ),
    inference(resolution,[],[f20,f15])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != k8_relat_1(k2_relat_1(sK0),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k8_relat_1(k2_relat_1(X0),X0) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k8_relat_1(k2_relat_1(sK0),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f16,plain,(
    sK0 != k8_relat_1(k2_relat_1(sK0),sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (800784385)
% 0.13/0.36  ipcrm: permission denied for id (800817155)
% 0.13/0.37  ipcrm: permission denied for id (800849924)
% 0.13/0.38  ipcrm: permission denied for id (800882702)
% 0.13/0.38  ipcrm: permission denied for id (800915473)
% 0.20/0.39  ipcrm: permission denied for id (800948251)
% 0.20/0.40  ipcrm: permission denied for id (801013795)
% 0.20/0.43  ipcrm: permission denied for id (801079358)
% 0.20/0.46  ipcrm: permission denied for id (801177684)
% 0.36/0.57  % (13616)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.36/0.59  % (13624)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.36/0.60  % (13618)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.36/0.60  % (13618)Refutation found. Thanks to Tanya!
% 0.36/0.60  % SZS status Theorem for theBenchmark
% 0.36/0.60  % SZS output start Proof for theBenchmark
% 0.36/0.60  fof(f30,plain,(
% 0.36/0.60    $false),
% 0.36/0.60    inference(trivial_inequality_removal,[],[f29])).
% 0.36/0.60  fof(f29,plain,(
% 0.36/0.60    sK0 != sK0),
% 0.36/0.60    inference(superposition,[],[f16,f28])).
% 0.36/0.60  fof(f28,plain,(
% 0.36/0.60    sK0 = k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.36/0.60    inference(trivial_inequality_removal,[],[f27])).
% 0.36/0.60  fof(f27,plain,(
% 0.36/0.60    k1_xboole_0 != k1_xboole_0 | sK0 = k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.36/0.60    inference(superposition,[],[f25,f23])).
% 0.36/0.60  fof(f23,plain,(
% 0.36/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.36/0.60    inference(forward_demodulation,[],[f22,f18])).
% 0.36/0.60  fof(f18,plain,(
% 0.36/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.36/0.60    inference(cnf_transformation,[],[f3])).
% 0.36/0.60  fof(f3,axiom,(
% 0.36/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.36/0.60  fof(f22,plain,(
% 0.36/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.36/0.60    inference(definition_unfolding,[],[f17,f19])).
% 0.36/0.60  fof(f19,plain,(
% 0.36/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.36/0.60    inference(cnf_transformation,[],[f4])).
% 0.36/0.60  fof(f4,axiom,(
% 0.36/0.60    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.36/0.60  fof(f17,plain,(
% 0.36/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.36/0.60    inference(cnf_transformation,[],[f2])).
% 0.36/0.60  fof(f2,axiom,(
% 0.36/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.36/0.60  fof(f25,plain,(
% 0.36/0.60    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k2_relat_1(sK0),X0) | sK0 = k8_relat_1(X0,sK0)) )),
% 0.36/0.60    inference(resolution,[],[f24,f21])).
% 0.36/0.60  fof(f21,plain,(
% 0.36/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.36/0.60    inference(cnf_transformation,[],[f12])).
% 0.36/0.60  fof(f12,plain,(
% 0.36/0.60    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.36/0.60    inference(ennf_transformation,[],[f8])).
% 0.36/0.60  fof(f8,plain,(
% 0.36/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 0.36/0.60    inference(unused_predicate_definition_removal,[],[f1])).
% 0.36/0.60  fof(f1,axiom,(
% 0.36/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.36/0.60  fof(f24,plain,(
% 0.36/0.60    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | sK0 = k8_relat_1(X0,sK0)) )),
% 0.36/0.60    inference(resolution,[],[f20,f15])).
% 0.36/0.60  fof(f15,plain,(
% 0.36/0.60    v1_relat_1(sK0)),
% 0.36/0.60    inference(cnf_transformation,[],[f14])).
% 0.36/0.60  fof(f14,plain,(
% 0.36/0.60    sK0 != k8_relat_1(k2_relat_1(sK0),sK0) & v1_relat_1(sK0)),
% 0.36/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 0.36/0.60  fof(f13,plain,(
% 0.36/0.60    ? [X0] : (k8_relat_1(k2_relat_1(X0),X0) != X0 & v1_relat_1(X0)) => (sK0 != k8_relat_1(k2_relat_1(sK0),sK0) & v1_relat_1(sK0))),
% 0.36/0.60    introduced(choice_axiom,[])).
% 0.36/0.60  fof(f9,plain,(
% 0.36/0.60    ? [X0] : (k8_relat_1(k2_relat_1(X0),X0) != X0 & v1_relat_1(X0))),
% 0.36/0.60    inference(ennf_transformation,[],[f7])).
% 0.36/0.60  fof(f7,negated_conjecture,(
% 0.36/0.60    ~! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.36/0.60    inference(negated_conjecture,[],[f6])).
% 0.36/0.60  fof(f6,conjecture,(
% 0.36/0.60    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 0.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 0.36/0.60  fof(f20,plain,(
% 0.36/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 0.36/0.60    inference(cnf_transformation,[],[f11])).
% 0.36/0.60  fof(f11,plain,(
% 0.36/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.36/0.60    inference(flattening,[],[f10])).
% 0.36/0.60  fof(f10,plain,(
% 0.36/0.60    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.36/0.60    inference(ennf_transformation,[],[f5])).
% 0.36/0.60  fof(f5,axiom,(
% 0.36/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.36/0.60  fof(f16,plain,(
% 0.36/0.60    sK0 != k8_relat_1(k2_relat_1(sK0),sK0)),
% 0.36/0.60    inference(cnf_transformation,[],[f14])).
% 0.36/0.60  % SZS output end Proof for theBenchmark
% 0.36/0.60  % (13618)------------------------------
% 0.36/0.60  % (13618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.60  % (13618)Termination reason: Refutation
% 0.36/0.60  
% 0.36/0.60  % (13618)Memory used [KB]: 6012
% 0.36/0.60  % (13618)Time elapsed: 0.050 s
% 0.36/0.60  % (13618)------------------------------
% 0.36/0.60  % (13618)------------------------------
% 0.36/0.60  % (13481)Success in time 0.246 s
%------------------------------------------------------------------------------
