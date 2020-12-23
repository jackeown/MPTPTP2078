%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  64 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 125 expanded)
%              Number of equality atoms :   39 (  65 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f58,plain,(
    k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(superposition,[],[f57,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f57,plain,(
    k6_subset_1(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f46,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X0))) ),
    inference(backward_demodulation,[],[f50,f55])).

fof(f55,plain,(
    ! [X0] : k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(sK1,k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | k7_relat_1(sK1,k4_xboole_0(X0,X1)) = k4_xboole_0(sK1,k7_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f39,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) ) ),
    inference(forward_demodulation,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f33,f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f37,f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).

fof(f46,plain,(
    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(backward_demodulation,[],[f36,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    inference(resolution,[],[f28,f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f36,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f22,f24])).

fof(f22,plain,(
    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:30:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.51  % (19500)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (19493)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (19522)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (19522)Refutation not found, incomplete strategy% (19522)------------------------------
% 0.21/0.52  % (19522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (19522)Memory used [KB]: 1663
% 0.21/0.52  % (19522)Time elapsed: 0.001 s
% 0.21/0.52  % (19522)------------------------------
% 0.21/0.52  % (19522)------------------------------
% 0.21/0.52  % (19500)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    k4_xboole_0(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.52    inference(superposition,[],[f57,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k6_subset_1(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f46,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,X0)))) )),
% 0.21/0.52    inference(backward_demodulation,[],[f50,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)) = k4_xboole_0(sK1,k7_relat_1(sK1,X0))) )),
% 0.21/0.52    inference(resolution,[],[f51,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | k7_relat_1(sK1,k4_xboole_0(X0,X1)) = k4_xboole_0(sK1,k7_relat_1(sK1,X1))) )),
% 0.21/0.52    inference(resolution,[],[f39,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f38,f24])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f33,f24])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),X0)))) )),
% 0.21/0.52    inference(resolution,[],[f37,f21])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f29,f24])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_relat_1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.21/0.52    inference(backward_demodulation,[],[f36,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.21/0.52    inference(resolution,[],[f28,f21])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k4_xboole_0(sK1,k7_relat_1(sK1,sK0)))),
% 0.21/0.52    inference(forward_demodulation,[],[f22,f24])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (19500)------------------------------
% 0.21/0.52  % (19500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19500)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (19500)Memory used [KB]: 1791
% 0.21/0.52  % (19500)Time elapsed: 0.095 s
% 0.21/0.52  % (19500)------------------------------
% 0.21/0.52  % (19500)------------------------------
% 0.21/0.52  % (19506)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (19492)Success in time 0.149 s
%------------------------------------------------------------------------------
